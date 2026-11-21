#include <assert.h>
#include <stdbool.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct object {
	unsigned long long offset;
	struct type *type;
	union {
		struct member *mem;
		unsigned long long idx;
	} u;
	/* index of the current array element */
	unsigned long long elem;
	/* for a struct with existential parameters, their arguments, determined by the initializers */
	struct genarg *exbind;
	/* for each existential parameter, the member whose initializer determined it */
	struct exsrc *exsrc;
	bool iscur;
};

struct exsrc {
	struct member *mem;
	/* type of the initializer of the member */
	struct type *type;
};

struct initparser {
	/* TODO: keep track of type depth, and allocate maximum possible
	   number of nested objects in initializer */
	struct object obj[32], *cur, *sub;
	struct init *init, **last;
	/*
	whether the type depends on mono parameters, so offsets are not
	known and entries record their subobject instead
	*/
	bool dep;
};

struct init *
mkinit(unsigned long long start, unsigned long long end, struct bitfield bits, struct expr *expr)
{
	struct init *init;

	init = xmalloc(sizeof(*init));
	init->start = start;
	init->end = end;
	init->expr = expr;
	init->bits = bits;
	init->next = NULL;
	init->path = NULL;
	init->npath = 0;

	return init;
}

/* number of elements in an array type whose element type depends on mono parameters */
static unsigned long long
arraycount(struct type *t)
{
	assert(t->u.array.length && t->u.array.length->kind == EXPRCONST);
	return t->u.array.length->u.constant.u;
}

/* insert `new` into the list starting at *init, replacing initializers it covers */
static struct init **
initinsert(struct init **init, struct init *new)
{
	struct init *old;

	for (; old = *init; init = &old->next) {
		if (old->end * 8 - old->bits.after <= new->start * 8 + new->bits.before)
			continue;
		/* no overlap, insert before `old` */
		if (new->end * 8 - new->bits.after <= old->start * 8 + old->bits.before)
			break;
		/* replace any initializers that `new` covers */
		if (old->end * 8 - old->bits.after <= new->end * 8 - new->bits.after) {
			do old = old->next;
			while (old && old->end * 8 - old->bits.after <= new->end * 8 - new->bits.after);
			break;
		}
		/* `old` covers `new`, keep looking */
	}
	new->next = old;
	*init = new;
	return &new->next;
}

static void
initadd(struct initparser *p, struct init *new)
{
	struct init **end;

	if (p->dep) {
		/* the order is determined when offsets are known */
		for (end = &p->init; *end; end = &(*end)->next)
			;
		*end = new;
		return;
	}
	p->last = initinsert(p->last, new);
}

/* record the subobject an initializer entry applies to */
static void
initpath(struct initparser *p, struct init *init)
{
	struct object *o;
	struct member *m;
	struct initstep *step;
	unsigned long long n;

	init->npath = p->sub - p->obj;
	init->path = xreallocarray(NULL, init->npath, sizeof(*init->path));
	for (o = p->obj, step = init->path; o < p->sub; ++o, ++step) {
		if (o->type->kind == TYPEARRAY) {
			step->isindex = true;
			step->n = o->elem;
		} else {
			n = 0;
			for (m = o->type->u.structunion.members; m != o->u.mem; m = m->next)
				++n;
			step->isindex = false;
			step->n = n;
		}
	}
}

/*
Compute the offsets of the entries of an initializer for an object of
the concrete type t, which was parsed for a type depending on mono
parameters.
*/
struct init *
initresolve(struct init *init, struct type *t)
{
	struct init *head, *next;
	struct type *st;
	struct member *m;
	unsigned long long off, n;
	size_t i;

	head = NULL;
	for (; init; init = next) {
		next = init->next;
		if (!init->path && init->npath == 0 && init->end == 0) {
			/* the single initializer of the whole object */
			init->start = 0;
			init->end = t->size;
			init->bits = (struct bitfield){0};
			init->next = NULL;
			initinsert(&head, init);
			continue;
		}
		st = t;
		off = 0;
		init->bits = (struct bitfield){0};
		for (i = 0; i < init->npath; ++i) {
			if (init->path[i].isindex) {
				off += init->path[i].n * st->base->size;
				st = st->base;
			} else {
				m = st->u.structunion.members;
				for (n = init->path[i].n; n > 0; --n)
					m = m->next;
				off += m->offset;
				st = m->type;
				init->bits = m->bits;
			}
		}
		init->start = off;
		init->end = off + st->size;
		init->next = NULL;
		initinsert(&head, init);
	}
	return head;
}

static struct genarg *exbind(struct type *);

static void
subobj(struct initparser *p, struct type *t, unsigned long long off)
{
	/* the subobject could be incomplete if it's a flexible array member */
	if (t->incomplete)
		error(&tok.loc, "initializer specified for incomplete type");
	off += p->sub->offset;
	if (++p->sub == p->obj + countof(p->obj))
		fatal("internal error: too many designators");
	p->sub->type = t;
	p->sub->offset = off;
	p->sub->iscur = false;
	p->sub->exbind = exbind(t);
	p->sub->exsrc = NULL;
}

/* arguments to be determined for the existential parameters of t, if any */
static struct genarg *
exbind(struct type *t)
{
	struct genarg *args;
	struct generic *ex;

	if (t->kind != TYPESTRUCT && t->kind != TYPEUNION || !t->u.structunion.exists)
		return NULL;
	ex = t->u.structunion.exists;
	args = xreallocarray(NULL, ex->nparam, sizeof(*args));
	memset(args, 0, ex->nparam * sizeof(*args));
	return args;
}

/*
The type of an initializer for a member that mentions existential
parameters of its struct, which binds them. All initializers of the
struct must agree.
*/
static bool
exbound(struct genarg *a)
{
	return a->type || a->size || a->constset;
}

/*
Report an initializer of type `at` for the member of o with type t,
which contradicts the arguments in `bind` determined by the earlier
initializers.
*/
static void
exconflict(struct object *o, struct genarg *bind, struct type *t, struct type *at)
{
	struct generic *ex;
	struct genarg *one;
	struct exsrc *src;
	const char *kind, *name, *mem;
	size_t i;

	ex = o->type->u.structunion.exists;
	kind = o->type->kind == TYPESTRUCT ? "struct" : "union";
	name = ex->name ? ex->name : "<anonymous>";
	mem = o->u.mem->name ? o->u.mem->name : "<anonymous>";
	/* find an argument which the initializer contradicts by itself */
	one = xreallocarray(NULL, ex->nparam, sizeof(*one));
	for (i = 0; i < ex->nparam; ++i) {
		src = &o->exsrc[i];
		if (!src->mem || !exbound(&bind[i]))
			continue;
		memset(one, 0, ex->nparam * sizeof(*one));
		one[i] = bind[i];
		if (genunify(ex, one, t, QUALNONE, at, QUALNONE))
			continue;
		if (bind[i].type) {
			error(&tok.loc, "member '%s' of type '%s' is initialized with a value of type '%s', but member '%s', initialized with a value of type '%s', determined existential parameter '%s' of %s '%s' to be '%s'",
				mem, typespelling(t, QUALNONE), typespelling(at, QUALNONE),
				src->mem->name ? src->mem->name : "<anonymous>", typespelling(src->type, QUALNONE),
				ex->params[i].name, kind, name, typespelling(bind[i].type, bind[i].qual));
		}
		error(&tok.loc, "member '%s' of type '%s' is initialized with a value of type '%s', which is inconsistent with existential parameter '%s' of %s '%s' as determined by member '%s', initialized with a value of type '%s'",
			mem, typespelling(t, QUALNONE), typespelling(at, QUALNONE),
			ex->params[i].name, kind, name,
			src->mem->name ? src->mem->name : "<anonymous>", typespelling(src->type, QUALNONE));
	}
	error(&tok.loc, "member '%s' of type '%s' is initialized with a value of type '%s', which is inconsistent with the existential parameters of %s '%s'",
		mem, typespelling(t, QUALNONE), typespelling(at, QUALNONE), kind, name);
}

/*
The type of an initializer for a member that mentions existential
parameters of its struct, which binds them. All initializers of the
struct must agree.
*/
static struct type *
exmember(struct initparser *p, struct type *t, struct expr *e)
{
	struct object *o;
	struct generic *ex;
	struct genarg *old;
	enum typequal q;
	size_t i;

	if (p->sub == p->obj)
		return t;
	o = p->sub - 1;
	if (!o->exbind)
		return t;
	ex = o->type->u.structunion.exists;
	if (!typehasparam(t, ex))
		return t;
	if (!o->exsrc) {
		o->exsrc = xreallocarray(NULL, ex->nparam, sizeof(*o->exsrc));
		memset(o->exsrc, 0, ex->nparam * sizeof(*o->exsrc));
	}
	/* a failed unification may leave partial bindings behind */
	old = xreallocarray(NULL, ex->nparam, sizeof(*old));
	memcpy(old, o->exbind, ex->nparam * sizeof(*old));
	if (!genunify(ex, o->exbind, t, QUALNONE, e->type, QUALNONE))
		exconflict(o, old, t, e->type);
	for (i = 0; i < ex->nparam; ++i) {
		if (!exbound(&old[i]) && exbound(&o->exbind[i])) {
			o->exsrc[i].mem = o->u.mem;
			o->exsrc[i].type = e->type;
		}
	}
	free(old);
	q = QUALNONE;
	return typesubst(t, &q, ex, o->exbind);
}

static bool
findmember(struct initparser *p, const char *name)
{
	struct member *m;

	for (m = p->sub->type->u.structunion.members; m; m = m->next) {
		if (m->name) {
			if (strcmp(m->name, name) == 0) {
				p->sub->u.mem = m;
				subobj(p, m->type, m->offset);
				return true;
			}
		} else {
			subobj(p, m->type, m->offset);
			if (findmember(p, name))
				return true;
			--p->sub;
		}
	}
	return false;
}

static void
designator(struct scope *s, struct initparser *p)
{
	struct type *t;
	char *name;

	p->last = &p->init;
	p->sub = p->cur;
	for (;;) {
		t = p->sub->type;
		switch (tok.kind) {
		case TLBRACK:
			if (t->kind != TYPEARRAY)
				error(&tok.loc, "index designator is only valid for array types");
			next();
			p->sub->elem = intconstexpr(s, false);
			if (p->dep && typedep(t->base)) {
				if (p->sub->elem >= arraycount(t))
					error(&tok.loc, "index designator is larger than array length");
				p->sub->u.idx = 0;
			} else {
				p->sub->u.idx = p->sub->elem * t->base->size;
				if (p->sub->u.idx >= t->size) {
					if (!t->incomplete)
						error(&tok.loc, "index designator is larger than array length");
					t->size = p->sub->u.idx + t->base->size;
				}
			}
			expect(TRBRACK, "for index designator");
			subobj(p, t->base, p->sub->u.idx);
			break;
		case TPERIOD:
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "member designator only valid for struct/union types");
			next();
			name = expect(TIDENT, "for member designator");
			if (!findmember(p, name))
				error(&tok.loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", name);
			break;
		default:
			expect(TASSIGN, "after designator");
			return;
		}
	}
}

static void
focus(struct initparser *p)
{
	struct type *t;

	switch (p->sub->type->kind) {
	case TYPEARRAY:
		t = p->sub->type->base;
		p->sub->u.idx = 0;
		p->sub->elem = 0;
		if (p->sub->type->incomplete)
			p->sub->type->size = t->size;
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		p->sub->u.mem = p->sub->type->u.structunion.members;
		t = p->sub->u.mem->type;
		break;
	default:
		fatal("internal error: init cursor has unexpected type");
	}
	subobj(p, t, 0);
}

static void
advance(struct initparser *p)
{
	struct type *t;

	for (;;) {
		--p->sub;
		t = p->sub->type;
		switch (t->kind) {
		case TYPEARRAY:
			++p->sub->elem;
			if (p->dep && typedep(t->base)) {
				if (p->sub->elem < arraycount(t)) {
					subobj(p, t->base, 0);
					return;
				}
				break;
			}
			p->sub->u.idx += t->base->size;
			if (p->sub->u.idx == t->size) {
				if (!t->incomplete)
					break;
				t->size += t->base->size;
			}
			subobj(p, t->base, p->sub->u.idx);
			return;
		case TYPESTRUCT:
			p->sub->u.mem = p->sub->u.mem->next;
			if (p->sub->u.mem) {
				subobj(p, p->sub->u.mem->type, p->sub->u.mem->offset);
				return;
			}
			break;
		}
		if (p->sub == p->cur)
			error(&tok.loc, "too many initializers for type");
	}
}

/* 6.7.9 Initialization */
struct init *
parseinit(struct scope *s, struct type *t)
{
	struct initparser p;
	struct expr *expr;
	struct type *base;
	struct bitfield bits;
	struct init *new;
	struct location loc;

	p.cur = NULL;
	p.sub = p.obj;
	p.sub->offset = 0;
	p.sub->type = t;
	p.sub->iscur = false;
	p.sub->exbind = exbind(t);
	p.sub->exsrc = NULL;
	p.init = NULL;
	p.last = &p.init;
	p.dep = typedep(t);
	if (p.dep && t->kind == TYPEARRAY && t->incomplete)
		error(&tok.loc, "array of unknown size with element type depending on mono parameters cannot be initialized");
	if (t->incomplete && t->kind != TYPEARRAY)
		error(&tok.loc, "initializer specified for incomplete type");
	if (t->kind == TYPEARRAY && t->base->size == 0 && !typedep(t->base))
		error(&tok.loc, "initializer specified for variable length array type");
	for (;;) {
		if (p.cur) {
			if (tok.kind == TLBRACK || tok.kind == TPERIOD)
				designator(s, &p);
			else if (p.sub != p.cur)
				advance(&p);
			else if (p.cur->type->kind == TYPESTRUCT || p.cur->type->kind == TYPEUNION)
				focus(&p);
		}
		if (consume(TLBRACE)) {
			if (p.sub->type->kind == TYPEPARAM && tok.kind != TRBRACE)
				error(&tok.loc, "braces around initializer for type parameter '%s'", p.sub->type->u.param.name);
			if (consume(TRBRACE)){
				if (p.sub->type->incomplete)
					error(&tok.loc, "array of unknown size has empty initializer");
				goto next;
			}
			if (p.cur == p.sub) {
				if (p.cur->type->prop & PROPSCALAR)
					error(&tok.loc, "nested braces around scalar initializer");
				assert(p.cur->type->kind == TYPEARRAY);
				focus(&p);
			}
			p.cur = p.sub;
			p.cur->iscur = true;
			continue;
		}
		/* the type of the whole initializer is used to infer type arguments */
		if (!p.cur)
			exprexpect(t);
		loc = tok.loc;
		expr = assignexpr(s);
		for (;;) {
			t = p.sub->type;
			switch (t->kind) {
			case TYPEARRAY:
				/* a C5 array can be initialized with another */
				if (t->u.array.byvalue && exprunarray(expr) && expr->base->kind != EXPRSTRING && typecompatible(expr->base->type, t)) {
					expr = expr->base;
					goto add;
				}
				if (!expr->decayed || expr->base->kind != EXPRSTRING || !(t->base->prop & PROPINT))
					break;
				base = t->base;
				expr = expr->base;
				if (!(base->prop & PROPCHAR && expr->type->base->prop & PROPCHAR) && !typecompatible(base, expr->type->base))
					error(&tok.loc, "cannot initialize array with string literal of different width");
				if (t->u.array.byvalue && expr->type->size > t->size)
					error(&tok.loc, "string literal is too long for array");
				if (t->incomplete)
					t->size = expr->type->size;
				goto add;
			case TYPESTRUCT:
			case TYPEUNION:
				/* a const variant of t initializes it as a whole, if it converts */
				if (typeisslice(t) && typeisslice(expr->type) || !typecompatible(expr->type, t) && typeconstvariant(expr->type, t))
					expr = exprassign(expr, t);
				if (typecompatible(expr->type, t)) {
					if (typeisslice(t) && expr->kind == EXPRCOMPOUND && !p.dep) {
						/* initialize the pointer and length directly, so that a slice of a static array is a constant */
						for (new = expr->u.compound.init; new; new = new->next)
							initadd(&p, mkinit(p.sub->offset + new->start, p.sub->offset + new->end, new->bits, new->expr));
						goto next;
					}
					goto add;
				}
				break;
			case TYPEPARAM:
				/* the structure of a type parameter is unknown, so it is initialized as a whole */
				expr = eval(expr);
				if (expr->kind == EXPRCONST && expr->type->prop & PROPINT && expr->u.constant.u == 0)
					goto next;  /* zero */
				expr = exprassign(expr, t);
				goto add;
			default:  /* scalar type */
				assert(t->prop & PROPSCALAR);
				expr = exprassign(expr, exmember(&p, t, expr));
				goto add;
			}
			/*
			Only within braces may an initializer be for the
			first subobject of an aggregate or union.
			*/
			if (!p.cur)
				error(&loc, "initializer for %s must be brace-enclosed or have compatible type", typeisslice(t) ? "slice" : t->kind == TYPEARRAY ? "array" : "struct or union");
			focus(&p);
		}
	add:
		if (p.sub > p.obj && (p.sub[-1].type->kind == TYPESTRUCT || p.sub[-1].type->kind == TYPEUNION))
			bits = p.sub[-1].u.mem->bits;
		else
			bits = (struct bitfield){0};
		new = mkinit(p.sub->offset, p.sub->offset + p.sub->type->size, bits, expr);
		if (p.dep)
			initpath(&p, new);
		initadd(&p, new);
		for (;;) {
			if (p.sub->type->incomplete)
				p.sub->type->incomplete = false;
		next:
			if (!p.cur)
				return p.init;
			if (tok.kind == TCOMMA) {
				next();
				if (tok.kind != TRBRACE)
					break;
			} else if (tok.kind != TRBRACE) {
				error(&tok.loc, "expected ',' or '}' after initializer");
			}
			next();
			p.sub = p.cur;
			do p.cur = p.cur == p.obj ? NULL : p.cur - 1;
			while (p.cur && !p.cur->iscur);
		}
	}
}
