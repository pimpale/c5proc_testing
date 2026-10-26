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
	bool iscur;
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

	p.cur = NULL;
	p.sub = p.obj;
	p.sub->offset = 0;
	p.sub->type = t;
	p.sub->iscur = false;
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
		expr = assignexpr(s);
		for (;;) {
			t = p.sub->type;
			switch (t->kind) {
			case TYPEARRAY:
				if (!expr->decayed || expr->base->kind != EXPRSTRING || !(t->base->prop & PROPINT))
					break;
				base = t->base;
				expr = expr->base;
				if (!(base->prop & PROPCHAR && expr->type->base->prop & PROPCHAR) && !typecompatible(base, expr->type->base))
					error(&tok.loc, "cannot initialize array with string literal of different width");
				if (t->incomplete)
					t->size = expr->type->size;
				goto add;
			case TYPESTRUCT:
			case TYPEUNION:
				if (typecompatible(expr->type, t))
					goto add;
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
				expr = exprassign(expr, t);
				goto add;
			}
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
