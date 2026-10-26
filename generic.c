#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct geninst {
	struct genarg *args;
	struct type *type;
	enum typequal qual;
	struct geninst *next;
};

struct generic *
mkgeneric(bool ismono)
{
	struct generic *g;

	g = xmalloc(sizeof(*g));
	memset(g, 0, sizeof(*g));
	g->ismono = ismono;
	return g;
}

struct type *
mkparamtype(struct generic *g, size_t index, char *name)
{
	struct type *t;

	t = mktype(TYPEPARAM, 0);
	/*
	The size of an erased type parameter is never known. A mono type
	parameter is complete, but its layout is not known until it is
	instantiated.
	*/
	t->incomplete = !g->ismono;
	t->u.param.gen = g;
	t->u.param.index = index;
	t->u.param.name = name;
	return t;
}

/* qualifier bits of the constness parameters of g */
static enum typequal
constbits(struct generic *g)
{
	enum typequal bits = QUALNONE;
	size_t i;

	if (!g)
		return QUALCPARAMS;
	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENCONSTNESS)
			bits |= g->params[i].bit;
	}
	return bits;
}

/* substitute the constness arguments of g for its constness parameters in q */
enum typequal
qualsubst(enum typequal q, struct generic *g, struct genarg *args)
{
	enum typequal r;
	size_t i;

	if (!(q & constbits(g)))
		return q;
	r = q & ~constbits(g);
	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENCONSTNESS && q & g->params[i].bit)
			r |= args[i].qual;
	}
	return r;
}

/*
Whether qualifiers q1 are a subset of q2. A constness parameter may be
const, so const in q2 includes it.
*/
bool
qualsubset(enum typequal q1, enum typequal q2)
{
	if (q2 & QUALCONST)
		q2 |= QUALCPARAMS;
	return (q1 & q2) == q1;
}

/* whether t refers to a parameter of g, or of any generic if g is NULL */
bool
typehasparam(struct type *t, struct generic *g)
{
	struct generic *tg;
	struct decl *p;
	size_t i;

	switch (t->kind) {
	case TYPEPARAM:
		return !g || t->u.param.gen == g;
	case TYPEARRAY:
		/* the length may depend on parameters */
		if (t->prop & PROPDEPLEN)
			return true;
		/* fallthrough */
	case TYPEPOINTER:
		return t->qual & constbits(g) || typehasparam(t->base, g);
	case TYPEFUNC:
		if (t->qual & constbits(g) || typehasparam(t->base, g))
			return true;
		for (p = t->u.func.params; p; p = p->next) {
			if (p->qual & constbits(g) || typehasparam(p->type, g))
				return true;
		}
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		if (!tg)
			break;
		for (i = 0; i < tg->nparam; ++i) {
			if (tg->params[i].kind == GENCONSTNESS ? t->u.structunion.genargs[i].qual & constbits(g) : t->u.structunion.genargs[i].type ? typehasparam(t->u.structunion.genargs[i].type, g) : exprhasparam(t->u.structunion.genargs[i].size, g))
				return true;
		}
		break;
	}
	return false;
}

/* whether t refers to a parameter of a mono (or erased) declaration */
bool
typehasparamkind(struct type *t, bool mono)
{
	struct generic *tg;
	struct decl *p;

	switch (t->kind) {
	case TYPEPARAM:
		return t->u.param.gen->ismono == mono;
	case TYPEARRAY:
		if (t->prop & PROPDEPLEN && exprhasparamkind(t->u.array.length, mono))
			return true;
		/* fallthrough */
	case TYPEPOINTER:
		return typehasparamkind(t->base, mono);
	case TYPEFUNC:
		if (typehasparamkind(t->base, mono))
			return true;
		for (p = t->u.func.params; p; p = p->next) {
			if (typehasparamkind(p->type, mono))
				return true;
		}
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		if (tg && argshaveparam(tg, t->u.structunion.genargs, mono))
			return true;
		break;
	}
	return false;
}

bool
argshaveparam(struct generic *g, struct genarg *args, bool mono)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		/* constness is always erased */
		if (g->params[i].kind == GENCONSTNESS)
			continue;
		if (args[i].type ? typehasparamkind(args[i].type, mono) : exprhasparamkind(args[i].size, mono))
			return true;
	}
	return false;
}

/* whether the layout of t depends on mono parameters, so is not yet known */
bool
typedep(struct type *t)
{
	struct generic *tg;

	switch (t->kind) {
	case TYPEPARAM:
		return t->u.param.gen->ismono;
	case TYPEARRAY:
		return t->prop & PROPDEPLEN && !t->incomplete || typedep(t->base);
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		return tg && tg->ismono && !t->incomplete && argshaveparam(tg, t->u.structunion.genargs, true);
	}
	return false;
}

/*
Substitute the arguments `args` for the parameters of g in t.
Qualifiers of a substituted parameter are added to *tq.
*/
struct type *
typesubst(struct type *t, enum typequal *tq, struct generic *g, struct genarg *args)
{
	struct type *n;
	struct generic *tg;
	struct genarg *newargs;
	struct decl *p, *np, **end;
	struct expr *len;
	enum typequal q;
	size_t i;

	if (!typehasparam(t, g) && !(t->prop & PROPDEPLEN))
		return t;
	switch (t->kind) {
	case TYPEPARAM:
		*tq |= args[t->u.param.index].qual;
		return args[t->u.param.index].type;
	case TYPEPOINTER:
		/* qualifiers from the substituted parameter are added after the constness substitution */
		q = qualsubst(t->qual, g, args);
		n = typesubst(t->base, &q, g, args);
		return mkpointertype(n, q);
	case TYPEARRAY:
		q = qualsubst(t->qual, g, args);
		n = typesubst(t->base, &q, g, args);
		if (t->prop & PROPDEPLEN) {
			len = constsubst(t->u.array.length, g, args);
			if (len->kind != EXPRCONST) {
				/* still depends on other parameters */
				n = mkarraytype(n, q, 0);
				n->incomplete = exprhasparamkind(len, false);
				n->prop |= PROPDEPLEN;
				n->u.array.length = len;
				return n;
			}
			if (len->type->u.arith.issigned && len->u.constant.u >> 63)
				error(&tok.loc, "array length must be non-negative");
			return mkarraytype(n, q, len->u.constant.u);
		}
		if (t->u.array.length && t->u.array.length->kind == EXPRCONST)
			n = mkarraytype(n, q, t->u.array.length->u.constant.u);
		else if (t->incomplete || !t->base->size)
			n = mkarraytype(n, q, 0);
		else
			n = mkarraytype(n, q, t->size / t->base->size);
		if (typedep(n))
			n->u.array.length = t->u.array.length;
		return n;
	case TYPEFUNC:
		n = mktype(TYPEFUNC, t->prop);
		*n = *t;
		n->value = NULL;
		q = qualsubst(t->qual, g, args);
		n->base = typesubst(t->base, &q, g, args);
		n->qual = q;
		end = &n->u.func.params;
		for (p = t->u.func.params; p; p = p->next) {
			np = xmalloc(sizeof(*np));
			*np = *p;
			q = qualsubst(p->qual, g, args);
			np->type = typesubst(p->type, &q, g, args);
			np->qual = q;
			/* the alignment of a parameter of dependent type is only now known */
			if (np->kind == DECLOBJECT && np->u.obj.align < np->type->align)
				np->u.obj.align = np->type->align;
			*end = np;
			end = &np->next;
		}
		*end = NULL;
		return n;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		newargs = xreallocarray(NULL, tg->nparam, sizeof(*newargs));
		for (i = 0; i < tg->nparam; ++i) {
			newargs[i].size = NULL;
			newargs[i].type = NULL;
			newargs[i].constset = t->u.structunion.genargs[i].constset;
			q = qualsubst(t->u.structunion.genargs[i].qual, g, args);
			if (tg->params[i].kind == GENCONSTNESS) {
				/* only the qualifier */
			} else if (t->u.structunion.genargs[i].type) {
				newargs[i].type = typesubst(t->u.structunion.genargs[i].type, &q, g, args);
			} else {
				newargs[i].size = t->u.structunion.genargs[i].size;
				if (exprhasparam(newargs[i].size, g))
					newargs[i].size = constsubst(newargs[i].size, g, args);
			}
			newargs[i].qual = q;
		}
		return geninst(tg, newargs, tq);
	}
	fatal("internal error: unexpected type in substitution");
	return NULL;
}

/* whether two size arguments are the same; dependent ones are compared structurally */
bool
sizesame(struct expr *e1, struct expr *e2)
{
	if (e1 == e2)
		return true;
	if (e1->kind != e2->kind)
		return false;
	switch (e1->kind) {
	case EXPRCONST:
		return e1->u.constant.u == e2->u.constant.u;
	case EXPRSIZEPARAM:
		return e1->u.sizeparam.gen == e2->u.sizeparam.gen && e1->u.sizeparam.index == e2->u.sizeparam.index;
	case EXPRBINARY:
		return e1->op == e2->op && sizesame(e1->u.binary.l, e2->u.binary.l) && sizesame(e1->u.binary.r, e2->u.binary.r);
	case EXPRCAST:
		return e1->type == e2->type && sizesame(e1->base, e2->base);
	case EXPRLAYOUT:
		return e1->u.layout.kind == e2->u.layout.kind && typesame(e1->u.layout.type, e2->u.layout.type);
	}
	return false;
}

bool
argssame(struct generic *g, struct genarg *a1, struct genarg *a2)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENSIZE) {
			if (!sizesame(a1[i].size, a2[i].size))
				return false;
		} else if (g->params[i].kind == GENCONSTNESS) {
			if (a1[i].qual != a2[i].qual)
				return false;
		} else if (a1[i].qual != a2[i].qual || !typesame(a1[i].type, a2[i].type)) {
			return false;
		}
	}
	return true;
}

/* expression for the value of size parameter i of g */
struct expr *
mksizeparamexpr(struct generic *g, size_t i)
{
	struct expr *e;

	e = xmalloc(sizeof(*e));
	memset(e, 0, sizeof(*e));
	e->kind = EXPRSIZEPARAM;
	e->type = &typeulong;
	e->u.sizeparam.gen = g;
	e->u.sizeparam.index = i;
	return e;
}

/*
Instantiate the pattern of g with the arguments `args`. The same
arguments always produce the same type.
*/
struct type *
geninst(struct generic *g, struct genarg *args, enum typequal *tq)
{
	struct geninst *inst;
	struct type *t, *p;
	struct member *m, *nm, **end;
	enum typequal q;
	size_t i;

	p = g->pattern;
	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENSIZE) {
			if (args[i].size->kind != EXPRSIZEPARAM || args[i].size->u.sizeparam.gen != g || args[i].size->u.sizeparam.index != i)
				break;
		} else if (g->params[i].kind == GENCONSTNESS) {
			if (args[i].qual != g->params[i].bit)
				break;
		} else if (args[i].type != g->params[i].type || args[i].qual) {
			break;
		}
	}
	if (i == g->nparam)
		return p;
	for (inst = g->insts; inst; inst = inst->next) {
		if (argssame(g, inst->args, args)) {
			*tq |= inst->qual;
			return inst->type;
		}
	}
	inst = xmalloc(sizeof(*inst));
	inst->args = args;
	inst->qual = QUALNONE;
	inst->next = g->insts;
	g->insts = inst;
	if ((p->kind != TYPESTRUCT && p->kind != TYPEUNION) || p->u.structunion.gen != g) {
		/* generic typedef */
		inst->type = typesubst(p, &inst->qual, g, args);
		*tq |= inst->qual;
		return inst->type;
	}
	if (p->incomplete)
		error(&tok.loc, "generic %s '%s' used before its definition is complete", p->kind == TYPESTRUCT ? "struct" : "union", p->u.structunion.tag);
	/*
	The instance is cached before its members are substituted, so
	that members referring to the instance itself find it.
	*/
	t = mktype(p->kind, p->prop);
	*t = *p;
	t->value = NULL;
	t->u.structunion.genargs = args;
	inst->type = t;
	end = &t->u.structunion.members;
	for (m = p->u.structunion.members; m; m = m->next) {
		nm = xmalloc(sizeof(*nm));
		*nm = *m;
		q = qualsubst(m->qual, g, args);
		nm->type = typesubst(m->type, &q, g, args);
		nm->qual = q;
		*end = nm;
		end = &nm->next;
	}
	*end = NULL;
	if (g->ismono) {
		if (argshaveparam(g, args, false)) {
			/* the layout depends on an erased parameter, so can never be known */
			t->incomplete = true;
		} else if (argshaveparam(g, args, true)) {
			t->size = 0;
			t->align = 0;
		} else {
			structlayout(t, p);
		}
	}
	return t;
}


static struct expr *
mkconstsize(unsigned long long n)
{
	struct expr *e;

	e = xmalloc(sizeof(*e));
	memset(e, 0, sizeof(*e));
	e->kind = EXPRCONST;
	e->type = &typeulong;
	e->u.constant.u = n;
	return e;
}

/* unify a size in a parameter type with a size in an argument type */
static bool
unifysize(struct generic *g, struct genarg *bind, struct expr *p, struct expr *a)
{
	struct genarg *b;

	if (p->kind != EXPRSIZEPARAM || p->u.sizeparam.gen != g)
		return !exprhasparam(p, g) || sizesame(p, a);
	b = &bind[p->u.sizeparam.index];
	if (!b->size) {
		b->size = a;
		return true;
	}
	return sizesame(b->size, a);
}

/* unify a constness argument in a parameter type with one in an argument type */
static bool
unifyconst(struct generic *g, struct genarg *bind, enum typequal p, enum typequal a)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind != GENCONSTNESS || !(p & g->params[i].bit))
			continue;
		if (!bind[i].constset) {
			bind[i].qual = a;
			bind[i].constset = true;
			return true;
		}
		return bind[i].qual == a;
	}
	return p == a;
}

/*
Unify the parameter type p with the argument type a, binding the
parameters of g in `bind`. Parts of p that do not refer to parameters
of g are not checked here; the argument is converted to the
substituted parameter type afterwards. The only conversion allowed is
adding qualifiers to pointed-to types.
*/
bool
genunify(struct generic *g, struct genarg *bind, struct type *p, enum typequal pq, struct type *a, enum typequal aq)
{
	struct decl *pp, *ap;
	struct genarg *b, *pargs, *aargs;
	enum typequal bq;
	size_t i;

	if (!typehasparam(p, g))
		return true;
	switch (p->kind) {
	case TYPEPARAM:
		b = &bind[p->u.param.index];
		/* qualifiers of the argument not required by the parameter are part of the binding */
		aq &= ~pq;
		if (!b->type) {
			b->type = a;
			b->qual = aq;
			return true;
		}
		return typesame(b->type, a) && (aq & ~b->qual) == 0;
	case TYPEPOINTER:
		if (a->kind != TYPEPOINTER)
			return false;
		bq = p->qual;
		for (i = 0; i < g->nparam; ++i) {
			if (g->params[i].kind != GENCONSTNESS || !(p->qual & g->params[i].bit))
				continue;
			b = &bind[i];
			/* the constness of the argument binds the parameter */
			if (!b->constset) {
				b->qual = a->qual & QUALCONSTANT;
				b->constset = true;
			} else if (!qualsubset(a->qual & QUALCONSTANT, b->qual)) {
				return false;
			}
			bq = bq & ~g->params[i].bit | b->qual;
		}
		if (!qualsubset(a->qual, bq) && p->base->kind != TYPEPARAM)
			return false;
		return genunify(g, bind, p->base, bq, a->base, a->qual);
	case TYPEARRAY:
		if (a->kind != TYPEARRAY)
			return false;
		if (p->prop & PROPDEPLEN && p->u.array.length->kind == EXPRSIZEPARAM && p->u.array.length->u.sizeparam.gen == g) {
			if (a->incomplete || a->prop & (PROPVM | PROPDEPLEN) || !a->base->size)
				return false;
			if (!unifysize(g, bind, p->u.array.length, mkconstsize(a->size / a->base->size)))
				return false;
		}
		return genunify(g, bind, p->base, p->qual, a->base, a->qual);
	case TYPEFUNC:
		if (a->kind != TYPEFUNC || a->u.func.isvararg != p->u.func.isvararg)
			return false;
		if (!genunify(g, bind, p->base, p->qual, a->base, a->qual))
			return false;
		for (pp = p->u.func.params, ap = a->u.func.params; pp && ap; pp = pp->next, ap = ap->next) {
			if (!genunify(g, bind, pp->type, pp->qual, ap->type, ap->qual))
				return false;
		}
		return !pp && !ap;
	case TYPESTRUCT:
	case TYPEUNION:
		if (a->kind != p->kind || a->u.structunion.gen != p->u.structunion.gen)
			return false;
		pargs = p->u.structunion.genargs;
		aargs = a->u.structunion.genargs;
		for (i = 0; i < p->u.structunion.gen->nparam; ++i) {
			if (p->u.structunion.gen->params[i].kind == GENCONSTNESS) {
				if (!unifyconst(g, bind, pargs[i].qual, aargs[i].qual))
					return false;
			} else if (!pargs[i].type) {
				if (!unifysize(g, bind, pargs[i].size, aargs[i].size))
					return false;
			} else if (!genunify(g, bind, pargs[i].type, pargs[i].qual, aargs[i].type, aargs[i].qual)) {
				return false;
			}
		}
		return true;
	}
	return false;
}

/* arguments for g that are its own parameters */
struct genarg *
genidentity(struct generic *g)
{
	struct genarg *args;
	size_t i;

	args = xreallocarray(NULL, g->nparam, sizeof(*args));
	for (i = 0; i < g->nparam; ++i) {
		args[i].type = g->params[i].type;
		args[i].qual = QUALNONE;
		args[i].size = g->params[i].kind == GENSIZE ? mksizeparamexpr(g, i) : NULL;
		args[i].constset = g->params[i].kind == GENCONSTNESS;
		if (args[i].constset)
			args[i].qual = g->params[i].bit;
	}
	return args;
}

/* close a generic argument or parameter list; the first '>' of '>>' closes it */
void
closeangle(void)
{
	if (tok.kind == TSHR)
		tok.kind = TGREATER;
	else
		expect(TGREATER, "to close type argument list");
}

/* parse a constness parameter as the argument for another constness parameter */
static bool
constarg(struct scope *s, enum typequal *q)
{
	struct decl *d;

	if (tok.kind < TIDENT)
		return false;
	d = scopegetdecl(s, tokenstr(tok.kind), true);
	if (!d || d->kind != DECLCONST || !d->gen || d->gen->params[d->u.enumconst].kind != GENCONSTNESS)
		return false;
	*q = d->gen->params[d->u.enumconst].bit;
	next();
	return true;
}

/*
Parse the arguments `<...>` for g. If `allowauto` is set, arguments
written as `auto` are left unknown, to be inferred.
*/
struct genarg *
genargs(struct scope *s, struct generic *g, bool allowauto)
{
	struct genarg *args;
	struct type *t;
	enum typequal q;
	size_t i;

	args = xreallocarray(NULL, g->nparam, sizeof(*args));
	expect(TLESS, "to open type argument list");
	for (i = 0; i < g->nparam; ++i) {
		if (i > 0) {
			if (tok.kind == TGREATER || tok.kind == TSHR)
				error(&tok.loc, "too few type arguments");
			expect(TCOMMA, "between type arguments");
		}
		args[i].type = NULL;
		args[i].qual = QUALNONE;
		args[i].size = NULL;
		args[i].constset = false;
		if (allowauto && consume(TAUTO))
			continue;
		if (g->params[i].kind == GENCONSTNESS) {
			args[i].constset = true;
			if (consume(TCONST))
				args[i].qual = QUALCONST;
			else if (tok.kind == C5_MUT)
				next();
			else if (!constarg(s, &args[i].qual))
				error(&tok.loc, "expected 'const', 'mut', or constness parameter for '%s'", g->params[i].name);
			continue;
		}
		if (g->params[i].kind == GENSIZE) {
			args[i].size = sizeargexpr(s);
			continue;
		}
		q = QUALNONE;
		t = typename(s, &q, NULL);
		if (!t)
			error(&tok.loc, "expected type for generic parameter '%s'", g->params[i].name);
		args[i].type = t;
		args[i].qual = q;
	}
	if (tok.kind == TCOMMA)
		error(&tok.loc, "too many type arguments");
	closeangle();
	return args;
}

static void
addstr(struct array *buf, const char *s)
{
	arrayaddbuf(buf, s, strlen(s));
}

static void typestr(struct array *, struct type *, enum typequal, const char *);

static void
argsstr(struct array *buf, struct generic *g, struct genarg *args)
{
	size_t i;

	char num[32];

	addstr(buf, "<");
	for (i = 0; i < g->nparam; ++i) {
		if (i > 0)
			addstr(buf, ", ");
		/* constness is erased, leaving an empty slot */
		if (g->params[i].kind == GENCONSTNESS)
			continue;
		if (g->params[i].kind == GENSIZE) {
			if (args[i].size->kind == EXPRCONST) {
				snprintf(num, sizeof(num), "%llu", args[i].size->u.constant.u);
				addstr(buf, num);
			} else if (args[i].size->kind == EXPRSIZEPARAM) {
				addstr(buf, args[i].size->u.sizeparam.gen->params[args[i].size->u.sizeparam.index].name);
			} else {
				addstr(buf, "?");
			}
			continue;
		}
		typestr(buf, args[i].type, args[i].qual, "");
	}
	addstr(buf, ">");
}

static void
qualstr(struct array *buf, enum typequal q)
{
	if (q & QUALCONST)
		addstr(buf, "const ");
	if (q & QUALVOLATILE)
		addstr(buf, "volatile ");
	if (q & QUALRESTRICT)
		addstr(buf, "restrict ");
	if (q & QUALATOMIC)
		addstr(buf, "_Atomic ");
}

/*
Write the canonical spelling of the type t with qualifiers q, as an
abstract declarator with `inner` in the position of the identifier.
*/
static void
typestr(struct array *buf, struct type *t, enum typequal q, const char *inner)
{
	struct array tmp = {0};
	struct member *m;
	struct decl *p;
	char num[32];

	switch (t->kind) {
	case TYPEPOINTER:
		if (t->base->kind == TYPEARRAY || t->base->kind == TYPEFUNC)
			addstr(&tmp, "(*");
		else
			addstr(&tmp, "*");
		if (q & QUALCONST)
			addstr(&tmp, " const");
		if (q & QUALVOLATILE)
			addstr(&tmp, " volatile");
		if (q & QUALRESTRICT)
			addstr(&tmp, " restrict");
		if ((q || *inner && *inner != '*' && *inner != '(' && *inner != '[') && *inner)
			addstr(&tmp, " ");
		addstr(&tmp, inner);
		if (t->base->kind == TYPEARRAY || t->base->kind == TYPEFUNC)
			addstr(&tmp, ")");
		arrayaddbuf(&tmp, "", 1);
		typestr(buf, t->base, t->qual, tmp.val);
		free(tmp.val);
		return;
	case TYPEARRAY:
		addstr(&tmp, inner);
		if (t->incomplete) {
			addstr(&tmp, "[]");
		} else {
			snprintf(num, sizeof(num), "[%llu]", t->size / t->base->size);
			addstr(&tmp, num);
		}
		arrayaddbuf(&tmp, "", 1);
		typestr(buf, t->base, t->qual | q, tmp.val);
		free(tmp.val);
		return;
	case TYPEFUNC:
		addstr(&tmp, inner);
		addstr(&tmp, "(");
		for (p = t->u.func.params; p; p = p->next) {
			typestr(&tmp, p->type, p->qual, "");
			if (p->next)
				addstr(&tmp, ", ");
		}
		if (t->u.func.isvararg)
			addstr(&tmp, t->u.func.params ? ", ..." : "...");
		else if (!t->u.func.params)
			addstr(&tmp, "void");
		addstr(&tmp, ")");
		arrayaddbuf(&tmp, "", 1);
		typestr(buf, t->base, t->qual, tmp.val);
		free(tmp.val);
		return;
	}
	qualstr(buf, q);
	switch (t->kind) {
	case TYPEVOID:    addstr(buf, "void"); break;
	case TYPEBOOL:    addstr(buf, "bool"); break;
	case TYPECHAR:
		if (t == &typechar)
			addstr(buf, "char");
		else
			addstr(buf, t->u.arith.issigned ? "signed char" : "unsigned char");
		break;
	case TYPESHORT:   addstr(buf, t->u.arith.issigned ? "short" : "unsigned short"); break;
	case TYPEINT:     addstr(buf, t->u.arith.issigned ? "int" : "unsigned int"); break;
	case TYPELONG:    addstr(buf, t->u.arith.issigned ? "long" : "unsigned long"); break;
	case TYPELLONG:   addstr(buf, t->u.arith.issigned ? "long long" : "unsigned long long"); break;
	case TYPEFLOAT:   addstr(buf, "float"); break;
	case TYPEDOUBLE:  addstr(buf, "double"); break;
	case TYPELDOUBLE: addstr(buf, "long double"); break;
	case TYPENULLPTR: addstr(buf, "nullptr_t"); break;
	case TYPEBITINT:
		snprintf(num, sizeof(num), "%s_BitInt(%d)", t->u.arith.issigned ? "" : "unsigned ", t->u.arith.width);
		addstr(buf, num);
		break;
	case TYPEPARAM:
		addstr(buf, t->u.param.name);
		break;
	case TYPEENUM:
		/* an enum type is compatible with its underlying integer type */
		switch (t->size) {
		case 1: addstr(buf, t->u.arith.issigned ? "signed char" : "unsigned char"); break;
		case 2: addstr(buf, t->u.arith.issigned ? "short" : "unsigned short"); break;
		case 4: addstr(buf, t->u.arith.issigned ? "int" : "unsigned int"); break;
		default: addstr(buf, t->u.arith.issigned ? "long" : "unsigned long"); break;
		}
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		if (t->u.structunion.gen) {
			addstr(buf, t->u.structunion.gen->name);
			argsstr(buf, t->u.structunion.gen, t->u.structunion.genargs);
		} else if (t->u.structunion.tag) {
			addstr(buf, t->u.structunion.tag);
		} else {
			addstr(buf, t->kind == TYPESTRUCT ? "struct {" : "union {");
			for (m = t->u.structunion.members; m; m = m->next) {
				typestr(buf, m->type, m->qual, m->name ? m->name : "");
				addstr(buf, m->next ? "; " : ";");
			}
			addstr(buf, "}");
		}
		break;
	default:
		fatal("internal error: cannot name type");
	}
	if (*inner) {
		if (*inner != '*' && *inner != '(' && *inner != '[')
			addstr(buf, " ");
		addstr(buf, inner);
	}
}

/* the canonical name of an instance of g, for example `add<int>` */
char *
geninstname(struct generic *g, struct genarg *args)
{
	struct array buf = {0};

	addstr(&buf, g->name);
	argsstr(&buf, g, args);
	arrayaddbuf(&buf, "", 1);
	return buf.val;
}
