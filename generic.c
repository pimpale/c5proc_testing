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

enum typequal
genconstbits(struct generic *g)
{
	return constbits(g);
}

/* whether t refers to the constness parameter i of g */
bool
typehasconstparam(struct type *t, struct generic *g, size_t i)
{
	struct generic one = {0};

	one.nparam = 1;
	one.params = &g->params[i];
	return typehasparam(t, &one);
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
				n->u.array.byvalue = t->u.array.byvalue;
				return n;
			}
			if (len->type->u.arith.issigned && len->u.constant.u >> 63)
				error(&tok.loc, "array length must be non-negative");
			n = mkarraytype(n, q, len->u.constant.u);
			if (t->u.array.byvalue) {
				n->u.array.byvalue = true;
				n->u.array.length = len;
				n->incomplete = false;
			}
			return n;
		}
		if (t->u.array.length && t->u.array.length->kind == EXPRCONST)
			n = mkarraytype(n, q, t->u.array.length->u.constant.u);
		else if (t->incomplete || !t->base->size)
			n = mkarraytype(n, q, 0);
		else
			n = mkarraytype(n, q, t->size / t->base->size);
		if (typedep(n) || t->u.array.byvalue)
			n->u.array.length = t->u.array.length;
		if (t->u.array.byvalue) {
			n->u.array.byvalue = true;
			n->incomplete = false;
		}
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

/*
The join of two constness arguments: const if either is, and otherwise
whichever constness parameters either one is.
*/
static enum typequal
constjoin(enum typequal a, enum typequal b)
{
	a = (a | b) & QUALCONSTANT;
	return a & QUALCONST ? QUALCONST : a;
}

/* an argument supplies the qualifiers aq where the parameter type has the qualifiers pq */
static void
scanqual(struct generic *g, struct genarg *bind, enum typequal pq, enum typequal aq, int sign)
{
	size_t i;

	if (sign < 0)
		return;
	for (i = 0; i < g->nparam; ++i) {
		/* an argument that was written out is not inferred */
		if (g->params[i].kind == GENCONSTNESS && pq & g->params[i].bit && !bind[i].constset)
			bind[i].qual = constjoin(bind[i].qual, aq);
	}
}

/*
Infer the constness parameters of g from an argument of type a for the
parameter type p: a constness parameter is const if any argument
supplies const where it occurs. `sign` is the position of p (see
genvariancecheck); in a negative position, an argument that accepts
const says nothing about the parameter, so it is ignored.
*/
void
genscanconst(struct generic *g, struct genarg *bind, struct type *p, struct type *a, int sign)
{
	struct decl *pp, *ap;
	struct generic *tg;
	struct genarg *pargs, *aargs;
	size_t i;

	if (!typehasparam(p, g) || p->kind != a->kind)
		return;
	switch (p->kind) {
	case TYPEPOINTER:
		scanqual(g, bind, p->qual, a->qual, sign);
		if (p->base->kind != TYPEFUNC && !(p->qual & QUALCONST))
			sign = 0;
		genscanconst(g, bind, p->base, a->base, sign);
		break;
	case TYPEARRAY:
		scanqual(g, bind, p->qual, a->qual, sign);
		genscanconst(g, bind, p->base, a->base, sign);
		break;
	case TYPEFUNC:
		genscanconst(g, bind, p->base, a->base, sign);
		for (pp = p->u.func.params, ap = a->u.func.params; pp && ap; pp = pp->next, ap = ap->next)
			genscanconst(g, bind, pp->type, ap->type, -sign);
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = p->u.structunion.gen;
		if (!tg || a->u.structunion.gen != tg)
			break;
		pargs = p->u.structunion.genargs;
		aargs = a->u.structunion.genargs;
		for (i = 0; i < tg->nparam; ++i) {
			if (tg->params[i].kind == GENCONSTNESS)
				scanqual(g, bind, pargs[i].qual, aargs[i].qual, sign * tg->params[i].variance);
			else if (pargs[i].type)
				genscanconst(g, bind, pargs[i].type, aargs[i].type, sign * tg->params[i].variance);
		}
		break;
	}
}

/*
Unify the parameter type p with the argument type a, binding the type
and size parameters of g in `bind`. The first occurrence of a parameter
binds it. Constness is not considered here (see genscanconst), and
parts of p that do not refer to parameters of g are not checked; the
argument is converted to the substituted parameter type afterwards.
*/
bool
genunify(struct generic *g, struct genarg *bind, struct type *p, enum typequal pq, struct type *a, enum typequal aq)
{
	struct decl *pp, *ap;
	struct genarg *b, *pargs, *aargs;
	size_t i;

	if (!typehasparam(p, g))
		return true;
	switch (p->kind) {
	case TYPEPARAM:
		b = &bind[p->u.param.index];
		/* a type parameter never captures qualifiers */
		if (!b->type) {
			b->type = a;
			b->qual = QUALNONE;
			return true;
		}
		return typeconstvariant(b->type, a);
	case TYPEPOINTER:
		if (a->kind != TYPEPOINTER)
			return false;
		return genunify(g, bind, p->base, p->qual, a->base, a->qual);
	case TYPEARRAY:
		if (a->kind != TYPEARRAY || a->u.array.byvalue != p->u.array.byvalue)
			return false;
		if (p->prop & PROPDEPLEN && a->prop & PROPDEPLEN) {
			if (!unifysize(g, bind, p->u.array.length, a->u.array.length))
				return false;
		} else if (p->prop & PROPDEPLEN && p->u.array.length->kind == EXPRSIZEPARAM && p->u.array.length->u.sizeparam.gen == g) {
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
				/* see genscanconst */
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

/*
Whether two types are const variants: the same apart from const
qualifiers and constness arguments, at any depth. Const variants have
the same representation.
*/
bool
typeconstvariant(struct type *a, struct type *b)
{
	struct decl *ap, *bp;
	struct generic *g;
	struct genarg *aargs, *bargs;
	size_t i;

	if (typecompatible(a, b))
		return true;
	if (a->kind != b->kind)
		return false;
	switch (a->kind) {
	case TYPEARRAY:
		if (!typearraylensame(a, b))
			return false;
		/* fallthrough */
	case TYPEPOINTER:
		return !((a->qual ^ b->qual) & ~QUALCONSTANT) && typeconstvariant(a->base, b->base);
	case TYPEFUNC:
		if (a->u.func.isvararg != b->u.func.isvararg || !typeconstvariant(a->base, b->base))
			return false;
		for (ap = a->u.func.params, bp = b->u.func.params; ap && bp; ap = ap->next, bp = bp->next) {
			if (!typeconstvariant(ap->type, bp->type))
				return false;
		}
		return !ap && !bp;
	case TYPESTRUCT:
	case TYPEUNION:
		g = a->u.structunion.gen;
		if (!g || b->u.structunion.gen != g)
			return false;
		aargs = a->u.structunion.genargs;
		bargs = b->u.structunion.genargs;
		for (i = 0; i < g->nparam; ++i) {
			switch (g->params[i].kind) {
			case GENCONSTNESS:
				break;
			case GENSIZE:
				if (!sizesame(aargs[i].size, bargs[i].size))
					return false;
				break;
			case GENTYPE:
				if (!typeconstvariant(aargs[i].type, bargs[i].type))
					return false;
				break;
			}
		}
		return true;
	}
	return false;
}

/*
Whether a value of type `from` converts implicitly to its const variant
`to`. Constness may only be added where nothing can be written through
the result that the source does not allow:

- an instance of a struct or union converts as the markers of its
  parameters say;
- a pointer converts to a pointer to const of a type its target
  converts to, but otherwise only to a pointer to the same type;
- a function converts to one that takes arguments which convert to
  its own parameters, and returns what its own result converts to.
*/
bool
typeconstconv(struct type *from, struct type *to)
{
	struct decl *fp, *tp;
	struct generic *g;
	struct genarg *fargs, *targs;
	size_t i;
	int v;

	if (typecompatible(from, to))
		return true;
	if (from->kind != to->kind)
		return false;
	switch (from->kind) {
	case TYPEPOINTER:
		if (!qualsubset(from->qual, to->qual))
			return false;
		if (typecompatible(from->base, to->base))
			return true;
		if (from->base->kind != TYPEFUNC && !(to->qual & QUALCONST))
			return false;
		return typeconstconv(from->base, to->base);
	case TYPEFUNC:
		if (from->u.func.isvararg != to->u.func.isvararg || !typeconstconv(from->base, to->base))
			return false;
		for (fp = from->u.func.params, tp = to->u.func.params; fp && tp; fp = fp->next, tp = tp->next) {
			if (!typeconstconv(tp->type, fp->type))
				return false;
		}
		return !fp && !tp;
	case TYPESTRUCT:
	case TYPEUNION:
		g = from->u.structunion.gen;
		if (!g || to->u.structunion.gen != g)
			return false;
		fargs = from->u.structunion.genargs;
		targs = to->u.structunion.genargs;
		for (i = 0; i < g->nparam; ++i) {
			v = g->params[i].variance;
			switch (g->params[i].kind) {
			case GENCONSTNESS:
				if (v > 0 ? !qualsubset(fargs[i].qual, targs[i].qual) : v < 0 ? !qualsubset(targs[i].qual, fargs[i].qual) : fargs[i].qual != targs[i].qual)
					return false;
				break;
			case GENSIZE:
				if (!sizesame(fargs[i].size, targs[i].size))
					return false;
				break;
			case GENTYPE:
				if (v > 0 ? !typeconstconv(fargs[i].type, targs[i].type) : v < 0 ? !typeconstconv(targs[i].type, fargs[i].type) : !typecompatible(fargs[i].type, targs[i].type))
					return false;
				break;
			}
		}
		return true;
	}
	return false;
}

/*
The const variant of t in which every constness argument is const.
Const variants have the same representation, so one instance of a mono
declaration serves all of them.
*/
struct type *
typeeraseconst(struct type *t)
{
	struct type *n, *base;
	struct generic *g;
	struct genarg *args, *newargs;
	struct decl *p, *np, **end;
	enum typequal q;
	size_t i;
	bool changed;

	switch (t->kind) {
	case TYPEPOINTER:
		base = typeeraseconst(t->base);
		return base == t->base ? t : mkpointertype(base, t->qual);
	case TYPEARRAY:
		base = typeeraseconst(t->base);
		if (base == t->base)
			return t;
		n = mktype(TYPEARRAY, t->prop);
		*n = *t;
		n->value = NULL;
		n->base = base;
		return n;
	case TYPEFUNC:
		changed = typeeraseconst(t->base) != t->base;
		for (p = t->u.func.params; p; p = p->next)
			changed |= typeeraseconst(p->type) != p->type;
		if (!changed)
			return t;
		n = mktype(TYPEFUNC, t->prop);
		*n = *t;
		n->value = NULL;
		n->base = typeeraseconst(t->base);
		end = &n->u.func.params;
		for (p = t->u.func.params; p; p = p->next) {
			np = xmalloc(sizeof(*np));
			*np = *p;
			np->type = typeeraseconst(p->type);
			*end = np;
			end = &np->next;
		}
		*end = NULL;
		return n;
	case TYPESTRUCT:
	case TYPEUNION:
		g = t->u.structunion.gen;
		if (!g || g->pattern == t)
			return t;
		args = t->u.structunion.genargs;
		newargs = xreallocarray(NULL, g->nparam, sizeof(*newargs));
		changed = false;
		for (i = 0; i < g->nparam; ++i) {
			newargs[i] = args[i];
			if (g->params[i].kind == GENCONSTNESS) {
				newargs[i].qual = QUALCONST;
				newargs[i].constset = true;
				changed |= args[i].qual != QUALCONST;
			} else if (args[i].type) {
				newargs[i].type = typeeraseconst(args[i].type);
				changed |= newargs[i].type != args[i].type;
			}
		}
		if (!changed) {
			free(newargs);
			return t;
		}
		q = QUALNONE;
		return geninst(g, newargs, &q);
	}
	return t;
}

static const char *
signname(int sign)
{
	return sign > 0 ? "positive" : sign < 0 ? "negative" : "invariant";
}

/* parameter i of g occurs in a position of the given sign in member m */
static void
varianceuse(struct generic *g, size_t i, int sign, struct member *m)
{
	int v;

	v = g->params[i].variance;
	if (v && v != sign)
		error(&tok.loc, "parameter '%s' of '%s' is declared '%c', but member '%s' uses it in %s %s position", g->params[i].name, g->name ? g->name : "<anonymous>", v > 0 ? '+' : '-', m->name ? m->name : "<anonymous>", sign ? "a" : "an", signname(sign));
}

static void
variancequal(struct generic *g, enum typequal q, int sign, struct member *m)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENCONSTNESS && q & g->params[i].bit)
			varianceuse(g, i, sign, m);
	}
}

static void
variancetype(struct generic *g, struct type *t, int sign, struct member *m)
{
	struct generic *tg;
	struct genarg *args;
	struct decl *p;
	size_t i;

	if (!typehasparam(t, g))
		return;
	switch (t->kind) {
	case TYPEPARAM:
		varianceuse(g, t->u.param.index, sign, m);
		break;
	case TYPEPOINTER:
		variancequal(g, t->qual, sign, m);
		/* something can be stored through a pointer unless it is to const, or to a function */
		if (t->base->kind != TYPEFUNC && !(t->qual & QUALCONST))
			sign = 0;
		variancetype(g, t->base, sign, m);
		break;
	case TYPEARRAY:
		variancequal(g, t->qual, sign, m);
		variancetype(g, t->base, sign, m);
		break;
	case TYPEFUNC:
		variancetype(g, t->base, sign, m);
		for (p = t->u.func.params; p; p = p->next)
			variancetype(g, p->type, -sign, m);
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		/* an argument is in the position of the parameter it is for */
		tg = t->u.structunion.gen;
		if (!tg)
			break;
		args = t->u.structunion.genargs;
		for (i = 0; i < tg->nparam; ++i) {
			if (tg->params[i].kind == GENCONSTNESS)
				variancequal(g, args[i].qual, sign * tg->params[i].variance, m);
			else if (args[i].type)
				variancetype(g, args[i].type, sign * tg->params[i].variance, m);
		}
		break;
	}
}

/*
Check the `+` and `-` markers on the parameters of the generic struct
or union g against its members. Every place a parameter appears has a
sign, the product of the signs of what it is nested in: a member, the
target of a pointer to const, and the result of a function are
positive, a parameter of a function is negative, the target of any
other pointer is zero, and an argument for another struct has the sign
of that struct's parameter. A parameter declared `+` must only appear
in positive positions, and one declared `-` only in negative ones.
*/
void
genvariancecheck(struct generic *g)
{
	struct member *m;

	for (m = g->pattern->u.structunion.members; m; m = m->next) {
		variancequal(g, m->qual, 1, m);
		variancetype(g, m->type, 1, m);
	}
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

/* parse an argument for a constness parameter: const, mut, or another constness parameter */
bool
genconstarg(struct scope *s, enum typequal *q)
{
	struct decl *d;

	*q = QUALNONE;
	if (consume(TCONST)) {
		*q = QUALCONST;
		return true;
	}
	if (tok.kind == C5_MUT) {
		next();
		return true;
	}
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
			if (!genconstarg(s, &args[i].qual))
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
		/* a type parameter is never const, so that a value of its type can always be written */
		if (q & QUALCONSTANT)
			error(&tok.loc, "argument for type parameter '%s' cannot be const-qualified; constness is passed with a constness parameter", g->params[i].name);
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

/* whether to spell out constness arguments, which instance names leave out */
static bool spellconst;

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
		if (g->params[i].kind == GENCONSTNESS) {
			if (spellconst)
				addstr(buf, !args[i].constset || args[i].qual & ~QUALCONST ? g->params[i].name : args[i].qual & QUALCONST ? "const" : "mut");
			continue;
		}
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

/* the unknown constness of destructured values, which are numbered to tell them apart */
static void
exqualstr(struct array *buf, enum typequal q, bool before)
{
	char name[32];
	int i;

	if (!spellconst || q & QUALCONST)
		return;
	for (i = 0; i < 16; ++i) {
		if (q & QUALXPARAM0 << i) {
			snprintf(name, sizeof(name), before ? " ?const%d" : "?const%d ", i + 1);
			addstr(buf, name);
		}
	}
}

static void
qualstr(struct array *buf, enum typequal q)
{
	exqualstr(buf, q, false);
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
		exqualstr(&tmp, q, true);
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
		if (t->u.array.byvalue)
			break;
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
	case TYPEARRAY:
		addstr(buf, "array<");
		typestr(buf, t->base, t->qual, "");
		if (t->u.array.length && t->u.array.length->kind == EXPRSIZEPARAM) {
			addstr(buf, ", ");
			addstr(buf, t->u.array.length->u.sizeparam.gen->params[t->u.array.length->u.sizeparam.index].name);
		} else if (t->prop & PROPDEPLEN || typedep(t->base)) {
			addstr(buf, ", ?");
		} else {
			snprintf(num, sizeof(num), ", %llu", t->base->size ? t->size / t->base->size : 0);
			addstr(buf, num);
		}
		addstr(buf, ">");
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

/*
The built-in generic struct that slices are instances of:

	forall<constness +C, type T>
	struct slice { C T *data; size_t length; };
*/
static struct generic *slicegen;

/* the type of a slice of elements of type `elem`, which have the constness `qual` */
struct type *
mkslicetype(struct type *elem, enum typequal qual)
{
	struct generic *g;
	struct genarg *args;
	struct member *data, *length;
	struct type *t;
	enum typequal q;

	if (qual & ~QUALCONSTANT)
		error(&tok.loc, "slice elements can only be qualified with const");
	if (!slicegen) {
		g = mkgeneric(false);
		g->name = "slice";
		g->nparam = 2;
		g->params = xreallocarray(NULL, 2, sizeof(g->params[0]));
		memset(g->params, 0, 2 * sizeof(g->params[0]));
		g->params[0].kind = GENCONSTNESS;
		g->params[0].name = "C";
		g->params[0].bit = QUALCPARAM0;
		g->params[0].variance = 1;
		g->params[1].kind = GENTYPE;
		g->params[1].name = "T";
		g->params[1].type = mkparamtype(g, 1, "T");
		length = xmalloc(sizeof(*length));
		memset(length, 0, sizeof(*length));
		length->name = "length";
		length->type = &typeulong;
		length->offset = 8;
		data = xmalloc(sizeof(*data));
		memset(data, 0, sizeof(*data));
		data->name = "data";
		data->type = mkpointertype(g->params[1].type, QUALCPARAM0);
		data->next = length;
		t = mktype(TYPESTRUCT, 0);
		t->size = 16;
		t->align = 8;
		t->u.structunion.tag = "slice";
		t->u.structunion.members = data;
		t->u.structunion.gen = g;
		t->u.structunion.genargs = genidentity(g);
		g->pattern = t;
		slicegen = g;
	}
	args = xreallocarray(NULL, 2, sizeof(*args));
	memset(args, 0, 2 * sizeof(*args));
	args[0].qual = constjoin(qual, QUALNONE);
	args[0].constset = true;
	args[1].type = elem;
	q = QUALNONE;
	return geninst(slicegen, args, &q);
}

bool
typeisslice(struct type *t)
{
	return slicegen && t->kind == TYPESTRUCT && t->u.structunion.gen == slicegen;
}

/* a copy of g with new parameters, and the arguments for g that refer to them */
struct generic *
genfresh(struct generic *g, struct genarg **args)
{
	struct generic *n;
	size_t i;

	n = mkgeneric(g->ismono);
	n->name = g->name;
	n->nparam = g->nparam;
	n->params = xreallocarray(NULL, g->nparam, sizeof(n->params[0]));
	for (i = 0; i < g->nparam; ++i) {
		n->params[i] = g->params[i];
		if (g->params[i].kind == GENTYPE)
			n->params[i].type = mkparamtype(n, i, g->params[i].name);
	}
	*args = genidentity(n);
	return n;
}

/*
Two-way unification, used to match the type of a given against the type
of an implicit parameter. The types on either side may refer to the
parameters of g[0] and g[1], which are bound in bind[0] and bind[1].
Only type and size parameters are bound; qualifiers must agree. In lax
mode, constness is ignored, so that the types unify if they are const
variants.
*/
static int
unifyvar(struct unifier *u, struct type *t)
{
	if (t->kind != TYPEPARAM)
		return -1;
	if (u->g[0] && t->u.param.gen == u->g[0])
		return 0;
	if (u->g[1] && t->u.param.gen == u->g[1])
		return 1;
	return -1;
}

static int
unifysizevar(struct unifier *u, struct expr *e)
{
	if (e->kind != EXPRSIZEPARAM)
		return -1;
	if (u->g[0] && e->u.sizeparam.gen == u->g[0])
		return 0;
	if (u->g[1] && e->u.sizeparam.gen == u->g[1])
		return 1;
	return -1;
}

static bool
unifysizes(struct unifier *u, struct expr *a, struct expr *b, int depth)
{
	struct genarg *bd;
	int k;

	if (depth > 64)
		return false;
	k = unifysizevar(u, a);
	if (k >= 0) {
		bd = &u->bind[k][a->u.sizeparam.index];
		if (bd->size && unifysizevar(u, bd->size) != k)
			return unifysizes(u, bd->size, b, depth + 1);
		if (unifysizevar(u, b) == k && b->u.sizeparam.index == a->u.sizeparam.index)
			return true;
		bd->size = b;
		return true;
	}
	k = unifysizevar(u, b);
	if (k >= 0) {
		bd = &u->bind[k][b->u.sizeparam.index];
		if (bd->size && unifysizevar(u, bd->size) != k)
			return unifysizes(u, a, bd->size, depth + 1);
		bd->size = a;
		return true;
	}
	return sizesame(a, b);
}

static struct expr *
arraylen(struct type *t)
{
	if (t->prop & PROPDEPLEN)
		return t->u.array.length;
	if (t->incomplete || t->prop & PROPVM || !t->base->size && !t->u.array.byvalue)
		return NULL;
	if (t->u.array.length && t->u.array.length->kind == EXPRCONST)
		return t->u.array.length;
	return mkconstsize(t->base->size ? t->size / t->base->size : 0);
}

static struct genarg *partialargs(struct generic *, struct genarg *);

static bool
unifytypes(struct unifier *u, struct type *a, enum typequal aq, struct type *b, enum typequal bq, int depth)
{
	struct genarg *bd, *aargs, *bargs;
	struct generic *tg;
	struct decl *ap, *bp;
	struct expr *al, *bl;
	size_t i;
	int k;

	if (depth > 64)
		return false;
	if (u->lax) {
		aq &= ~QUALCONSTANT;
		bq &= ~QUALCONSTANT;
	}
	k = unifyvar(u, a);
	if (k >= 0) {
		bd = &u->bind[k][a->u.param.index];
		if (bd->type && bd->type != a)
			return unifytypes(u, bd->type, bd->qual | aq, b, bq, depth + 1);
		if (b == a)
			return aq == bq;
		/* the variable takes the qualifiers of the other side that it does not already have */
		if ((aq & bq) != aq)
			return false;
		bd->type = b;
		bd->qual = bq & ~aq;
		return true;
	}
	k = unifyvar(u, b);
	if (k >= 0) {
		bd = &u->bind[k][b->u.param.index];
		if (bd->type && bd->type != b)
			return unifytypes(u, a, aq, bd->type, bd->qual | bq, depth + 1);
		if ((aq & bq) != bq)
			return false;
		bd->type = a;
		bd->qual = aq & ~bq;
		return true;
	}
	if (aq != bq)
		return false;
	if (a == b)
		return true;
	if (a->kind != b->kind)
		return typecompatible(a, b);
	switch (a->kind) {
	case TYPEPOINTER:
		return unifytypes(u, a->base, a->qual, b->base, b->qual, depth + 1);
	case TYPEARRAY:
		if (a->u.array.byvalue != b->u.array.byvalue)
			return false;
		al = arraylen(a);
		bl = arraylen(b);
		if (!al != !bl || al && !unifysizes(u, al, bl, depth + 1))
			return false;
		return unifytypes(u, a->base, a->qual, b->base, b->qual, depth + 1);
	case TYPEFUNC:
		if (a->u.func.isvararg != b->u.func.isvararg)
			return false;
		if (!unifytypes(u, a->base, a->qual, b->base, b->qual, depth + 1))
			return false;
		for (ap = a->u.func.params, bp = b->u.func.params; ap && bp; ap = ap->next, bp = bp->next) {
			if (!unifytypes(u, ap->type, QUALNONE, bp->type, QUALNONE, depth + 1))
				return false;
		}
		return !ap && !bp;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = a->u.structunion.gen;
		if (!tg || tg != b->u.structunion.gen)
			return false;
		aargs = a->u.structunion.genargs;
		bargs = b->u.structunion.genargs;
		for (i = 0; i < tg->nparam; ++i) {
			switch (tg->params[i].kind) {
			case GENCONSTNESS:
				if (!u->lax && aargs[i].qual != bargs[i].qual)
					return false;
				break;
			case GENSIZE:
				if (!unifysizes(u, aargs[i].size, bargs[i].size, depth + 1))
					return false;
				break;
			case GENTYPE:
				if (!unifytypes(u, aargs[i].type, aargs[i].qual, bargs[i].type, bargs[i].qual, depth + 1))
					return false;
				break;
			}
		}
		return true;
	}
	return typecompatible(a, b);
}

bool
unify(struct unifier *u, struct type *a, enum typequal aq, struct type *b, enum typequal bq)
{
	return unifytypes(u, a, aq, b, bq, 0);
}

/* substitute the arguments for g that are known in `bind` into t */
struct type *
genpartial(struct generic *g, struct genarg *bind, struct type *t, enum typequal *tq)
{
	if (!typehasparam(t, g))
		return t;
	return typesubst(t, tq, g, partialargs(g, bind));
}

/* arguments for g where parameters not bound in `bind` stand for themselves */
static struct genarg *
partialargs(struct generic *g, struct genarg *bind)
{
	struct genarg *args;
	size_t i;

	args = genidentity(g);
	for (i = 0; i < g->nparam; ++i) {
		switch (g->params[i].kind) {
		case GENTYPE:
			if (bind[i].type)
				args[i] = bind[i];
			break;
		case GENSIZE:
			if (bind[i].size)
				args[i] = bind[i];
			break;
		case GENCONSTNESS:
			if (bind[i].constset)
				args[i] = bind[i];
			break;
		}
	}
	return args;
}

/*
Substitute the bindings made by unification into t, until it no longer
refers to bound parameters.
*/
struct type *
unifyresolve(struct unifier *u, struct type *t, enum typequal *tq)
{
	struct type *old;
	int k, n;

	for (n = 0; n < 16; ++n) {
		old = t;
		for (k = 0; k < 2; ++k) {
			if (u->g[k] && typehasparam(t, u->g[k]))
				t = typesubst(t, tq, u->g[k], partialargs(u->g[k], u->bind[k]));
		}
		if (t == old)
			break;
	}
	return t;
}

struct expr *
unifyresolvesize(struct unifier *u, struct expr *e)
{
	struct expr *b;
	int k, n;

	for (n = 0; n < 16; ++n) {
		k = unifysizevar(u, e);
		if (k < 0)
			break;
		b = u->bind[k][e->u.sizeparam.index].size;
		if (!b || unifysizevar(u, b) == k && b->u.sizeparam.index == e->u.sizeparam.index)
			break;
		e = b;
	}
	return e;
}

/* number of type constructors and variables in t, for the Paterson conditions */
size_t
typecomplexity(struct type *t)
{
	struct generic *tg;
	struct decl *p;
	size_t n, i;

	n = 1;
	switch (t->kind) {
	case TYPEPOINTER:
	case TYPEARRAY:
		n += typecomplexity(t->base);
		break;
	case TYPEFUNC:
		n += typecomplexity(t->base);
		for (p = t->u.func.params; p; p = p->next)
			n += typecomplexity(p->type);
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		if (!tg)
			break;
		for (i = 0; i < tg->nparam; ++i) {
			if (tg->params[i].kind == GENTYPE)
				n += typecomplexity(t->u.structunion.genargs[i].type);
		}
		break;
	}
	return n;
}

/* number of occurrences of the type parameter `var` in t */
size_t
typeoccurs(struct type *t, struct type *var)
{
	struct generic *tg;
	struct decl *p;
	size_t n, i;

	n = 0;
	switch (t->kind) {
	case TYPEPARAM:
		return t == var;
	case TYPEPOINTER:
	case TYPEARRAY:
		return typeoccurs(t->base, var);
	case TYPEFUNC:
		n += typeoccurs(t->base, var);
		for (p = t->u.func.params; p; p = p->next)
			n += typeoccurs(p->type, var);
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		if (!tg)
			break;
		for (i = 0; i < tg->nparam; ++i) {
			if (tg->params[i].kind == GENTYPE)
				n += typeoccurs(t->u.structunion.genargs[i].type, var);
		}
		break;
	}
	return n;
}

/* the canonical spelling of a type, for diagnostics */
char *
typespelling(struct type *t, enum typequal q)
{
	struct array buf = {0};

	spellconst = true;
	typestr(&buf, t, q, "");
	spellconst = false;
	arrayaddbuf(&buf, "", 1);
	return buf.val;
}
