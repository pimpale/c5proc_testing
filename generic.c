#include <stdbool.h>
#include <stddef.h>
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
	/* the size of a generic type parameter is never known */
	t->incomplete = true;
	t->u.param.gen = g;
	t->u.param.index = index;
	t->u.param.name = name;
	return t;
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
	case TYPEPOINTER:
	case TYPEARRAY:
		return typehasparam(t->base, g);
	case TYPEFUNC:
		if (typehasparam(t->base, g))
			return true;
		for (p = t->u.func.params; p; p = p->next) {
			if (typehasparam(p->type, g))
				return true;
		}
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		tg = t->u.structunion.gen;
		if (!tg)
			break;
		for (i = 0; i < tg->nparam; ++i) {
			if (typehasparam(t->u.structunion.genargs[i].type, g))
				return true;
		}
		break;
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
	enum typequal q;
	size_t i;

	if (!typehasparam(t, g))
		return t;
	switch (t->kind) {
	case TYPEPARAM:
		*tq |= args[t->u.param.index].qual;
		return args[t->u.param.index].type;
	case TYPEPOINTER:
		q = t->qual;
		n = typesubst(t->base, &q, g, args);
		return mkpointertype(n, q);
	case TYPEARRAY:
		q = t->qual;
		n = typesubst(t->base, &q, g, args);
		if (t->incomplete || !t->base->size)
			return mkarraytype(n, q, 0);
		return mkarraytype(n, q, t->size / t->base->size);
	case TYPEFUNC:
		n = mktype(TYPEFUNC, t->prop);
		*n = *t;
		n->value = NULL;
		q = t->qual;
		n->base = typesubst(t->base, &q, g, args);
		n->qual = q;
		end = &n->u.func.params;
		for (p = t->u.func.params; p; p = p->next) {
			np = xmalloc(sizeof(*np));
			*np = *p;
			q = p->qual;
			np->type = typesubst(p->type, &q, g, args);
			np->qual = q;
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
			q = t->u.structunion.genargs[i].qual;
			newargs[i].type = typesubst(t->u.structunion.genargs[i].type, &q, g, args);
			newargs[i].qual = q;
		}
		return geninst(tg, newargs, tq);
	}
	fatal("internal error: unexpected type in substitution");
	return NULL;
}

static bool
argssame(struct generic *g, struct genarg *a1, struct genarg *a2)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		if (a1[i].qual != a2[i].qual || !typesame(a1[i].type, a2[i].type))
			return false;
	}
	return true;
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
		if (args[i].type != g->params[i].type || args[i].qual)
			break;
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
		q = m->qual;
		nm->type = typesubst(m->type, &q, g, args);
		nm->qual = q;
		*end = nm;
		end = &nm->next;
	}
	*end = NULL;
	return t;
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
		if (a->qual & ~p->qual && p->base->kind != TYPEPARAM)
			return false;
		return genunify(g, bind, p->base, p->qual, a->base, a->qual);
	case TYPEARRAY:
		if (a->kind != TYPEARRAY)
			return false;
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
			if (!genunify(g, bind, pargs[i].type, pargs[i].qual, aargs[i].type, aargs[i].qual))
				return false;
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
		if (allowauto && consume(TAUTO)) {
			args[i].type = NULL;
			args[i].qual = QUALNONE;
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
