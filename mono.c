#include <assert.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

/*
A mono function is parsed and checked once, with its type parameters
treated as types of unknown layout. Each instance is lowered from a
copy of the function body with the type arguments substituted, so the
backend only ever sees concrete types.
*/

struct ptrmap {
	size_t len, cap;
	void **keys, **vals;
};

static size_t
ptrhash(void *p)
{
	uintptr_t x = (uintptr_t)p;

	x ^= x >> 17;
	x *= 0x9e3779b97f4a7c15u;
	return x ^ x >> 29;
}

static void *
ptrget(struct ptrmap *m, void *k)
{
	size_t i;

	if (!m->cap)
		return NULL;
	for (i = ptrhash(k) & m->cap - 1; m->keys[i]; i = i + 1 & m->cap - 1) {
		if (m->keys[i] == k)
			return m->vals[i];
	}
	return NULL;
}

static void
ptrput(struct ptrmap *m, void *k, void *v)
{
	void **oldkeys, **oldvals;
	size_t i, oldcap;

	if (m->len >= m->cap / 2) {
		oldkeys = m->keys;
		oldvals = m->vals;
		oldcap = m->cap;
		m->cap = oldcap ? oldcap * 2 : 64;
		m->keys = xreallocarray(NULL, m->cap, sizeof(m->keys[0]));
		m->vals = xreallocarray(NULL, m->cap, sizeof(m->vals[0]));
		memset(m->keys, 0, m->cap * sizeof(m->keys[0]));
		m->len = 0;
		for (i = 0; i < oldcap; ++i) {
			if (oldkeys[i])
				ptrput(m, oldkeys[i], oldvals[i]);
		}
		free(oldkeys);
		free(oldvals);
	}
	for (i = ptrhash(k) & m->cap - 1; m->keys[i]; i = i + 1 & m->cap - 1) {
		if (m->keys[i] == k) {
			m->vals[i] = v;
			return;
		}
	}
	m->keys[i] = k;
	m->vals[i] = v;
	++m->len;
}

static void
ptrfree(struct ptrmap *m)
{
	free(m->keys);
	free(m->vals);
}

struct inst {
	/* the mono function, its arguments, and the instance */
	struct decl *decl;
	struct genarg *args;
	struct decl *inst;
	/* where the instance was first requested, and by which instance */
	struct location loc;
	struct inst *parent;
	struct inst *next;
};

static struct inst *insts, **instsend = &insts;
/* the instance being created */
static struct inst *curinst;

/* explain which instantiations led to an error */
static void
instnotes(void)
{
	struct inst *i;

	for (i = curinst; i; i = i->parent) {
		diagloc(&i->loc);
		fprintf(stderr, "note: in instantiation of '%s'\n", i->inst->name);
	}
}

/* state for copying a function body for an instance */
struct copy {
	struct generic *gen;
	struct genarg *args;
	struct ptrmap decls, exprs, stmts;
};

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

/* the instance of the mono function d for the arguments `args` */
struct decl *
monoinst(struct decl *d, struct genarg *args)
{
	struct inst *i;
	struct decl *n;
	struct type *t;
	enum typequal q;
	char *name;

	assert(d->gen && d->gen->ismono);
	for (i = insts; i; i = i->next) {
		if (i->decl == d && argssame(d->gen, i->args, args))
			return i->inst;
	}
	name = geninstname(d->gen, args);
	q = QUALNONE;
	t = typesubst(d->type, &q, d->gen, args);
	/* XXX: instances should be shared between translation units */
	n = mkdecl(name, DECLFUNC, t, d->qual | q, LINKINTERN);
	n->asmname = name;
	n->value = mkglobal(n);
	n->u.func.isnoreturn = d->u.func.isnoreturn;
	n->defined = true;

	i = xmalloc(sizeof(*i));
	i->decl = d;
	i->args = args;
	i->inst = n;
	/* not a conditional expression, to avoid a QBE 1.3 bug with conditional moves */
	if (curinst)
		i->loc = curinst->loc;
	else
		i->loc = tok.loc;
	i->parent = curinst;
	i->next = NULL;
	*instsend = i;
	instsend = &i->next;
	return n;
}

static struct type *
copytype(struct copy *c, struct type *t, enum typequal *tq)
{
	t = typesubst(t, tq, c->gen, c->args);
	return t;
}

static struct decl *
copydecl(struct copy *c, struct decl *d)
{
	struct decl *n;
	enum typequal q;

	n = ptrget(&c->decls, d);
	if (n)
		return n;
	/* only automatic objects and static locals belong to the instance */
	if (d->kind != DECLOBJECT || d->linkage != LINKNONE || d->u.obj.storage != SDAUTO && !d->u.obj.mono)
		return d;
	q = d->qual;
	n = mkdecl(d->name, DECLOBJECT, copytype(c, d->type, &q), q, LINKNONE);
	n->u.obj = d->u.obj;
	n->u.obj.mono = false;
	if (n->u.obj.align < n->type->align)
		n->u.obj.align = n->type->align;
	n->defined = d->defined;
	if (d->u.obj.mono)
		n->value = mkglobal(n);
	ptrput(&c->decls, d, n);
	return n;
}

static struct expr *copyexpr(struct copy *, struct expr *);

static struct init *
copyinit(struct copy *c, struct init *init, struct type *oldtype, struct type *newtype)
{
	struct init *head, **end, *n;

	end = &head;
	for (; init; init = init->next) {
		n = mkinit(init->start, init->end, init->bits, copyexpr(c, init->expr));
		n->path = init->path;
		n->npath = init->npath;
		*end = n;
		end = &n->next;
	}
	*end = NULL;
	/* offsets of initializers for dependent types are computed now that the type is known */
	if (typedep(oldtype))
		head = initresolve(head, newtype);
	return head;
}

static struct type *
copytypeonly(struct copy *c, struct type *t)
{
	enum typequal q = QUALNONE;

	return copytype(c, t, &q);
}

static struct expr *
copylayout(struct copy *c, struct expr *e)
{
	struct expr *n;
	struct type *t;
	enum typequal q;
	unsigned long long v;

	q = QUALNONE;
	t = copytype(c, e->u.layout.type, &q);
	assert(!typedep(t));
	switch (e->u.layout.kind) {
	case LAYOUTSIZE:
		v = t->size;
		break;
	case LAYOUTALIGN:
		v = t->align;
		break;
	case LAYOUTOFFSET:
		v = 0;
		if (!typemember(t, e->u.layout.member, &v))
			fatal("internal error: member '%s' missing from instance", e->u.layout.member);
		break;
	default:
		fatal("internal error: unknown layout expression");
	}
	n = xmalloc(sizeof(*n));
	memset(n, 0, sizeof(*n));
	n->kind = EXPRCONST;
	n->type = &typeulong;
	n->u.constant.u = v;
	return n;
}

static struct expr *
copyexprs(struct copy *c, struct expr *e)
{
	struct expr *head, **end;

	end = &head;
	for (; e; e = e->next) {
		*end = copyexpr(c, e);
		end = &(*end)->next;
	}
	*end = NULL;
	return head;
}

static struct expr *
copyexpr(struct copy *c, struct expr *e)
{
	struct expr *n;
	struct decl *d;
	struct genarg *args;
	enum typequal q;
	size_t i;

	if (!e)
		return NULL;
	n = ptrget(&c->exprs, e);
	if (n)
		return n;
	if (e->kind == EXPRLAYOUT && !typedep(copytypeonly(c, e->u.layout.type))) {
		n = copylayout(c, e);
		ptrput(&c->exprs, e, n);
		return n;
	}
	n = xmalloc(sizeof(*n));
	*n = *e;
	ptrput(&c->exprs, e, n);
	q = QUALNONE;
	n->type = copytype(c, e->type, &q);
	n->qual |= q;
	n->next = NULL;
	n->toeval = copyexpr(c, e->toeval);
	if (e->kind != EXPRCOMMA)
		n->base = copyexpr(c, e->base);
	switch (e->kind) {
	case EXPRIDENT:
		d = e->u.ident.decl;
		if (d->gen && d->kind == DECLFUNC && e->u.ident.genargs) {
			args = xreallocarray(NULL, d->gen->nparam, sizeof(*args));
			for (i = 0; i < d->gen->nparam; ++i) {
				args[i].qual = e->u.ident.genargs[i].qual;
				args[i].type = copytype(c, e->u.ident.genargs[i].type, &args[i].qual);
			}
			n->u.ident.genargs = args;
			if (d->gen->ismono)
				n->u.ident.decl = monoinst(d, args);
		} else {
			n->u.ident.decl = copydecl(c, d);
		}
		break;
	case EXPRCALL:
		n->u.call.args = copyexprs(c, e->u.call.args);
		break;
	case EXPRBITFIELD:
		if (e->u.bitfield.type) {
			unsigned long long off = 0;
			struct member *m;

			q = QUALNONE;
			m = typemember(copytype(c, e->u.bitfield.type, &q), e->u.bitfield.member, &off);
			n->u.bitfield.bits = m->bits;
			n->u.bitfield.type = NULL;
		}
		break;
	case EXPRCOMPOUND:
		n->u.compound.decl = copydecl(c, e->u.compound.decl);
		n->u.compound.init = copyinit(c, e->u.compound.init, e->u.compound.decl->type, n->u.compound.decl->type);
		break;
	case EXPRBINARY:
		n->u.binary.l = copyexpr(c, e->u.binary.l);
		n->u.binary.r = copyexpr(c, e->u.binary.r);
		break;
	case EXPRCOND:
		n->u.cond.t = copyexpr(c, e->u.cond.t);
		n->u.cond.f = copyexpr(c, e->u.cond.f);
		break;
	case EXPRASSIGN:
		n->u.assign.l = copyexpr(c, e->u.assign.l);
		n->u.assign.r = copyexpr(c, e->u.assign.r);
		break;
	case EXPRCOMMA:
		n->base = copyexprs(c, e->base);
		break;
	case EXPRSIZEOF:
		q = QUALNONE;
		n->u.szof.type = copytype(c, e->u.szof.type, &q);
		break;
	case EXPRLAYOUT:
		/* the type still depends on other mono parameters */
		q = QUALNONE;
		n->u.layout.type = copytype(c, e->u.layout.type, &q);
		break;
	}
	return n;
}

/* the copy of a statement, which may be referred to before it is copied */
static struct stmt *
stmtref(struct copy *c, struct stmt *st)
{
	struct stmt *n;

	if (!st)
		return NULL;
	n = ptrget(&c->stmts, st);
	if (!n) {
		n = xmalloc(sizeof(*n));
		memset(n, 0, sizeof(*n));
		ptrput(&c->stmts, st, n);
	}
	return n;
}

static struct stmt *copystmt(struct copy *, struct stmt *);

static struct stmt *
copystmts(struct copy *c, struct stmt *st)
{
	struct stmt *head, **end;

	end = &head;
	for (; st; st = st->next) {
		*end = copystmt(c, st);
		end = &(*end)->next;
	}
	*end = NULL;
	return head;
}

static struct stmt *
copystmt(struct copy *c, struct stmt *st)
{
	struct stmt *n;
	struct decl *d;

	n = stmtref(c, st);
	*n = *st;
	n->next = NULL;
	n->defer = stmtref(c, st->defer);
	n->breaklabel = NULL;
	n->continuelabel = NULL;
	switch (st->kind) {
	case STMTCOMPOUND:
		n->u.compound.body = copystmts(c, st->u.compound.body);
		n->u.compound.enddefer = stmtref(c, st->u.compound.enddefer);
		break;
	case STMTEXPR:
	case STMTRETURN:
		n->u.expr = copyexpr(c, st->u.expr);
		break;
	case STMTDECL:
		d = st->u.decl.decl;
		if (d) {
			n->u.decl.decl = copydecl(c, d);
			n->u.decl.init = copyinit(c, st->u.decl.init, d->type, n->u.decl.decl->type);
			if (d->u.obj.mono) {
				/* a static local is defined when the instance is created, not when it is reached */
				emitdata(n->u.decl.decl, n->u.decl.init);
				n->u.decl.decl = NULL;
			}
		}
		n->u.decl.vm = copyexpr(c, st->u.decl.vm);
		break;
	case STMTIF:
		n->u.ifstmt.cond = copyexpr(c, st->u.ifstmt.cond);
		n->u.ifstmt.then = copystmts(c, st->u.ifstmt.then);
		n->u.ifstmt.els = copystmts(c, st->u.ifstmt.els);
		break;
	case STMTSWITCH:
		n->u.switchstmt.cond = copyexpr(c, st->u.switchstmt.cond);
		n->u.switchstmt.body = copystmts(c, st->u.switchstmt.body);
		n->u.switchstmt.seen = NULL;
		break;
	case STMTCASE:
	case STMTDEFAULT:
		n->u.caselabel.switchstmt = stmtref(c, st->u.caselabel.switchstmt);
		break;
	case STMTWHILE:
	case STMTDO:
	case STMTFOR:
		n->u.loop.init = copystmts(c, st->u.loop.init);
		n->u.loop.cond = copyexpr(c, st->u.loop.cond);
		n->u.loop.post = copyexpr(c, st->u.loop.post);
		n->u.loop.body = copystmts(c, st->u.loop.body);
		break;
	case STMTLABEL:
		n->u.label.indefer = stmtref(c, st->u.label.indefer);
		n->u.label.block = NULL;
		n->u.label.epoch = 0;
		break;
	case STMTGOTO:
	case STMTBREAK:
	case STMTCONTINUE:
		n->u.jump.target = stmtref(c, st->u.jump.target);
		n->u.jump.indefer = stmtref(c, st->u.jump.indefer);
		n->u.jump.nextgoto = NULL;
		break;
	case STMTDEFER:
		n->u.defer.body = copystmts(c, st->u.defer.body);
		n->u.defer.prev = stmtref(c, st->u.defer.prev);
		break;
	case STMTSTATICASSERT:
		n->u.staticassert.cond = eval(copyexpr(c, st->u.staticassert.cond));
		if (n->u.staticassert.cond->kind != EXPRCONST || !(n->u.staticassert.cond->type->prop & PROPINT))
			error(&st->u.staticassert.loc, "not an integer constant expression");
		if (!n->u.staticassert.cond->u.constant.u) {
			if (st->u.staticassert.hasmsg)
				error(&st->u.staticassert.loc, "static assertion failed: %.*s", (int)(st->u.staticassert.msg.size - 1), (char *)st->u.staticassert.msg.data);
			error(&st->u.staticassert.loc, "static assertion failed");
		}
		break;
	}
	return n;
}

/*
Substitute the arguments `args` for the parameters of g in a constant
expression, and evaluate it.
*/
struct expr *
constsubst(struct expr *e, struct generic *g, struct genarg *args)
{
	struct copy c;

	memset(&c, 0, sizeof(c));
	c.gen = g;
	c.args = args;
	e = eval(copyexpr(&c, e));
	ptrfree(&c.decls);
	ptrfree(&c.exprs);
	ptrfree(&c.stmts);
	return e;
}

static void
instantiate(struct inst *i)
{
	struct decl *d, *op, *np;
	struct copy c;
	struct type *t;
	struct scope *s;
	struct func *f;
	struct stmt *body;
	enum typequal q;

	d = i->decl;
	if (!d->u.func.body)
		error(&i->loc, "mono function '%s' is used but not defined in this translation unit", d->name);
	curinst = i;
	memset(&c, 0, sizeof(c));
	/* the body refers to the parameters of its own definition */
	c.gen = d->u.func.defgen;
	c.args = i->args;
	q = QUALNONE;
	t = copytype(&c, d->u.func.deftype, &q);
	for (op = d->u.func.deftype->u.func.params, np = t->u.func.params; op && np; op = op->next, np = np->next)
		ptrput(&c.decls, op, np);

	s = mkscope(&filescope);
	f = mkfunc(i->inst, i->inst->name, t, s);
	ptrput(&c.decls, d->u.func.namedecl, scopegetdecl(s, "__func__", false));
	body = copystmts(&c, d->u.func.body);
	lower(f, body);
	if (d->u.func.isnoreturn)
		funchlt(f);
	emitfunc(f, false);
	delfunc(f);
	delscope(s);
	ptrfree(&c.decls);
	ptrfree(&c.exprs);
	ptrfree(&c.stmts);
	curinst = NULL;
}

/* emit the instances of mono functions, including those they use in turn */
void
emitmonoinsts(void)
{
	struct inst *i;

	errornotes = instnotes;
	for (i = insts; i; i = i->next)
		instantiate(i);
	errornotes = NULL;
}
