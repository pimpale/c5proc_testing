#include <assert.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct stmt *
addstmt(struct stmt ***end, enum stmtkind kind)
{
	struct stmt *st;

	st = xmalloc(sizeof(*st));
	memset(st, 0, sizeof(*st));
	st->kind = kind;
	**end = st;
	*end = &st->next;

	return st;
}

struct caselabel {
	struct treenode node;
	struct stmt *stmt;
};

/*
A destructuring pattern: a brace-enclosed list of elements, which are
matched against the members of a struct or union like the initializers
of an initializer list. An element binds a name to the member (or skips
it, if it has no name), matches the member against a nested pattern, or
in a case label, requires the member to equal a constant.
*/
struct pattern {
	enum {
		PATBIND,
		PATCONST,
		PATSUB,
	} kind;
	struct location loc;
	/* member name, if designated */
	char *member;
	/* name and type of a binding; the type is NULL for auto */
	struct decl *binding;
	/* constant, or inclusive range of constants */
	struct expr *lo, *hi;
	struct pattern *sub;
	struct pattern *next;
};

static struct expr *
patternconst(struct scope *s)
{
	struct expr *e;

	e = eval(condexpr(s));
	if (e->kind != EXPRCONST)
		error(&tok.loc, "constant in pattern is not a constant expression");
	return e;
}

static struct pattern *
parsepattern(struct scope *s, bool allowconst)
{
	struct pattern *head, **end, *p;

	expect(TLBRACE, "to open pattern");
	head = NULL;
	end = &head;
	while (tok.kind != TRBRACE) {
		p = xmalloc(sizeof(*p));
		memset(p, 0, sizeof(*p));
		p->loc = tok.loc;
		if (consume(TPERIOD)) {
			p->member = expect(TIDENT, "for member name");
			expect(TASSIGN, "after member name");
		}
		if (tok.kind == TLBRACE) {
			p->kind = PATSUB;
			p->sub = parsepattern(s, allowconst);
		} else if (tok.kind == TAUTO || istypestart(s)) {
			p->kind = PATBIND;
			p->binding = patternbinding(s);
		} else if (allowconst) {
			p->kind = PATCONST;
			p->lo = patternconst(s);
			if (consume(TELLIPSIS))
				p->hi = patternconst(s);
		} else {
			error(&tok.loc, "expected a type or 'auto' to bind a name in pattern");
		}
		*end = p;
		end = &p->next;
		if (!consume(TCOMMA))
			break;
	}
	expect(TRBRACE, "to close pattern");
	if (!head)
		error(&tok.loc, "pattern has no elements");
	return head;
}

/*
Match the pattern p against the struct or union `obj`. The names it
binds are declared in s, as aliases for the members. The condition for
the constants in the pattern to match is added to *cond.
*/
static void
applypattern(struct scope *s, struct pattern *p, struct expr *obj, struct expr **cond, bool *bound)
{
	struct type *t, *mt;
	struct member *m, *cur;
	struct genarg *exargs;
	struct expr *e, *c;
	struct decl *d;
	enum typequal mq;
	unsigned long long offset;

	t = obj->type;
	if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
		error(&p->loc, "pattern can only match a struct or union");
	if (t->incomplete)
		error(&p->loc, "pattern matches incomplete struct or union");
	/* this value has its own types for existential parameters, which the bindings share */
	exargs = t->u.structunion.exists ? exopen(t->u.structunion.exists) : NULL;
	cur = t->u.structunion.members;
	for (; p; p = p->next) {
		offset = 0;
		if (p->member) {
			m = typemember(t, p->member, &offset);
			if (!m)
				error(&p->loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", p->member);
			for (cur = t->u.structunion.members; cur && cur != m; cur = cur->next)
				;
		} else {
			if (!cur)
				error(&p->loc, "pattern has more elements than the %s has members", t->kind == TYPEUNION ? "union" : "struct");
			m = cur;
			offset = m->offset;
		}
		if (cur)
			cur = cur->next;
		e = exprmember(exprdup(obj), t, m, offset, exargs);
		switch (p->kind) {
		case PATSUB:
			applypattern(s, p->sub, e, cond, bound);
			break;
		case PATCONST:
			if (!(e->type->prop & PROPSCALAR) || e->decayed)
				error(&p->loc, "constant in pattern requires a member of scalar type");
			if (p->hi)
				c = exprcompare(TLAND, exprcompare(TGEQ, e, p->lo), exprcompare(TLEQ, exprdup(e), p->hi));
			else
				c = exprcompare(TEQL, e, p->lo);
			*cond = *cond ? exprcompare(TLAND, *cond, c) : c;
			break;
		case PATBIND:
			d = p->binding;
			mt = e->decayed ? e->base->type : e->type;
			mq = e->decayed ? e->base->qual : e->qual;
			if (d->type && !typecompatible(d->type, mt))
				error(&p->loc, "binding '%s' has a type that is incompatible with the member it is bound to", d->name ? d->name : "<unnamed>");
			if (!d->name)
				break;
			if (scopegetdecl(s, d->name, false))
				error(&p->loc, "redeclaration of '%s' in pattern", d->name);
			d->type = mt;
			d->qual |= mq;
			if (e->decayed)
				e->base->qual = d->qual;
			else
				e->qual = d->qual;
			d->u.alias = e;
			scopeputdecl(s, d);
			*bound = true;
			break;
		}
	}
}

/* an unnamed object initialized with e, to match patterns against */
static struct expr *
patternobject(struct expr *e, struct stmt ***end)
{
	struct type *t;
	struct decl *d;
	struct stmt *st;

	t = e->type;
	if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
		error(&tok.loc, "destructured value must be a struct or union");
	if (t->incomplete)
		error(&tok.loc, "destructured value has incomplete type");
	d = mkdecl(NULL, DECLOBJECT, t, QUALNONE, LINKNONE);
	d->u.obj.storage = SDAUTO;
	d->defined = true;
	st = addstmt(end, STMTDECL);
	st->u.decl.decl = d;
	st->u.decl.init = mkinit(0, t->size, (struct bitfield){0}, e);
	st->u.decl.hasinit = true;
	return exprident(d);
}

/* destructuring declaration: pattern = expression; */
static void
destructure(struct scope *s, struct stmt ***end)
{
	struct pattern *p;
	struct expr *e, *cond;
	bool bound;

	p = parsepattern(s, false);
	expect(TASSIGN, "after pattern");
	e = assignexpr(s);
	expect(TSEMICOLON, "after destructuring declaration");
	cond = NULL;
	bound = false;
	applypattern(s, p, patternobject(e, end), &cond, &bound);
}

static void compound(struct funcctx *, struct scope *, struct stmt ***);

/* add a case label that is tested with a condition, after those before it */
static void
addtest(struct stmt *sw, struct stmt *st, struct expr *cond)
{
	struct stmt **end;

	st->u.caselabel.istest = true;
	st->u.caselabel.cond = cond;
	for (end = &sw->u.switchstmt.tests; *end; end = &(*end)->u.caselabel.nexttest)
		;
	*end = st;
}

/*
6.8.1 Labeled statements

Returns 0 if there is no label, 1 if a label was parsed, and 2 if a case
label was parsed along with the block that follows it.
*/
static int
label(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	char *name;
	struct stmt *st, *sw;
	struct caselabel *c;
	struct mapkey key;
	size_t idx;
	unsigned long long i, j, k;
	struct pattern *pat;
	struct scope *cs;
	struct expr *cond;
	struct type *t;
	bool bound;

	attr(NULL, 0);
	switch (tok.kind) {
	case TCASE:
		next();
		sw = s->switchstmt;
		if (!sw)
			error(&tok.loc, "'case' label must be in switch");
		if (s->defer != sw->defer)
			error(&tok.loc, "'case' label must not be in the scope of a defer statement in its switch");
		if (sw->u.switchstmt.subject) {
			/* the first case whose pattern matches is selected */
			if (tok.kind != TLBRACE)
				error(&tok.loc, "'case' label of a switch on a struct or union must be a pattern");
			pat = parsepattern(s, true);
			expect(TCOLON, "after case pattern");
			st = addstmt(end, STMTCASE);
			st->u.caselabel.switchstmt = sw;
			cs = mkscope(s);
			cond = NULL;
			bound = false;
			applypattern(cs, pat, sw->u.switchstmt.subject, &cond, &bound);
			addtest(sw, st, cond);
			if (!bound) {
				delscope(cs);
				break;
			}
			/* the names bound by the pattern are in scope in the block that follows */
			if (tok.kind != TLBRACE)
				error(&tok.loc, "'case' label that binds names must be followed by a block");
			compound(fc, cs, end);
			return 2;
		}
		if (tok.kind == TLBRACE)
			error(&tok.loc, "'case' label with a pattern must be in a switch on a struct or union");
		i = intconstexpr(s, true);
		if (consume(TELLIPSIS)) {
			/* inclusive range */
			j = intconstexpr(s, true);
			t = sw->u.switchstmt.cond->type;
			if (!eval(exprcompare(TLEQ, exprconst(t, i), exprconst(t, j)))->u.constant.u)
				error(&tok.loc, "'case' range is empty");
			for (k = i; j - i < 1024; ++k) {
				c = treeinsert(&sw->u.switchstmt.seen, k, sizeof(*c));
				if (!c->node.new)
					error(&tok.loc, "multiple 'case' labels with same value");
				if (k == j)
					break;
			}
			st = addstmt(end, STMTCASE);
			st->u.caselabel.switchstmt = sw;
			cond = exprcompare(TLAND,
				exprcompare(TGEQ, sw->u.switchstmt.temp, exprconst(t, i)),
				exprcompare(TLEQ, sw->u.switchstmt.temp, exprconst(t, j)));
			addtest(sw, st, cond);
			expect(TCOLON, "after case expression");
			break;
		}
		c = treeinsert(&sw->u.switchstmt.seen, i, sizeof(*c));
		if (!c->node.new)
			error(&tok.loc, "multiple 'case' labels with same value");
		st = addstmt(end, STMTCASE);
		c->stmt = st;
		st->u.caselabel.switchstmt = sw;
		st->u.caselabel.value = i;
		expect(TCOLON, "after case expression");
		break;
	case TDEFAULT:
		next();
		sw = s->switchstmt;
		if (!sw)
			error(&tok.loc, "'default' label must be in switch");
		if (s->defer != sw->defer)
			error(&tok.loc, "'default' label must not be in the scope of a defer statement in its switch");
		if (sw->u.switchstmt.hasdefault)
			error(&tok.loc, "multiple 'default' labels");
		expect(TCOLON, "after 'default'");
		sw->u.switchstmt.hasdefault = true;
		st = addstmt(end, STMTDEFAULT);
		st->u.caselabel.switchstmt = sw;
		break;
	default:
		if (tok.kind < TIDENT)
			return 0;
		name = tokenstr(tok.kind);
		if (!peek(TCOLON))
			return 0;
		mapkey(&key, name, strlen(name));
		if (!mapput(&fc->labels, &key, &idx))
			error(&tok.loc, "label '%s' redefined", name);
		st = addstmt(end, STMTLABEL);
		fc->labels.vals[idx].p = st;
		st->defer = s->defer;
		st->u.label.name = name;
		st->u.label.indefer = s->indefer;
		st->u.label.nextname = fc->names;
		fc->names = st;
		break;
	}
	return 1;
}

static void
labelstmt(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	int r;

	fc->names = NULL;
	while ((r = label(fc, s, end)) == 1)
		;
	if (r == 0)
		stmt(fc, s, end);
	fc->names = NULL;
}

/* parse a compound statement, with s as the scope of the block */
static void
compound(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	struct stmt *st, **body;

	next();
	st = addstmt(end, STMTCOMPOUND);
	st->defer = s->defer;
	body = &st->u.compound.body;
	while (tok.kind != TRBRACE) {
		if (!label(fc, s, &body) && !decl(s, fc, &body))
			stmt(fc, s, &body);
	}
	st->u.compound.enddefer = s->defer;
	delscope(s);
	next();
}

/*
Parse the body of a selection or iteration statement in the scope `s`
created for it. This is a block, so deferred blocks registered inside
it are executed when it finishes.
*/
static void
secondary(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	struct stmt *st, **body;

	st = addstmt(end, STMTCOMPOUND);
	st->defer = s->defer;
	body = &st->u.compound.body;
	labelstmt(fc, s, &body);
	st->u.compound.enddefer = s->defer;
}

/*
The enclosing loop or switch statement that is labeled `name`, which
`break name;` or `continue name;` targets (C2y). A jump may not leave a
deferred block, so the statements outside of it are not found.
*/
static struct stmt *
namedtarget(struct scope *s, const char *name, const char *keyword, bool loop)
{
	struct stmt *st, *l;

	for (st = s->breakstmt; st; st = st->outer) {
		for (l = st->names; l; l = l->u.label.nextname) {
			if (strcmp(l->u.label.name, name) != 0)
				continue;
			if (loop && st->kind == STMTSWITCH)
				error(&tok.loc, "'%s %s' must name a loop, but '%s' labels a switch statement", keyword, name, name);
			return st;
		}
	}
	if (s->indefer)
		error(&tok.loc, "'%s %s' must name an enclosing %s within the deferred block", keyword, name, loop ? "loop" : "loop or switch");
	error(&tok.loc, "'%s %s' must name an enclosing %s, but no enclosing %s is labeled '%s'", keyword, name, loop ? "loop" : "loop or switch", loop ? "loop" : "loop or switch statement", name);
	return NULL;
}

static struct stmt *
jumpstmt(struct scope *s, struct stmt ***end, enum stmtkind kind)
{
	struct stmt *st;

	st = addstmt(end, kind);
	st->defer = s->defer;
	st->u.jump.loc = tok.loc;
	st->u.jump.indefer = s->indefer;
	return st;
}

/* 6.8 Statements and blocks */
void
stmt(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	char *name;
	struct expr *e;
	struct type *t;
	struct stmt *st, **body, *names, *target;
	struct scope *ds;

	/* the labels of this statement */
	names = fc->names;
	fc->names = NULL;
	attr(NULL, 0);
	switch (tok.kind) {
	/* 6.8.2 Compound statement */
	case TLBRACE:
		if (peekbraces(TASSIGN))
			destructure(s, end);
		else
			compound(fc, mkscope(s), end);
		break;

	/* 6.8.3 Expression statement */
	case TSEMICOLON:
		next();
		break;
	default:
		e = expr(s);
		st = addstmt(end, STMTEXPR);
		st->u.expr = e;
		expect(TSEMICOLON, "after expression statement");
		break;

	/* 6.8.4 Selection statement */
	case TIF:
		next();
		s = mkscope(s);
		expect(TLPAREN, "after 'if'");
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of if statement must have scalar type");
		expect(TRPAREN, "after expression");
		st = addstmt(end, STMTIF);
		st->u.ifstmt.cond = e;

		body = &st->u.ifstmt.then;
		s = mkscope(s);
		secondary(fc, s, &body);
		s = delscope(s);

		if (consume(TELSE)) {
			st->u.ifstmt.haselse = true;
			body = &st->u.ifstmt.els;
			s = mkscope(s);
			secondary(fc, s, &body);
			s = delscope(s);
		}
		s = delscope(s);
		break;
	case TSWITCH:
		next();

		s = mkscope(s);
		expect(TLPAREN, "after 'switch'");
		e = expr(s);
		expect(TRPAREN, "after expression");

		if (e->type->kind == TYPESTRUCT || e->type->kind == TYPEUNION) {
			/* the cases are patterns, matched against a copy of the value */
			e = patternobject(e, end);
			st = addstmt(end, STMTSWITCH);
			st->defer = s->defer;
			st->u.switchstmt.subject = e;
		} else {
			if (!(e->type->prop & PROPINT))
				error(&tok.loc, "controlling expression of switch statement must have integer, struct, or union type");
			e = exprpromote(e);

			st = addstmt(end, STMTSWITCH);
			st->defer = s->defer;
			st->u.switchstmt.cond = e;
			st->u.switchstmt.temp = exprtemp(e->type);
		}
		st->names = names;
		st->outer = s->breakstmt;
		body = &st->u.switchstmt.body;
		s = mkscope(s);
		s->breakstmt = st;
		s->switchstmt = st;
		secondary(fc, s, &body);
		s = delscope(s);
		s = delscope(s);
		break;

	/* 6.8.5 Iteration statements */
	case TWHILE:
		next();
		s = mkscope(s);
		expect(TLPAREN, "after 'while'");
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of loop must have scalar type");
		expect(TRPAREN, "after expression");

		st = addstmt(end, STMTWHILE);
		st->defer = s->defer;
		st->names = names;
		st->outer = s->breakstmt;
		st->u.loop.cond = e;
		body = &st->u.loop.body;
		s = mkscope(s);
		s->continuestmt = st;
		s->breakstmt = st;
		secondary(fc, s, &body);
		s = delscope(s);
		s = delscope(s);
		break;
	case TDO:
		next();

		st = addstmt(end, STMTDO);
		st->defer = s->defer;
		st->names = names;
		st->outer = s->breakstmt;
		body = &st->u.loop.body;
		s = mkscope(s);
		s = mkscope(s);
		s->continuestmt = st;
		s->breakstmt = st;
		secondary(fc, s, &body);
		s = delscope(s);

		expect(TWHILE, "after 'do' statement");
		expect(TLPAREN, "after 'while'");
		e = expr(s);
		t = e->type;
		if (!(t->prop & PROPSCALAR))
			error(&tok.loc, "controlling expression of loop must have scalar type");
		expect(TRPAREN, "after expression");
		st->u.loop.cond = e;

		s = delscope(s);
		expect(TSEMICOLON, "after 'do' statement");
		break;
	case TFOR:
		next();
		expect(TLPAREN, "after 'for'");
		s = mkscope(s);
		st = addstmt(end, STMTFOR);
		st->defer = s->defer;
		st->names = names;
		st->outer = s->breakstmt;
		body = &st->u.loop.init;
		if (!decl(s, fc, &body)) {
			if (tok.kind != TSEMICOLON)
				addstmt(&body, STMTEXPR)->u.expr = expr(s);
			expect(TSEMICOLON, NULL);
		}

		if (tok.kind != TSEMICOLON) {
			e = expr(s);
			t = e->type;
			if (!(t->prop & PROPSCALAR))
				error(&tok.loc, "controlling expression of loop must have scalar type");
			st->u.loop.cond = e;
		}
		expect(TSEMICOLON, NULL);
		st->u.loop.post = tok.kind == TRPAREN ? NULL : expr(s);
		expect(TRPAREN, NULL);

		body = &st->u.loop.body;
		s = mkscope(s);
		s->breakstmt = st;
		s->continuestmt = st;
		secondary(fc, s, &body);
		s = delscope(s);
		s = delscope(s);
		break;

	/* 6.8.6 Jump statements */
	case TGOTO:
		next();
		st = jumpstmt(s, end, STMTGOTO);
		name = expect(TIDENT, "after 'goto'");
		st->u.jump.name = name;
		st->u.jump.nextgoto = fc->gotos;
		fc->gotos = st;
		expect(TSEMICOLON, "after 'goto' statement");
		break;
	case TCONTINUE:
		next();
		if (tok.kind >= TIDENT) {
			/* continue with the loop that has this label */
			target = namedtarget(s, tokenstr(tok.kind), "continue", true);
			next();
		} else {
			if (!s->continuestmt)
				error(&tok.loc, s->indefer ? "'continue' statement must not exit a deferred block" : "'continue' statement must be in loop");
			target = s->continuestmt;
		}
		st = jumpstmt(s, end, STMTCONTINUE);
		st->u.jump.target = target;
		expect(TSEMICOLON, "after 'continue' statement");
		break;
	case TBREAK:
		next();
		if (tok.kind >= TIDENT) {
			/* leave the loop or switch that has this label */
			target = namedtarget(s, tokenstr(tok.kind), "break", false);
			next();
		} else {
			if (!s->breakstmt)
				error(&tok.loc, s->indefer ? "'break' statement must not exit a deferred block" : "'break' statement must be in loop or switch");
			target = s->breakstmt;
		}
		st = jumpstmt(s, end, STMTBREAK);
		st->u.jump.target = target;
		expect(TSEMICOLON, "after 'break' statement");
		break;
	case TRETURN:
		next();
		if (s->indefer)
			error(&tok.loc, "'return' statement must not be in a deferred block");
		t = fc->type;
		st = addstmt(end, STMTRETURN);
		st->defer = s->defer;
		if (t->base != &typevoid) {
			/* the value may be an initializer list for the return type */
			if (tok.kind == TLBRACE) {
				e = exprcompound(s, t->base);
			} else {
				exprexpect(t->base);
				e = expr(s);
			}
			st->u.expr = exprassign(e, t->base);
		}
		expect(TSEMICOLON, "after 'return' statement");
		break;

	/* TS 25755 Defer statement */
	case T_DEFER:
		next();
		st = addstmt(end, STMTDEFER);
		st->u.defer.prev = s->defer;

		/* jumps out of the deferred block are not allowed */
		ds = mkscope(s);
		ds->breakstmt = NULL;
		ds->continuestmt = NULL;
		ds->switchstmt = NULL;
		ds->defer = NULL;
		ds->indefer = st;
		body = &st->u.defer.body;
		stmt(fc, ds, &body);
		delscope(ds);

		/* in effect for the rest of the enclosing block */
		s->defer = st;
		break;

	case T__ASM__:
		error(&tok.loc, "inline assembly is not yet supported");
	}
}

static void
resolvegoto(struct funcctx *fc, struct stmt *st)
{
	struct stmt *l, *d;
	struct mapkey key;
	char *name;

	name = st->u.jump.name;
	mapkey(&key, name, strlen(name));
	l = mapget(&fc->labels, &key, NULL);
	if (!l)
		error(&st->u.jump.loc, "label '%s' is not defined", name);
	if (l->u.label.indefer != st->u.jump.indefer)
		error(&st->u.jump.loc, "'goto' must not jump into or out of a deferred block");
	/* the deferred blocks in effect at the label must also be in effect at the goto */
	for (d = st->defer; d != l->defer; d = d->u.defer.prev) {
		if (!d)
			error(&st->u.jump.loc, "'goto' must not jump into the scope of a defer statement");
	}
	st->u.jump.target = l;
}

/* parse a function body, starting at its compound statement */
struct stmt *
funcbody(struct funcctx *fc, struct scope *s)
{
	struct stmt *body, **end, *st;

	mapinit(&fc->labels, 8);
	fc->gotos = NULL;
	fc->names = NULL;
	body = NULL;
	end = &body;
	stmt(fc, s, &end);
	for (st = fc->gotos; st; st = st->u.jump.nextgoto)
		resolvegoto(fc, st);
	mapfree(&fc->labels, NULL);

	return body;
}

static void
delstmts(struct stmt *st)
{
	struct stmt *next;

	for (; st; st = next) {
		next = st->next;
		delstmt(st);
	}
}

void
delstmt(struct stmt *st)
{
	switch (st->kind) {
	case STMTCOMPOUND:
		delstmts(st->u.compound.body);
		break;
	case STMTEXPR:
		delexpr(st->u.expr);
		break;
	case STMTIF:
		delexpr(st->u.ifstmt.cond);
		delstmts(st->u.ifstmt.then);
		delstmts(st->u.ifstmt.els);
		break;
	case STMTSWITCH:
		delstmts(st->u.switchstmt.body);
		break;
	case STMTWHILE:
	case STMTDO:
	case STMTFOR:
		delstmts(st->u.loop.init);
		if (st->kind == STMTFOR && st->u.loop.cond)
			delexpr(st->u.loop.cond);
		if (st->u.loop.post)
			delexpr(st->u.loop.post);
		delstmts(st->u.loop.body);
		break;
	case STMTRETURN:
		if (st->u.expr)
			delexpr(st->u.expr);
		break;
	case STMTDEFER:
		delstmts(st->u.defer.body);
		break;
	}
	free(st);
}
