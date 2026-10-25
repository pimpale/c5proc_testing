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

/* 6.8.1 Labeled statements */
static bool
label(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	char *name;
	struct stmt *st, *sw;
	struct caselabel *c;
	struct mapkey key;
	size_t idx;
	unsigned long long i;

	attr(NULL, 0);
	switch (tok.kind) {
	case TCASE:
		next();
		sw = s->switchstmt;
		if (!sw)
			error(&tok.loc, "'case' label must be in switch");
		if (s->defer != sw->defer)
			error(&tok.loc, "'case' label must not be in the scope of a defer statement in its switch");
		i = intconstexpr(s, true);
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
			return false;
		name = tokenstr(tok.kind);
		if (!peek(TCOLON))
			return false;
		mapkey(&key, name, strlen(name));
		if (!mapput(&fc->labels, &key, &idx))
			error(&tok.loc, "label '%s' redefined", name);
		st = addstmt(end, STMTLABEL);
		fc->labels.vals[idx].p = st;
		st->defer = s->defer;
		st->u.label.name = name;
		st->u.label.indefer = s->indefer;
		break;
	}
	return true;
}

static void
labelstmt(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	while (label(fc, s, end))
		;
	stmt(fc, s, end);
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
	struct stmt *st, **body;
	struct scope *ds;

	attr(NULL, 0);
	switch (tok.kind) {
	/* 6.8.2 Compound statement */
	case TLBRACE:
		next();
		st = addstmt(end, STMTCOMPOUND);
		st->defer = s->defer;
		body = &st->u.compound.body;
		s = mkscope(s);
		while (tok.kind != TRBRACE) {
			if (!label(fc, s, &body) && !decl(s, fc, &body))
				stmt(fc, s, &body);
		}
		st->u.compound.enddefer = s->defer;
		s = delscope(s);
		next();
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

		if (!(e->type->prop & PROPINT))
			error(&tok.loc, "controlling expression of switch statement must have integer type");
		e = exprpromote(e);

		st = addstmt(end, STMTSWITCH);
		st->defer = s->defer;
		st->u.switchstmt.cond = e;
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
		if (!s->continuestmt)
			error(&tok.loc, s->indefer ? "'continue' statement must not exit a deferred block" : "'continue' statement must be in loop");
		st = jumpstmt(s, end, STMTCONTINUE);
		st->u.jump.target = s->continuestmt;
		expect(TSEMICOLON, "after 'continue' statement");
		break;
	case TBREAK:
		next();
		if (!s->breakstmt)
			error(&tok.loc, s->indefer ? "'break' statement must not exit a deferred block" : "'break' statement must be in loop or switch");
		st = jumpstmt(s, end, STMTBREAK);
		st->u.jump.target = s->breakstmt;
		expect(TSEMICOLON, "after 'break' statement");
		break;
	case TRETURN:
		next();
		if (s->indefer)
			error(&tok.loc, "'return' statement must not be in a deferred block");
		t = fc->type;
		st = addstmt(end, STMTRETURN);
		st->defer = s->defer;
		if (t->base != &typevoid)
			st->u.expr = exprassign(expr(s), t->base);
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
