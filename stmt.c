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
	unsigned long long i;

	attr(NULL, 0);
	switch (tok.kind) {
	case TCASE:
		next();
		sw = s->switchstmt;
		if (!sw)
			error(&tok.loc, "'case' label must be in switch");
		i = intconstexpr(s, true);
		c = treeinsert(&sw->u.switchstmt.seen, i, sizeof(*c));
		if (!c->node.new)
			error(&tok.loc, "multiple 'case' labels with same value");
		st = addstmt(end, STMTCASE);
		c->stmt = st;
		st->u.label.switchstmt = sw;
		st->u.label.value = i;
		expect(TCOLON, "after case expression");
		break;
	case TDEFAULT:
		next();
		sw = s->switchstmt;
		if (!sw)
			error(&tok.loc, "'default' label must be in switch");
		if (sw->u.switchstmt.hasdefault)
			error(&tok.loc, "multiple 'default' labels");
		expect(TCOLON, "after 'default'");
		sw->u.switchstmt.hasdefault = true;
		st = addstmt(end, STMTDEFAULT);
		st->u.label.switchstmt = sw;
		break;
	default:
		if (tok.kind < TIDENT)
			return false;
		name = tokenstr(tok.kind);
		if (!peek(TCOLON))
			return false;
		st = addstmt(end, STMTLABEL);
		st->u.name = name;
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

/* 6.8 Statements and blocks */
void
stmt(struct funcctx *fc, struct scope *s, struct stmt ***end)
{
	char *name;
	struct expr *e;
	struct type *t;
	struct stmt *st, **body;

	attr(NULL, 0);
	switch (tok.kind) {
	/* 6.8.2 Compound statement */
	case TLBRACE:
		next();
		st = addstmt(end, STMTCOMPOUND);
		body = &st->u.compound;
		s = mkscope(s);
		while (tok.kind != TRBRACE) {
			if (!label(fc, s, &body) && !decl(s, fc, &body))
				stmt(fc, s, &body);
		}
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
		labelstmt(fc, s, &body);
		s = delscope(s);

		if (consume(TELSE)) {
			st->u.ifstmt.haselse = true;
			body = &st->u.ifstmt.els;
			s = mkscope(s);
			labelstmt(fc, s, &body);
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
		st->u.switchstmt.cond = e;
		body = &st->u.switchstmt.body;
		s = mkscope(s);
		s->breakstmt = st;
		s->switchstmt = st;
		labelstmt(fc, s, &body);
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
		st->u.loop.cond = e;
		body = &st->u.loop.body;
		s = mkscope(s);
		s->continuestmt = st;
		s->breakstmt = st;
		labelstmt(fc, s, &body);
		s = delscope(s);
		s = delscope(s);
		break;
	case TDO:
		next();

		st = addstmt(end, STMTDO);
		body = &st->u.loop.body;
		s = mkscope(s);
		s = mkscope(s);
		s->continuestmt = st;
		s->breakstmt = st;
		labelstmt(fc, s, &body);
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
		labelstmt(fc, s, &body);
		s = delscope(s);
		s = delscope(s);
		break;

	/* 6.8.6 Jump statements */
	case TGOTO:
		next();
		name = expect(TIDENT, "after 'goto'");
		st = addstmt(end, STMTGOTO);
		st->u.name = name;
		expect(TSEMICOLON, "after 'goto' statement");
		break;
	case TCONTINUE:
		next();
		if (!s->continuestmt)
			error(&tok.loc, "'continue' statement must be in loop");
		st = addstmt(end, STMTCONTINUE);
		st->u.target = s->continuestmt;
		expect(TSEMICOLON, "after 'continue' statement");
		break;
	case TBREAK:
		next();
		if (!s->breakstmt)
			error(&tok.loc, "'break' statement must be in loop or switch");
		st = addstmt(end, STMTBREAK);
		st->u.target = s->breakstmt;
		expect(TSEMICOLON, "after 'break' statement");
		break;
	case TRETURN:
		next();
		t = fc->type;
		st = addstmt(end, STMTRETURN);
		if (t->base != &typevoid)
			st->u.expr = exprassign(expr(s), t->base);
		expect(TSEMICOLON, "after 'return' statement");
		break;

	case T__ASM__:
		error(&tok.loc, "inline assembly is not yet supported");
	}
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
		delstmts(st->u.compound);
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
	}
	free(st);
}
