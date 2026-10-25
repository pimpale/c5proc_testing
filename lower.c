#include <stdbool.h>
#include <stddef.h>
#include "util.h"
#include "cc.h"

/*
Generate code for a function body. Blocks are created in the same order
as when statements were emitted during parsing, so that the output is
unchanged.
*/

static void lowerstmt(struct func *, struct stmt *);

static void
lowerstmts(struct func *f, struct stmt *st)
{
	for (; st; st = st->next)
		lowerstmt(f, st);
}

/*
Deferred blocks are lowered once for each way of leaving their scope.
Each lowering of a deferred block gets a new epoch, so that labels
inside it get new blocks.
*/
static unsigned epoch, nextepoch;

static struct block *
labelblock(struct stmt *st)
{
	if (!st->u.label.block || st->u.label.epoch != epoch) {
		st->u.label.block = mkblock(st->u.label.name);
		st->u.label.epoch = epoch;
	}
	return st->u.label.block;
}

static void
clearvla(struct type *t)
{
	for (; t && t->prop & PROPVM; t = t->base) {
		if (t->kind == TYPEARRAY && !t->size)
			t->u.array.size = NULL;
	}
}

/*
Forget the sizes of variable length arrays declared in a deferred
block, so that they are computed again in its next lowering.
*/
static void
clearvlas(struct stmt *st)
{
	for (; st; st = st->next) {
		switch (st->kind) {
		case STMTCOMPOUND:
			clearvlas(st->u.compound.body);
			break;
		case STMTDECL:
			if (st->u.decl.decl)
				clearvla(st->u.decl.decl->type);
			break;
		case STMTIF:
			clearvlas(st->u.ifstmt.then);
			clearvlas(st->u.ifstmt.els);
			break;
		case STMTSWITCH:
			clearvlas(st->u.switchstmt.body);
			break;
		case STMTWHILE:
		case STMTDO:
		case STMTFOR:
			clearvlas(st->u.loop.init);
			clearvlas(st->u.loop.body);
			break;
		case STMTDEFER:
			clearvlas(st->u.defer.body);
			break;
		}
	}
}

/* execute the deferred blocks in effect at `from` but not at `to` */
static void
rundefers(struct func *f, struct stmt *from, struct stmt *to)
{
	struct stmt *d;
	unsigned oldepoch;

	for (d = from; d != to; d = d->u.defer.prev) {
		oldepoch = epoch;
		epoch = ++nextepoch;
		lowerstmts(f, d->u.defer.body);
		epoch = oldepoch;
		clearvlas(d->u.defer.body);
	}
}

static void
lowerstmt(struct func *f, struct stmt *st)
{
	struct switchcases *cases;
	struct value *v;
	struct block *b[4];

	switch (st->kind) {
	case STMTCOMPOUND:
		lowerstmts(f, st->u.compound.body);
		rundefers(f, st->u.compound.enddefer, st->defer);
		break;
	case STMTEXPR:
		funcexpr(f, st->u.expr);
		break;
	case STMTDECL:
		if (st->u.decl.vm)
			funcexpr(f, st->u.decl.vm);
		if (st->u.decl.decl)
			funcinit(f, st->u.decl.decl, st->u.decl.init, st->u.decl.hasinit);
		break;
	case STMTIF:
		b[0] = mkblock("if_true");
		b[1] = mkblock("if_false");
		funcbranch(f, st->u.ifstmt.cond, b[0], b[1]);

		funclabel(f, b[0]);
		lowerstmts(f, st->u.ifstmt.then);

		if (st->u.ifstmt.haselse) {
			b[2] = mkblock("if_join");
			funcjmp(f, b[2]);
			funclabel(f, b[1]);
			lowerstmts(f, st->u.ifstmt.els);
			funclabel(f, b[2]);
		} else {
			funclabel(f, b[1]);
		}
		break;
	case STMTSWITCH:
		cases = &st->u.switchstmt.cases;
		cases->root = NULL;
		cases->type = st->u.switchstmt.cond->type;
		cases->defaultlabel = NULL;

		b[0] = mkblock("switch_cond");
		b[1] = mkblock("switch_join");

		v = funcexpr(f, st->u.switchstmt.cond);
		funcjmp(f, b[0]);
		st->breaklabel = b[1];
		lowerstmts(f, st->u.switchstmt.body);
		funcjmp(f, b[1]);

		funclabel(f, b[0]);
		funcswitch(f, v, cases, cases->defaultlabel ? cases->defaultlabel : b[1]);

		funclabel(f, b[1]);
		break;
	case STMTCASE:
		b[0] = mkblock("switch_case");
		funclabel(f, b[0]);
		switchcase(&st->u.caselabel.switchstmt->u.switchstmt.cases, st->u.caselabel.value, b[0]);
		break;
	case STMTDEFAULT:
		cases = &st->u.caselabel.switchstmt->u.switchstmt.cases;
		cases->defaultlabel = mkblock("switch_default");
		funclabel(f, cases->defaultlabel);
		break;
	case STMTWHILE:
		b[0] = mkblock("while_cond");
		b[1] = mkblock("while_body");
		b[2] = mkblock("while_join");

		funclabel(f, b[0]);
		funcbranch(f, st->u.loop.cond, b[1], b[2]);
		funclabel(f, b[1]);
		st->continuelabel = b[0];
		st->breaklabel = b[2];
		lowerstmts(f, st->u.loop.body);
		funcjmp(f, b[0]);
		funclabel(f, b[2]);
		break;
	case STMTDO:
		b[0] = mkblock("do_body");
		b[1] = mkblock("do_cond");
		b[2] = mkblock("do_join");

		st->continuelabel = b[1];
		st->breaklabel = b[2];
		funclabel(f, b[0]);
		lowerstmts(f, st->u.loop.body);

		funclabel(f, b[1]);
		funcbranch(f, st->u.loop.cond, b[0], b[2]);
		funclabel(f, b[2]);
		break;
	case STMTFOR:
		lowerstmts(f, st->u.loop.init);

		b[0] = mkblock("for_cond");
		b[1] = mkblock("for_body");
		b[2] = mkblock("for_cont");
		b[3] = mkblock("for_join");

		funclabel(f, b[0]);
		if (st->u.loop.cond)
			funcbranch(f, st->u.loop.cond, b[1], b[3]);

		funclabel(f, b[1]);
		st->breaklabel = b[3];
		st->continuelabel = b[2];
		lowerstmts(f, st->u.loop.body);

		funclabel(f, b[2]);
		if (st->u.loop.post)
			funcexpr(f, st->u.loop.post);
		funcjmp(f, b[0]);
		funclabel(f, b[3]);
		break;
	case STMTLABEL:
		funclabel(f, labelblock(st));
		break;
	case STMTGOTO:
		rundefers(f, st->defer, st->u.jump.target->defer);
		funcjmp(f, labelblock(st->u.jump.target));
		break;
	case STMTCONTINUE:
		rundefers(f, st->defer, st->u.jump.target->defer);
		funcjmp(f, st->u.jump.target->continuelabel);
		break;
	case STMTBREAK:
		rundefers(f, st->defer, st->u.jump.target->defer);
		funcjmp(f, st->u.jump.target->breaklabel);
		break;
	case STMTRETURN:
		v = st->u.expr ? funcexpr(f, st->u.expr) : NULL;
		if (st->defer) {
			/* the return value is computed before deferred blocks are executed */
			if (v)
				v = funcsave(f, st->u.expr->type, v);
			rundefers(f, st->defer, NULL);
		}
		funcret(f, v);
		break;
	case STMTDEFER:
		/* executed when its scope is exited */
		break;
	}
}

void
lower(struct func *f, struct stmt *body)
{
	lowerstmts(f, body);
}
