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

static void
lowerstmt(struct func *f, struct stmt *st)
{
	struct gotolabel *g;
	struct switchcases *cases;
	struct value *v;
	struct block *b[4];

	switch (st->kind) {
	case STMTCOMPOUND:
		lowerstmts(f, st->u.compound);
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
		switchcase(&st->u.label.switchstmt->u.switchstmt.cases, st->u.label.value, b[0]);
		break;
	case STMTDEFAULT:
		cases = &st->u.label.switchstmt->u.switchstmt.cases;
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
		g = funcgoto(f, st->u.name);
		g->defined = true;
		funclabel(f, g->label);
		break;
	case STMTGOTO:
		funcjmp(f, funcgoto(f, st->u.name)->label);
		break;
	case STMTCONTINUE:
		funcjmp(f, st->u.target->continuelabel);
		break;
	case STMTBREAK:
		funcjmp(f, st->u.target->breaklabel);
		break;
	case STMTRETURN:
		v = st->u.expr ? funcexpr(f, st->u.expr) : NULL;
		funcret(f, v);
		break;
	}
}

void
lower(struct func *f, struct stmt *body)
{
	lowerstmts(f, body);
}
