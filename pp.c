#include <assert.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include "util.h"
#include "cc.h"

struct macroparam {
	char *name;
	enum {
		PARAMTOK = 1<<0,  /* the macro-expanded argument is used */
		PARAMVAR = 1<<1,  /* the parameter is variadic */
	} flags;
};

struct macroarg {
	/* argument tokens as written */
	struct token *raw;
	size_t nraw;
	/* argument tokens after macro expansion (if PARAMTOK) */
	struct token *token;
	size_t ntoken;
	/* whether the variadic arguments were left out entirely */
	bool omitted;
};

struct macro {
	enum {
		MACROOBJ,
		MACROFUNC,
	} kind;
	char *name;
	/* whether or not this macro is ineligible for expansion */
	bool hide;
	/* parameters of function-like macro */
	struct macroparam *param;
	size_t nparam;
	/* replacement list */
	struct token *token;
	size_t ntoken;
	/* tokens of the expansion in progress */
	struct token *exp;
};

struct frame {
	struct token *token;
	size_t ntoken;
	struct macro *macro;
};

enum ppflags ppflags;

static struct array ctx;
static struct array macros;

void
ppinit(void)
{
	next();
}

static void
macrodel(struct macro *m)
{
	free(m->param);
	free(m->token);
	free(m);
}

/* find the index of a macro parameter with the given name */
static size_t
macroparam(struct macro *m, struct token *t)
{
	size_t i;

	if (t->kind >= TPPIDENT) {
		for (i = 0; i < m->nparam; ++i) {
			if (strcmp(m->param[i].name, tokenstr(t->kind)) == 0)
				return i;
		}
	}
	return -1;
}

/* lookup a macro by name */
static struct macro *
macroget(enum tokenkind ident)
{
	return arraygetptr(&macros, ident - TPPIDENT);
}

static void
macrodone(struct macro *m)
{
	m->hide = false;
	free(m->exp);
	m->exp = NULL;
}

static bool
macrovarargs(struct macro *m)
{
	return m->kind == MACROFUNC && m->nparam > 0 && m->param[m->nparam - 1].flags & PARAMVAR;
}

/*
Whether a token of a replacement list is the variadic parameter in
', ## __VA_ARGS__'. As a GNU extension, this removes the comma when
the variadic arguments are left out, and pastes nothing otherwise.
*/
static bool
commapaste(struct macro *m, struct token *t)
{
	size_t i;

	if (t - m->token < 2 || t[-1].kind != THASHHASH || t[-2].kind != TCOMMA)
		return false;
	i = macroparam(m, t);
	return i != -1 && m->param[i].flags & PARAMVAR;
}

static struct token *
framenext(struct frame *f)
{
	return f->ntoken--, f->token++;
}

/* push a new context frame */
static struct frame *
ctxpush(struct token *t, size_t n, struct macro *m, bool space)
{
	struct frame *f;

	f = arrayadd(&ctx, sizeof(*f));
	f->token = t;
	f->ntoken = n;
	f->macro = m;
	if (n > 0)
		t[0].space = space;
	return f;
}

/* get the next token from the context */
static struct token *
ctxnext(void)
{
	struct frame *f;

	for (f = arraylast(&ctx, sizeof(*f)); ctx.len; --f, ctx.len -= sizeof(*f)) {
		if (f->ntoken)
			return framenext(f);
		if (f->macro)
			macrodone(f->macro);
	}
	return NULL;
}

static void
define(void)
{
	struct token *t, *end, *close;
	enum tokenkind ident;
	struct macro *m, *other;
	struct macroparam *p;
	struct array params = {0}, repl = {0};
	size_t i, depth;

	m = xmalloc(sizeof(*m));
	ident = tok.kind;
	m->name = tokencheck(&tok, TPPIDENT, "after #define");
	m->hide = false;
	m->exp = NULL;
	t = arrayadd(&repl, sizeof(*t));
	scan(t);
	if (t->kind == TLPAREN && !t->space) {
		m->kind = MACROFUNC;
		/* read macro parameter names */
		p = NULL;
		scan(&tok);
		while (tok.kind != TRPAREN) {
			if (p) {
				if (p->flags & PARAMVAR)
					tokencheck(&tok, TRPAREN, "after '...'");
				tokencheck(&tok, TCOMMA, "or ')' after macro parameter");
				scan(&tok);
			}
			p = arrayadd(&params, sizeof(*p));
			p->flags = 0;
			if (tok.kind == TELLIPSIS) {
				p->name = "__VA_ARGS__";
				p->flags |= PARAMVAR;
				scan(&tok);
			} else {
				p->name = tokencheck(&tok, TPPIDENT, "of macro parameter name or '...'");
				scan(&tok);
				/* GNU extension: named variadic parameter */
				if (tok.kind == TELLIPSIS) {
					p->flags |= PARAMVAR;
					scan(&tok);
				}
			}
		}
		scan(t);  /* first token in replacement list */
	} else {
		m->kind = MACROOBJ;
	}
	m->param = params.val;
	m->nparam = params.len / sizeof(m->param[0]);

	/* read macro body */
	while (t->kind != TNEWLINE && t->kind != TEOF) {
		t = arrayadd(&repl, sizeof(*t));
		scan(t);
	}
	tok = *t;
	m->token = repl.val;
	m->ntoken = repl.len / sizeof(*t) - 1;

	/* check the operators, and find out how each parameter is used */
	for (t = m->token, end = t + m->ntoken; t < end; ++t) {
		switch (t->kind) {
		case THASHHASH:
			if (t == m->token || t + 1 == end)
				error(&t->loc, "'##' operator cannot be at the start or end of a macro body");
			continue;
		case THASH:
			if (m->kind != MACROFUNC)
				continue;
			++t;
			tokencheck(t, TPPIDENT, "after '#' operator");
			if (macroparam(m, t) == -1)
				error(&t->loc, "'%s' is not a macro parameter name", tokenstr(t->kind));
			continue;
		case T__VA_OPT__:
			if (!macrovarargs(m))
				error(&t->loc, "__VA_OPT__ can only be used in variadic function-like macros");
			close = NULL;
			if (t + 1 < end && t[1].kind == TLPAREN) {
				for (depth = 0, close = t + 1; close < end; ++close) {
					if (close->kind == TLPAREN)
						++depth;
					else if (close->kind == TRPAREN && --depth == 0)
						break;
				}
			}
			if (!close || close == end)
				error(&t->loc, "__VA_OPT__ must be followed by a parenthesized list of tokens");
			/* whether there are variadic arguments is decided after expansion */
			m->param[m->nparam - 1].flags |= PARAMTOK;
			continue;
		}
		i = macroparam(m, t);
		if (i == -1) {
			if (t->kind == T__VA_ARGS__)
				error(&t->loc, "__VA_ARGS__ can only be used in variadic function-like macros");
			continue;
		}
		/* operands of '##' are not expanded */
		if (t > m->token && t[-1].kind == THASHHASH ? commapaste(m, t) : t + 1 == end || t[1].kind != THASHHASH)
			m->param[i].flags |= PARAMTOK;
	}

	i = ident - TPPIDENT;
	/*
	An incompatible redefinition is not an error here. The external
	preprocessor, which sees the same definitions, already diagnoses
	it, and allows it in system headers (glibc's stdbit.h redefines
	__STDC_ENDIAN_LITTLE__, for instance).
	*/
	other = arraysetptr(&macros, i, m);
	if (other)
		macrodel(other);
}

static void
undef(void)
{
	enum tokenkind ident;
	struct macro *m;

	ident = tok.kind;
	tokencheck(&tok, TPPIDENT, "after #undef");
	m = macroget(ident);
	if (m) {
		macrodel(m);
		((void **)macros.val)[ident - TPPIDENT] = NULL;
	}
	scan(&tok);
}

static void
directive(void)
{
	struct location newloc;
	enum ppflags oldflags;
	enum tokenkind kind;

	scan(&tok);
	if (tok.kind == TNEWLINE)
		return;  /* empty directive */
	oldflags = ppflags;
	ppflags |= PPNEWLINE;
	kind = tok.kind;
	switch (kind) {
	case TNUMBER:
		goto line;  /* gcc line markers */
	case TIF:
		error(&tok.loc, "#if directive is not implemented");
		break;
	case TIFDEF:
		error(&tok.loc, "#ifdef directive is not implemented");
		break;
	case TIFNDEF:
		error(&tok.loc, "#ifndef directive is not implemented");
		break;
	case TELIF:
		error(&tok.loc, "#elif directive is not implemented");
		break;
	case TENDIF:
		error(&tok.loc, "#endif directive is not implemented");
		break;
	case TINCLUDE:
		error(&tok.loc, "#include directive is not implemented");
		break;
	case TDEFINE:
		scan(&tok);
		define();
		break;
	case TUNDEF:
		scan(&tok);
		undef();
		break;
	case TLINE:
		scan(&tok);
		tokencheck(&tok, TNUMBER, "after #line");
	line:
		newloc.line = strtoull(tok.lit, NULL, 0);
		newloc.col = 1;
		scan(&tok);
		newloc.file = tok.loc.file;
		if (tok.kind == TSTRINGLIT) {
			char *quote;

			/* XXX: handle escape sequences (reuse string decoding from expr.c) */
			quote = strchr(tok.lit, '"');
			assert(quote);
			newloc.file = quote + 1;
			quote = strchr(quote + 1, '"');
			assert(quote);
			*quote = '\0';
			scan(&tok);
		}
		while (tok.kind == TNUMBER)
			scan(&tok);
		scansetloc(newloc);
		break;
	case TERROR:
	case TWARNING:
		diagloc(&tok.loc);
		fprintf(stderr, "%s directive:", kind == TERROR ? "#error" : "#warning");
		scan(&tok);
		while (tok.kind != TNEWLINE && tok.kind != TEOF) {
			tokenprint(&tok, stderr);
			scan(&tok);
		}
		fputc('\n', stderr);
		if (kind == TERROR)
			exit(1);
		break;
	case TPRAGMA:
		while (tok.kind != TNEWLINE && tok.kind != TEOF)
			next();
		break;
	default:
		error(&tok.loc, "invalid preprocessor directive #%s", tokenstr(tok.kind));
	}
	tokencheck(&tok, TNEWLINE, "after preprocessing directive");
	ppflags = oldflags;
}

/* get the next token without expanding it */
static void
nextinto(struct token *t)
{
	static bool newline = true;

	for (;;) {
		scan(t);
		if (newline && t->kind == THASH) {
			directive();
		} else {
			newline = t->kind == TNEWLINE;
			break;
		}
	}
}

static struct token *
rawnext(void)
{
	struct token *t;

	t = ctxnext();
	if (!t) {
		t = &tok;
		nextinto(t);
	}
	return t;
}

static bool
peekparen(void)
{
	static struct array pending;
	struct token *t;
	struct frame *f;

	t = ctxnext();
	if (t) {
		if (t->kind == TLPAREN)
			return true;
		f = arraylast(&ctx, sizeof(*f));
		--f->token;
		++f->ntoken;
		return false;
	}
	pending.len = 0;
	do t = arrayadd(&pending, sizeof(*t)), nextinto(t);
	while (t->kind == TNEWLINE);
	if (t->kind == TLPAREN)
		return true;
	t = pending.val;
	ctxpush(t, pending.len / sizeof(*t), NULL, t[0].space);
	return false;
}

static char *
tokenspell(struct token *t)
{
	return t->lit ? t->lit : tokenstr(t->kind);
}

/* the result of the '#' operator on a macro argument */
static struct token
stringize(struct macroarg *arg)
{
	struct array buf = {0};
	struct token *t;
	const char *lit;

	arrayaddbuf(&buf, "\"", 1);
	for (t = arg->raw; t < arg->raw + arg->nraw; ++t) {
		if (t->space && buf.len > 1)
			arrayaddbuf(&buf, " ", 1);
		lit = tokenspell(t);
		if (t->kind == TSTRINGLIT || t->kind == TCHARCONST) {
			for (; *lit; ++lit) {
				if (*lit == '\\' || *lit == '"')
					arrayaddbuf(&buf, "\\", 1);
				arrayaddbuf(&buf, lit, 1);
			}
		} else if (lit) {
			arrayaddbuf(&buf, lit, strlen(lit));
		}
	}
	arrayaddbuf(&buf, "\"", 2);
	return (struct token){.kind = TSTRINGLIT, .lit = buf.val};
}

/* replace l with the result of the '##' operator op on l and r */
static void
paste(struct token *l, struct token *r, struct token *op)
{
	const char *ls, *rs;
	struct token t;
	char *buf;

	ls = tokenspell(l);
	rs = tokenspell(r);
	buf = xmalloc(strlen(ls) + strlen(rs) + 1);
	strcpy(buf, ls);
	strcat(buf, rs);
	t.loc = l->loc;
	if (!scanstring(buf, &t))
		error(&l->loc, "pasting '%s' and '%s' does not give a valid preprocessing token", ls, rs);
	free(buf);
	t.space = l->space;
	/* the token is written by the operator, not by its operands */
	t.c5 = op->c5;
	*l = t;
}

/*
Append the replacement list tokens from t to end to out, replacing
parameters with arguments and applying the '#' and '##' operators.

Tokens of the replacement list take the location of the macro
invocation, but keep the mode of the file they were written in.
*/
static void
subst(struct macro *m, struct macroarg *args, struct token *t, struct token *end, struct location *loc, struct array *out)
{
	struct array inner;
	struct token tmp, *seq, *op, *body;
	struct macroarg *arg;
	size_t i, n, depth, pos;
	bool space, carry, empty;

	op = NULL;      /* '##' operator before the current operand */
	empty = false;  /* whether the left operand of op is a placemarker */
	carry = false;  /* whether an omitted operand was preceeded by a space */
	while (t < end) {
		if (t->kind == THASHHASH) {
			op = t++;
			continue;
		}
		/* the space before the replacement list is not part of it */
		space = t->space && t != m->token || carry;
		inner = (struct array){0};
		if (m->kind == MACROFUNC && t->kind == THASH) {
			tmp = stringize(&args[macroparam(m, t + 1)]);
			tmp.loc = *loc;
			tmp.c5 = t->c5;
			seq = &tmp, n = 1;
			t += 2;
		} else if (t->kind == T__VA_OPT__ && macrovarargs(m)) {
			body = t + 2;
			for (depth = 1, t = body; t->kind != TRPAREN || --depth > 0; ++t) {
				if (t->kind == TLPAREN)
					++depth;
			}
			if (args[m->nparam - 1].ntoken > 0)
				subst(m, args, body, t, loc, &inner);
			seq = inner.val, n = inner.len / sizeof(*seq);
			++t;
		} else if ((i = macroparam(m, t)) != -1) {
			arg = &args[i];
			if (commapaste(m, t)) {
				op = NULL;
				if (arg->omitted)
					out->len -= sizeof(*t);  /* remove the comma */
				seq = arg->token, n = arg->ntoken;
			} else if (op || t + 1 < end && t[1].kind == THASHHASH) {
				seq = arg->raw, n = arg->nraw;
			} else {
				seq = arg->token, n = arg->ntoken;
			}
			++t;
		} else {
			tmp = *t++;
			tmp.loc = *loc;
			seq = &tmp, n = 1;
		}
		if (op && !empty && out->len > 0) {
			if (n > 0) {
				paste(arraylast(out, sizeof(*seq)), seq, op);
				arrayaddbuf(out, seq + 1, (n - 1) * sizeof(*seq));
			}
		} else if (n > 0) {
			pos = out->len;
			arrayaddbuf(out, seq, n * sizeof(*seq));
			((struct token *)((char *)out->val + pos))->space = space;
			empty = false;
			carry = false;
		} else {
			if (!op)
				empty = true;
			carry = space;
		}
		op = NULL;
		free(inner.val);
	}
}

static bool expand(struct token *);

/* macro-expand an argument on its own, as if it were the rest of the file */
static void
expandarg(struct macroarg *arg)
{
	struct array buf = {0};
	struct token *raw, *t, cur;

	/* the argument is followed by an EOF token to stop the expansion */
	raw = xreallocarray(NULL, arg->nraw + 1, sizeof(*raw));
	if (arg->nraw > 0)
		memcpy(raw, arg->raw, arg->nraw * sizeof(*raw));
	raw[arg->nraw] = (struct token){.kind = TEOF};
	ctxpush(raw, arg->nraw + 1, NULL, raw[0].space);
	for (;;) {
		t = rawnext();
		if (t == &raw[arg->nraw])
			break;
		cur = *t;
		if (!expand(&cur))
			arrayaddbuf(&buf, &cur, sizeof(cur));
	}
	/* the frame of the argument is now on top, and empty */
	ctx.len -= sizeof(struct frame);
	free(raw);
	arg->token = buf.val;
	arg->ntoken = buf.len / sizeof(cur);
}

/* read the arguments of a function-like macro invoked at loc, after the '(' */
static struct macroarg *
readargs(struct macro *m, struct location *loc)
{
	struct macroarg *args;
	struct array buf = {0};
	struct token *t, cur;
	size_t i, paren;
	bool space;

	args = xreallocarray(NULL, m->nparam + 1, sizeof(*args));
	for (i = 0; i <= m->nparam; ++i)
		args[i] = (struct macroarg){0};
	i = 0;
	paren = 0;
	space = false;
	for (;;) {
		t = rawnext();
		switch (t->kind) {
		case TEOF:
			error(loc, "EOF when reading macro parameters");
		case TNEWLINE:
			space = true;
			continue;
		case TLPAREN:
			++paren;
			break;
		case TRPAREN:
			if (paren == 0)
				goto done;
			--paren;
			break;
		case TCOMMA:
			if (paren > 0 || i < m->nparam && m->param[i].flags & PARAMVAR)
				break;
			if (++i >= m->nparam)
				error(&t->loc, "too many arguments for macro '%s'", m->name);
			space = false;
			continue;
		}
		if (m->nparam == 0)
			error(&t->loc, "too many arguments for macro '%s'", m->name);
		cur = *t;
		if (space)
			cur.space = true;
		space = false;
		arrayaddbuf(&buf, &cur, sizeof(cur));
		++args[i].nraw;
	}
done:
	/* the variadic arguments may be omitted entirely */
	if (i + 1 < m->nparam && !(i + 2 == m->nparam && macrovarargs(m)))
		error(&t->loc, "not enough arguments for macro '%s'", m->name);
	if (macrovarargs(m))
		args[m->nparam - 1].omitted = i + 2 == m->nparam || m->nparam == 1 && buf.len == 0;
	/* args[0].raw is the buffer of all arguments */
	args[0].raw = buf.val;
	for (i = 1; i < m->nparam; ++i)
		args[i].raw = args[i - 1].raw + args[i - 1].nraw;
	for (i = 0; i < m->nparam; ++i) {
		if (m->param[i].flags & PARAMTOK)
			expandarg(&args[i]);
	}
	return args;
}

static char *
quote(const char *s)
{
	struct array buf = {0};

	arrayaddbuf(&buf, "\"", 1);
	for (; *s; ++s) {
		if (*s == '\\' || *s == '"')
			arrayaddbuf(&buf, "\\", 1);
		arrayaddbuf(&buf, s, 1);
	}
	arrayaddbuf(&buf, "\"", 2);
	return buf.val;
}

/*
Replace a predefined macro that depends on where or when it is used.
The location of a token from a macro expansion is that of the outermost
invocation, so __FILE__ and __LINE__ are right in macro bodies too.
*/
static void
builtin(struct token *t)
{
	static unsigned long counter;
	char buf[32];
	time_t now;
	size_t len;

	switch (t->kind) {
	case T__FILE__:
		t->kind = TSTRINGLIT;
		t->lit = quote(t->loc.file ? t->loc.file : "");
		return;
	case T__LINE__:
		len = snprintf(buf, sizeof(buf), "%zu", t->loc.line);
		break;
	case T__COUNTER__:
		len = snprintf(buf, sizeof(buf), "%lu", counter++);
		break;
	case T__DATE__:
	case T__TIME__:
		now = time(NULL);
		len = strftime(buf, sizeof(buf), t->kind == T__DATE__ ? "\"%b %e %Y\"" : "\"%H:%M:%S\"", localtime(&now));
		t->kind = TSTRINGLIT;
		t->lit = xmalloc(len + 1);
		memcpy(t->lit, buf, len + 1);
		return;
	default:
		return;
	}
	t->kind = TNUMBER;
	t->lit = xmalloc(len + 1);
	memcpy(t->lit, buf, len + 1);
}

/*
If the token is a macro to expand, push its expansion to the context
and return true. The token must be a copy, since reading the macro
arguments may free the context frame it came from.
*/
static bool
expand(struct token *t)
{
	struct macro *m;
	struct macroarg *args;
	struct array out = {0};
	size_t i;

	if (t->kind < TPPIDENT || t->hide)
		return false;
	m = macroget(t->kind);
	if (!m) {
		builtin(t);
		t->hide = true;
		return false;
	}
	if (m->hide) {
		t->hide = true;
		return false;
	}
	args = NULL;
	if (m->kind == MACROFUNC) {
		if (!peekparen())
			return false;
		args = readargs(m, &t->loc);
	}
	subst(m, args, m->token, m->token + m->ntoken, &t->loc, &out);
	if (args) {
		for (i = 0; i < m->nparam; ++i)
			free(args[i].token);
		free(args[0].raw);
		free(args);
	}
	m->exp = out.val;
	ctxpush(out.val, out.len / sizeof(*t), m, t->space || out.len > 0 && ((struct token *)out.val)->space);
	m->hide = true;
	return true;
}

/* whether a file is parsed in C5 (C-incompatible) mode, based on its extension */
bool
c5file(const char *name)
{
	static const char *last;
	static bool result;
	const char *dot;

	if (name != last) {
		last = name;
		dot = name ? strrchr(name, '.') : NULL;
		result = dot && (strcmp(dot, ".c5") == 0 || strcmp(dot, ".h5") == 0);
	}
	return result;
}

/* skip a _Pragma operator; like #pragma directives, they are ignored */
static void
pragmaop(void)
{
	struct location loc;

	loc = tok.loc;
	next();
	if (tok.kind != TLPAREN)
		error(&tok.loc, "expected '(' after _Pragma");
	do next();
	while (tok.kind != TRPAREN && tok.kind != TEOF);
	if (tok.kind == TEOF)
		error(&loc, "EOF in _Pragma operator");
}

void
next(void)
{
	struct token cur;

	for (;;) {
		cur = *rawnext();
		if (expand(&cur))
			continue;
		if (cur.kind == TNEWLINE && !(ppflags & PPNEWLINE))
			continue;
		if (cur.kind == T_PRAGMAOP) {
			tok = cur;
			pragmaop();
			continue;
		}
		break;
	}
	tok = cur;

	/* keyword aliases */
	switch (tok.kind) {
	case ALIAS_ALIGNAS:       tok.kind = TALIGNAS;       break;
	case ALIAS_ALIGNOF:       tok.kind = TALIGNOF;       break;
	case ALIAS_BOOL:          tok.kind = TBOOL;          break;
	case ALIAS__INLINE:
	case ALIAS__INLINE__:     tok.kind = TINLINE;        break;
	case ALIAS__SIGNED:
	case ALIAS__SIGNED__:     tok.kind = TSIGNED;        break;
	case ALIAS_STATIC_ASSERT: tok.kind = TSTATIC_ASSERT; break;
	case ALIAS_THREAD_LOCAL:
	case ALIAS__THREAD:       tok.kind = TTHREAD_LOCAL;  break;
	case ALIAS__TYPEOF:
	case ALIAS__TYPEOF__:     tok.kind = TTYPEOF;        break;
	case ALIAS__VOLATILE__:   tok.kind = TVOLATILE;      break;
	case ALIAS__ASM:          tok.kind = T__ASM__;       break;
	}

	/* keywords spelled in C5 files */
	if (tok.kind >= C5_ARRAY && tok.kind <= C5_SLICE && tok.c5) {
		switch (tok.kind) {
		case C5_ARRAY:    tok.kind = T_ARRAY;    break;
		case C5_DEFER:    tok.kind = T_DEFER;    break;
		case C5_ERASED:   tok.kind = T_ERASED;   break;
		case C5_EXISTS:   tok.kind = T_EXISTS;   break;
		case C5_FORALL:   tok.kind = T_FORALL;   break;
		case C5_GIVEN:    tok.kind = T_GIVEN;    break;
		case C5_IMPLICIT: tok.kind = T_IMPLICIT; break;
		case C5_MONO:     tok.kind = T_MONO;     break;
		case C5_SLICE:    tok.kind = T_SLICE;    break;
		}
	}
}

bool
peek(enum tokenkind kind)
{
	static struct token pending;
	struct token old;

	old = tok;
	next();
	if (tok.kind == kind) {
		next();
		return true;
	}
	pending = tok;
	tok = old;
	ctxpush(&pending, 1, NULL, pending.space);
	return false;
}

/*
Whether the braces opened by the current token are followed by a token
of the given kind. Used to tell a destructuring pattern, which is
followed by '=', from a compound statement.
*/
bool
peekbraces(enum tokenkind kind)
{
	struct array buf = {0};
	struct token *t;
	size_t depth, n;
	bool result;

	assert(tok.kind == TLBRACE);
	arrayaddbuf(&buf, &tok, sizeof(tok));
	next();
	result = false;
	switch (tok.kind) {
	/* tokens that start a statement or declaration, but not a pattern */
	case TRBRACE: case TSEMICOLON: case TIF: case TSWITCH: case TWHILE: case TDO: case TFOR:
	case TGOTO: case TCONTINUE: case TBREAK: case TRETURN: case TCASE: case TDEFAULT:
	case T_DEFER: case TSTATIC: case TEXTERN: case TTYPEDEF: case TREGISTER: case TSTATIC_ASSERT:
	case TMUL: case TLPAREN: case TINC: case TDEC: case TEOF:
		arrayaddbuf(&buf, &tok, sizeof(tok));
		break;
	default:
		depth = 1;
		for (;;) {
			arrayaddbuf(&buf, &tok, sizeof(tok));
			if (tok.kind == TEOF)
				break;
			if (tok.kind == TLBRACE)
				++depth;
			else if (tok.kind == TRBRACE && --depth == 0)
				break;
			next();
		}
		if (tok.kind != TEOF) {
			next();
			arrayaddbuf(&buf, &tok, sizeof(tok));
			result = tok.kind == kind;
		}
	}
	/* the tokens are read again; the buffer must outlive them, so it is not freed */
	t = buf.val;
	n = buf.len / sizeof(*t);
	tok = t[0];
	ctxpush(t + 1, n - 1, NULL, t[1].space);
	return result;
}

char *
expect(enum tokenkind kind, const char *msg)
{
	char *lit;

	lit = tokencheck(&tok, kind, msg);
	next();

	return lit;
}

bool
consume(enum tokenkind kind)
{
	if (tok.kind != kind)
		return false;
	next();
	return true;
}
