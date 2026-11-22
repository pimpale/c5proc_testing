#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "utf.h"
#include "cc.h"

static struct expr *
mkexpr(enum exprkind k, struct type *t, struct expr *b)
{
	struct expr *e;

	e = xmalloc(sizeof(*e));
	e->qual = QUALNONE;
	e->type = t;
	e->lvalue = false;
	e->decayed = false;
	e->kind = k;
	e->base = b;
	e->next = NULL;
	e->toeval = NULL;
	memset(&e->u, 0, sizeof(e->u));

	return e;
}

void
delexpr(struct expr *e)
{
	struct expr *sub;

	switch (e->kind) {
	case EXPRCALL:
		delexpr(e->base);
		while (sub = e->u.call.args) {
			e->u.call.args = sub->next;
			delexpr(sub);
		}
		break;
	case EXPRBITFIELD:
	case EXPRINCDEC:
	case EXPRUNARY:
	case EXPRCAST:
		delexpr(e->base);
		break;
	case EXPRBINARY:
		delexpr(e->u.binary.l);
		delexpr(e->u.binary.r);
		break;
	case EXPRCOND:
		delexpr(e->base);
		if (e->u.cond.t != e->base)
			delexpr(e->u.cond.t);
		delexpr(e->u.cond.f);
		break;
	/*
	XXX: compound assignment causes some reuse of expressions,
	so we can't free them without risk of a double-free

	case EXPRASSIGN:
		delexpr(e->assign.l);
		delexpr(e->assign.r);
		break;
	*/
	case EXPRCOMMA:
		while (sub = e->base) {
			e->base = sub->next;
			delexpr(sub);
		}
		break;
	}
	free(e);
}

static struct expr *
mkconstexpr(struct type *t, unsigned long long n)
{
	struct expr *e;

	e = mkexpr(EXPRCONST, t, NULL);
	e->u.constant.u = n;

	return e;
}

static struct expr *mkunaryexpr(enum tokenkind, struct expr *);
static struct expr *mkbinaryexpr(struct location *, enum tokenkind, struct expr *, struct expr *);

/*
A C5 array is a value: it is assigned, passed, and returned as a whole.
Like a C array, an expression of C5 array type is represented by a
pointer to its first element, which is used for indexing and pointer
arithmetic. This returns the array itself where its value is needed, or
NULL if e is not a C5 array.
*/
struct expr *
exprunarray(struct expr *e)
{
	if (e->decayed && e->base->type->kind == TYPEARRAY && e->base->type->u.array.byvalue)
		return e->base;
	return NULL;
}

/* a copy of an expression that refers to an object, which can be used independently of it */
struct expr *
exprdup(struct expr *e)
{
	struct expr *n;

	n = xmalloc(sizeof(*n));
	*n = *e;
	n->next = NULL;
	switch (e->kind) {
	case EXPRIDENT:
	case EXPRCONST:
	case EXPRLAYOUT:
	case EXPRSIZEPARAM:
		break;
	case EXPRUNARY:
	case EXPRCAST:
	case EXPRBITFIELD:
		n->base = exprdup(e->base);
		break;
	case EXPRBINARY:
		n->u.binary.l = exprdup(e->u.binary.l);
		n->u.binary.r = exprdup(e->u.binary.r);
		break;
	default:
		fatal("internal error: cannot copy expression");
	}
	return n;
}

/* 6.3.2.1 Conversion of arrays and function designators */
static struct expr *
decay(struct expr *e)
{
	struct type *t;
	enum typequal tq;

	/* XXX: combine with decl.c:adjust in some way? */
	t = e->type;
	tq = e->qual;
	switch (t->kind) {
	case TYPEARRAY:
		/*
		XXX: qualifiers should be applied to the element
		type of array types, not the array type itself

		assert(tq == QUALNONE);
		*/
		e = mkunaryexpr(TBAND, e);
		e->type = mkpointertype(t->base, t->qual | tq);
		e->decayed = true;
		break;
	case TYPEFUNC:
		e = mkunaryexpr(TBAND, e);
		e->decayed = true;
		break;
	}

	return e;
}

static struct expr *
mkunaryexpr(enum tokenkind op, struct expr *base)
{
	struct expr *expr;
	struct type *type;

	switch (op) {
	case TBAND:
		if (base->decayed) {
			expr = base;
			base = base->base;
			free(expr);
		}
		/*
		Allow struct and union types even if they are not lvalues,
		since we take their address when compiling member access.
		*/
		if (!base->lvalue && base->type->kind != TYPEFUNC && base->type->kind != TYPESTRUCT && base->type->kind != TYPEUNION && !(base->type->kind == TYPEARRAY && base->type->u.array.byvalue))
			error(&tok.loc, "'&' operand is not an lvalue or function designator");
		if (base->kind == EXPRBITFIELD)
			error(&tok.loc, "cannot take address of bit-field");
		expr = mkexpr(EXPRUNARY, mkpointertype(base->type, base->qual), base);
		expr->op = op;
		return expr;
	case TMUL:
		if (base->type->kind != TYPEPOINTER)
			error(&tok.loc, "cannot dereference non-pointer");
		if (base->kind == EXPRUNARY && base->op == TBAND && base->base->kind != EXPRSTRING && (base->base->lvalue || base->base->type->kind != TYPEARRAY)) {
			type = base->type->base;
			expr = base->base;
			expr->type = type;
		} else {
			expr = mkexpr(EXPRUNARY, base->type->base, base);
			expr->qual = base->type->qual;
			expr->lvalue = true;
			expr->op = op;
		}
		return decay(expr);
	}
	/* other unary operators get compiled as equivalent binary ones */
	fatal("internal error: unknown unary operator %d", op);
	return NULL;
}

static unsigned
bitfieldwidth(struct expr *e)
{
	if (e->kind != EXPRBITFIELD)
		return -1;
	return e->type->size * 8 - e->u.bitfield.bits.before - e->u.bitfield.bits.after;
}

static struct expr *
exprconvert(struct expr *e, struct type *t)
{
	if (typecompatible(e->type, t))
		return e;
	return mkexpr(EXPRCAST, t, e);
}

static bool
nullpointer(struct expr *e)
{
	if (e->kind != EXPRCONST)
		return false;
	if (e->type->kind == TYPENULLPTR)
		return true;
	if (!(e->type->prop & PROPINT) && (e->type->kind != TYPEPOINTER || e->type->base != &typevoid))
		return false;
	return e->u.constant.u == 0;
}

/*
Check that e can be assigned to an object of type t. If it can't,
return a description of the violated constraint.
*/
static const char *
assigncheck(struct expr *e, struct type *t)
{
	static char buf[256];
	struct type *et;

	et = e->type;
	switch (t->kind) {
	case TYPEBOOL:
		if (!(et->prop & PROPARITH) && et->kind != TYPEPOINTER && et->kind != TYPENULLPTR)
			return "assignment to bool must be from arithmetic, pointer, or nullptr_t type";
		break;
	case TYPEPOINTER:
		if (nullpointer(e))
			break;
		if (et->kind != TYPEPOINTER)
			return "assignment to pointer must be from pointer or null pointer constant";
		if (t->base != &typevoid && et->base != &typevoid && !typecompatible(t->base, et->base)) {
			/* a pointer converts to a pointer to a const variant of its target where that is safe */
			if (!typeconstvariant(t->base, et->base))
				return "base types of pointer assignment must be compatible or void";
			if (!qualsubset(et->qual, t->qual))
				return "assignment to pointer discards qualifiers";
			if (typeconstconv(et, t))
				break;
			if (t->base->kind == TYPEFUNC)
				return "function types are const variants that do not convert; a function converts only to one whose parameters convert to its own, and which returns what its own result converts to";
			return "pointed-to types are const variants that do not convert; a pointer converts only to a pointer to const of a type its target converts to";
		}
		if (!qualsubset(et->qual, t->qual))
			return "assignment to pointer discards qualifiers";
		break;
	case TYPENULLPTR:
		if (!nullpointer(e))
			return "assignment to nullptr_t must be from null pointer constant or expression with type nullptr_t";
		break;
	case TYPESTRUCT:
	case TYPEUNION:
		/* an instance converts to a const variant as the markers of its parameters allow */
		if (typecompatible(t, et) || typeconstconv(et, t))
			break;
		if (typeconstvariant(t, et))
			return "const variants of a struct or union convert only as the '+' and '-' markers on its parameters allow";
		return t->kind == TYPEUNION ? "assignment to union type must be from compatible type" : "assignment to struct type must be from compatible type";
	case TYPEPARAM:
		if (t != et) {
			snprintf(buf, sizeof(buf), "assignment to type parameter '%s' must be from the same type", t->u.param.name);
			return buf;
		}
		break;
	case TYPEARRAY:
		e = exprunarray(e);
		if (!t->u.array.byvalue || !e || !typecompatible(t, e->type))
			return "assignment to array type must be from compatible array type";
		break;
	default:
		assert(t->prop & PROPARITH);
		if (!(et->prop & PROPARITH))
			return "assignment to arithmetic type must be from arithmetic type";
		break;
	}
	return NULL;
}

/* stands in for an expression that could not be assigned to type t, after the error is reported */
static struct expr *
assignrecover(struct type *t)
{
	if (t->prop & PROPSCALAR)
		return mkconstexpr(t, 0);
	return exprtemp(t);
}

struct expr *
exprassign(struct expr *e, struct type *t)
{
	const char *err;

	err = assigncheck(e, t);
	if (err) {
		softerror(&tok.loc, "%s", err);
		return assignrecover(t);
	}
	switch (t->kind) {
	case TYPESTRUCT:
	case TYPEUNION:
		if (typecompatible(t, e->type))
			break;
		if (e->kind == EXPRCOMPOUND) {
			e->type = t;
			e->u.compound.decl->type = t;
			return e;
		}
		return mkexpr(EXPRCAST, t, e);
	case TYPEARRAY:
		return exprunarray(e);
	}
	return exprconvert(e, t);
}

struct expr *
exprconst(struct type *t, unsigned long long n)
{
	return mkconstexpr(t, n);
}

/* comparison of two scalar expressions, for matching patterns */
struct expr *
exprcompare(enum tokenkind op, struct expr *l, struct expr *r)
{
	return mkbinaryexpr(&tok.loc, op, l, r);
}

/* a temporary that holds a value once it is assigned */
struct expr *
exprtemp(struct type *t)
{
	struct expr *e;

	e = mkexpr(EXPRTEMP, t, NULL);
	e->lvalue = true;
	e->u.temp = NULL;
	return e;
}

struct expr *
exprpromote(struct expr *e)
{
	struct type *t;

	t = typepromote(e->type, bitfieldwidth(e));
	return exprconvert(e, t);
}

static struct type *
commonreal(struct expr **e1, struct expr **e2)
{
	struct type *t;

	t = typecommonreal((*e1)->type, bitfieldwidth(*e1), (*e2)->type, bitfieldwidth(*e2));
	*e1 = exprconvert(*e1, t);
	*e2 = exprconvert(*e2, t);

	return t;
}

/* a layout quantity of a type depending on mono parameters, computed when it is instantiated */
static struct expr *
mklayoutexpr(enum layoutkind kind, struct type *t, char *member)
{
	struct expr *e;

	e = mkexpr(EXPRLAYOUT, &typeulong, NULL);
	e->u.layout.kind = kind;
	e->u.layout.type = t;
	e->u.layout.member = member;
	return e;
}

static struct expr *
mksizeofexpr(struct type *t) {
	struct expr *e;

	if (typedep(t)) {
		e = mklayoutexpr(LAYOUTSIZE, t, NULL);
	} else if (t->kind == TYPEARRAY && t->size == 0 && t->prop & PROPVM) {
		e = mkexpr(EXPRSIZEOF, &typeulong, NULL);
		e->u.szof.type = t;
	} else {
		e = mkconstexpr(&typeulong, t->size);
	}

	return e;
}

static struct expr *slicedata(struct expr *);

static struct expr *
mkbinaryexpr(struct location *loc, enum tokenkind op, struct expr *l, struct expr *r)
{
	struct expr *e;
	struct type *t = NULL;
	enum typeprop lp, rp;

	if (op == TADD || op == TSUB) {
		l = slicedata(l);
		r = slicedata(r);
	}
	lp = l->type->prop;
	rp = r->type->prop;
	switch (op) {
	case TLOR:
	case TLAND:
		if (!(lp & PROPSCALAR))
			error(loc, "left operand of '%s' operator must be scalar", tokenstr(op));
		if (!(rp & PROPSCALAR))
			error(loc, "right operand of '%s' operator must be scalar", tokenstr(op));
		t = &typeint;
		break;
	case TEQL:
	case TNEQ:
		t = &typeint;
		if (lp & PROPARITH && rp & PROPARITH) {
			commonreal(&l, &r);
			break;
		}
		if (l->type->kind != TYPEPOINTER)
			e = l, l = r, r = e;
		if (l->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		if (nullpointer(eval(r))) {
			r = exprconvert(r, l->type);
			break;
		}
		if (nullpointer(eval(l))) {
			l = exprconvert(l, r->type);
			break;
		}
		if (r->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		if (l->type->base->kind == TYPEVOID)
			e = l, l = r, r = e;
		if (r->type->base->kind == TYPEVOID && l->type->base->kind != TYPEFUNC)
			r = exprconvert(r, l->type);
		else if (!typecompatible(l->type->base, r->type->base))
			error(loc, "pointer operands to '%s' operator are to incompatible types", tokenstr(op));
		break;
	case TLESS:
	case TGREATER:
	case TLEQ:
	case TGEQ:
		t = &typeint;
		if (lp & PROPREAL && rp & PROPREAL) {
			commonreal(&l, &r);
		} else if (l->type->kind == TYPEPOINTER && r->type->kind == TYPEPOINTER) {
			if (!typecompatible(l->type->base, r->type->base) || l->type->base->kind == TYPEFUNC)
				error(loc, "pointer operands to '%s' operator must be to compatible object types", tokenstr(op));
		} else {
			error(loc, "invalid operands to '%s' operator", tokenstr(op));
		}
		break;
	case TBOR:
	case TXOR:
	case TBAND:
		t = commonreal(&l, &r);
		break;
	case TADD:
		if (lp & PROPARITH && rp & PROPARITH) {
			t = commonreal(&l, &r);
			break;
		}
		if (r->type->kind == TYPEPOINTER)
			e = l, l = r, r = e, rp = lp;
		if (l->type->kind != TYPEPOINTER || !(rp & PROPINT))
			error(loc, "invalid operands to '+' operator");
		t = l->type;
		if (t->base->incomplete || t->base->kind == TYPEFUNC)
			error(loc, "pointer operand to '+' must be to complete object type");
		r = mkbinaryexpr(loc, TMUL, exprconvert(r, &typeulong), mksizeofexpr(t->base));
		break;
	case TSUB:
		if (lp & PROPARITH && rp & PROPARITH) {
			t = commonreal(&l, &r);
			break;
		}
		if (l->type->kind != TYPEPOINTER || !(rp & PROPINT) && r->type->kind != TYPEPOINTER)
			error(loc, "invalid operands to '-' operator");
		if (l->type->base->incomplete || l->type->base->kind == TYPEFUNC)
			error(loc, "pointer operand to '-' must be to complete object type");
		if (rp & PROPINT) {
			t = l->type;
			r = mkbinaryexpr(loc, TMUL, exprconvert(r, &typeulong), mksizeofexpr(t->base));
		} else {
			if (!typecompatible(l->type->base, r->type->base))
				error(&tok.loc, "pointer operands to '-' are to incompatible types");
			op = TDIV;
			t = &typelong;
			e = mkbinaryexpr(loc, TSUB, exprconvert(l, &typelong), exprconvert(r, &typelong));
			r = mksizeofexpr(l->type->base);
			l = e;
		}
		break;
	case TMOD:
		if (!(lp & PROPINT) || !(rp & PROPINT))
			error(loc, "operands to '%%' operator must be integer");
		t = commonreal(&l, &r);
		break;
	case TMUL:
	case TDIV:
		if (!(lp & PROPARITH) || !(rp & PROPARITH))
			error(loc, "operands to '%s' operator must be arithmetic", tokenstr(op));
		t = commonreal(&l, &r);
		break;
	case TSHL:
	case TSHR:
		if (!(lp & PROPINT) || !(rp & PROPINT))
			error(loc, "operands to '%s' operator must be integer", tokenstr(op));
		l = exprpromote(l);
		r = exprpromote(r);
		t = l->type;
		break;
	default:
		fatal("internal error: unknown binary operator %d", op);
	}
	e = mkexpr(EXPRBINARY, t, NULL);
	e->op = op;
	e->u.binary.l = l;
	e->u.binary.r = r;

	return e;
}

static struct type *
inttype(unsigned long long val, bool decimal, char *suffix)
{
	enum {
		U = 1,
		L = 2,
		LL = 4,
		WB = 8,
	};
	static struct type *const types[] = {
		&typeint,
		&typeuint,   /* u */
		&typelong,   /* l */
		&typeulong,  /* ul */
		&typellong,  /* ll */
		&typeullong, /* ull */
	};
	int flags, i, step;
	bool sign;
	char *s;
	struct type *t;

	/* parse suffix */
	flags = 0;
	for (s = suffix; *s; ++s) {
		int new;

		switch (*s) {
		case 'u':
		case 'U': new = U; break;
		case 'l':
		case 'L': new = s[1] == s[0] ? (++s, LL) : L; break;
		case 'w': if (s[1] != 'b') goto invalid; ++s, new = WB; break;
		case 'W': if (s[1] != 'B') goto invalid; ++s, new = WB; break;
		default:
		invalid: error(&tok.loc, "invalid integer constant suffix '%s'", suffix);
		}
		if (flags & new || flags & ~U && new & ~U)
			goto invalid;
		flags |= new;
	}

	/* find integer type */
	sign = !(flags & U);
	if (flags & WB) {
		for (i = 1;; ++i) {
			if (i > 64 - sign)
				goto notype;
			if (val <= 0xffffffffffffffff >> 64 - i)
				break;
		}
		return mkbitinttype(i + sign, sign);
	}
	assert(flags < countof(types));
	step = !sign || decimal ? 2 : 1;
	for (i = flags; i < countof(types); i += step) {
		t = types[i];
		if (typehasint(t, val, false))
			return t;
	}
notype:
	error(&tok.loc, "no suitable type for constant '%s'", tok.lit);
}

static int
octval(int c)
{
	if ('0' <= c && c <= '7')
		return c - '0';
	return -1;
}

static int
hexval(int c)
{
	if ('0' <= c && c <= '9')
		return c - '0';
	if ('a' <= c && c <= 'f')
		return c - 'a' + 10;
	if ('A' <= c && c <= 'F')
		return c - 'A' + 10;
	return -1;
}

static size_t
decodechar(const char *src, uint_least32_t *chr, bool *hexoct, const char *desc, struct location *loc)
{
	uint_least32_t c;
	size_t n;
	int i, v;
	const unsigned char *s = (const unsigned char *)src;

	*hexoct = false;
	if (*s == '\\') {
		++s;
		switch (*s) {
		case '\'':
		case '"':
		case '?':
		case '\\': c = *s;   ++s; break;
		case 'a':  c = '\a'; ++s; break;
		case 'b':  c = '\b'; ++s; break;
		case 'f':  c = '\f'; ++s; break;
		case 'n':  c = '\n'; ++s; break;
		case 'r':  c = '\r'; ++s; break;
		case 't':  c = '\t'; ++s; break;
		case 'v':  c = '\v'; ++s; break;
		case 'o':
		case 'u':
		case 'x':
			if (s[1] == '{') {
				/* delimited escape sequence (C2y); the scanner checked its form */
				i = *s;
				c = 0;
				for (s += 2; *s != '}'; ++s) {
					if (c > 0xffffffff / 16)
						error(loc, "escape sequence in %s is out of range", desc);
					c = c * (i == 'o' ? 8 : 16) + hexval(*s);
				}
				++s;
				if (i == 'u') {
					/* a universal character name, which is encoded like the character written directly */
					if (c > 0x10ffff || c >= 0xd800 && c <= 0xdfff)
						error(loc, "\\u{%lx} in %s is not a Unicode scalar value", (unsigned long)c, desc);
				} else {
					*hexoct = true;
				}
				break;
			}
			++s;
			c = 0;
			v = hexval(*s);
			assert(v >= 0);
			do {
				if (c > 0xffffffff / 16)
					error(&tok.loc, "character constant escape is out of range");
				c = c * 16 + v;
				v = hexval(*++s);
			} while (v >= 0);
			*hexoct = true;
			break;
		default:
			c = 0;
			v = octval(*s);
			assert(v >= 0);
			i = 0;
			do {
				if (c > 0xffffffff / 8)
					error(&tok.loc, "character constant escape is out of range");
				c = c * 8 + v;
				v = octval(*++s);
			} while (v >= 0 && ++i < 3);
			*hexoct = true;
		}
	} else {
		n = utf8dec(&c, s, 4);
		if (n == (size_t)-1)
			error(loc, "%s contains invalid UTF-8", desc);
		s += n;
	}
	*chr = c;
	return s - (const unsigned char *)src;
}

static size_t
encodechar8(void *dst, uint_least32_t chr, bool hexoct)
{
	if (!hexoct)
		return utf8enc(dst, chr);
	*(unsigned char *)dst = chr;
	return 1;
}

static size_t
encodechar16(void *dst, uint_least32_t chr, bool hexoct)
{
	if (!hexoct)
		return utf16enc(dst, chr) * sizeof(uint_least16_t);
	*(uint_least16_t *)dst = chr;
	return sizeof(uint_least16_t);
}

static size_t
encodechar32(void *dst, uint_least32_t chr, bool hexoct)
{
	*(uint_least32_t *)dst = chr;
	return sizeof(uint_least32_t);
}

struct type *
stringconcat(struct stringlit *str, bool forceutf8)
{
	static struct array parts;
	struct {
		struct location loc;
		char *str;
	} *p;
	int kind, newkind, term, newterm;
	struct type *t;
	size_t (*encodechar)(void *, uint_least32_t, bool);
	char *src;
	unsigned char *buf, *dst;
	uint_least32_t chr;
	bool hexoct, c5;
	size_t len, width;

	assert(tok.kind == TSTRINGLIT);
	parts.len = 0;
	len = 0;
	kind = 0;
	term = 0;
	c5 = tok.c5;
	do {
		src = tok.lit;
		/* p: no null terminator (Pascal style), c: null terminator (C style) */
		newterm = 0;
		if (*src == 'p' || *src == 'c')
			newterm = *src++;
		switch (*src) {
		case 'n': newkind = 'n', ++src; break;
		case 'u': if (src[1] == '8') ++src; /* fallthrough */
		case 'L':
		case 'U': newkind = *src, ++src; break;
		case '"': newkind = 0; break;
		default: assert(0);
		}
		if (kind != newkind && kind && newkind || term != newterm && term && newterm)
			error(&tok.loc, "adjacent string literals have differing prefixes");
		if (newkind)
			kind = newkind;
		if (newterm)
			term = newterm;
		p = arrayadd(&parts, sizeof(*p));
		p->loc = tok.loc;
		p->str = src + 1;
		len += strlen(src) - 2;
		next();
	} while (tok.kind == TSTRINGLIT);
	if (forceutf8) {
		kind = '8';
		term = 'c';
	}
	/* in C5 files, strings are UTF-8 and have no null terminator by default */
	if (!kind)
		kind = c5 ? '8' : 'n';
	if (!term)
		term = c5 ? 'p' : 'c';
	++len;  /* null byte */
	switch (kind) {
	case 'n': t = &typechar; break;
	case '8': t = &typeuchar; break;
	case 'u': t = &typeushort; break;
	case 'U': t = &typeuint; break;
	case 'L': t = targ->typewchar; break;
	default: assert(0);
	}
	switch (t->size) {
	case 1:
		width = 1;
		encodechar = encodechar8;
		break;
	case 2:
		width = sizeof(uint_least16_t);
		encodechar = encodechar16;
		break;
	case 4:
		width = sizeof(uint_least32_t);
		encodechar = encodechar32;
		break;
	default:
		assert(0);
	}
	buf = xreallocarray(NULL, len, width);
	str->data = buf;
	dst = buf;
	arrayforeach(&parts, p) {
		src = p->str;
		while (*src != '"') {
			src += decodechar(src, &chr, &hexoct, "string literal", &p->loc);
			dst += encodechar(dst, chr, hexoct);
		}
	}
	if (term == 'c')
		dst += encodechar(dst, 0, false);
	str->size = (dst - buf) / width;
	return t;
}

static struct expr *
generic(struct scope *s)
{
	struct expr *e, *match = NULL, *def = NULL;
	struct type *t, *want;
	enum typequal qual;

	next();
	expect(TLPAREN, "after '_Generic'");
	e = assignexpr(s);
	expect(TCOMMA, "after generic selector expression");
	want = e->type;
	delexpr(e);
	do {
		if (consume(TDEFAULT)) {
			if (def)
				error(&tok.loc, "multiple default expressions in generic association list");
			expect(TCOLON, "after 'default'");
			def = assignexpr(s);
		} else {
			qual = QUALNONE;
			t = typename(s, &qual, NULL);
			if (!t)
				error(&tok.loc, "expected typename for generic association");
			if (t->kind == TYPEFUNC)
				error(&tok.loc, "generic association must have object type");
			if (t->incomplete)
				error(&tok.loc, "generic association must have complete type");
			if (t->prop & PROPVM)
				error(&tok.loc, "generic association has variably modified type");
			expect(TCOLON, "after type name");
			e = assignexpr(s);
			if (typecompatible(t, want) && qual == QUALNONE) {
				if (match)
					error(&tok.loc, "generic selector matches multiple associations");
				match = e;
			} else {
				delexpr(e);
			}
		}
	} while (consume(TCOMMA));
	expect(TRPAREN, "after generic assocation list");
	if (!match) {
		if (!def)
			error(&tok.loc, "generic selector matches no associations and no default was specified");
		match = def;
	} else if (def) {
		delexpr(def);
	}
	return match;
}

/* 6.5 Expressions */
static void genref(struct scope *, struct expr *);
static struct expr *binaryexpr(struct scope *, struct expr *, int);
static void genbind(struct expr *, struct genarg *);

/*
The type expected of the expression about to be parsed, which is used to
infer type arguments if it is a call to a polymorphic function. It only
applies to the expression that starts at the token it was set at.
*/
static struct type *expecttype;
static struct location expectloc;

void
exprexpect(struct type *t)
{
	expecttype = t;
	expectloc = tok.loc;
}

struct expr *
exprident(struct decl *d)
{
	struct expr *e;

	e = mkexpr(EXPRIDENT, d->type, NULL);
	e->qual = d->qual;
	e->lvalue = d->kind == DECLOBJECT;
	e->u.ident.decl = d;
	return e;
}

static struct expr *
primaryexpr(struct scope *s)
{
	struct expr *e;
	struct decl *d;
	struct type *t;
	char *src, *end;
	uint_least32_t chr;
	unsigned long long val;
	bool hexoct, ordinary, c5;
	int base, prefix;
	struct type *hint;

	hint = NULL;
	if (expecttype) {
		if (tok.loc.file == expectloc.file && tok.loc.line == expectloc.line && tok.loc.col == expectloc.col)
			hint = expecttype;
		expecttype = NULL;
	}
	switch (tok.kind) {
	case TSTRINGLIT:
		c5 = tok.c5;
		e = mkexpr(EXPRSTRING, NULL, NULL);
		t = stringconcat(&e->u.string, false);
		e->type = mkarraytype(t, QUALNONE, e->u.string.size);
		/* a string without a null terminator may be empty */
		e->type->incomplete = false;
		/* in C5 files, string literals are C5 arrays */
		e->type->u.array.byvalue = c5;
		e->lvalue = true;
		e = decay(e);
		break;
	case TCHARCONST:
		src = tok.lit;
		ordinary = false;
		switch (*src) {
		case 'L': ++src; t = targ->typewchar; break;
		case 'u': ++src; t = *src == '8' ? ++src, &typeuchar : &typeushort; break;
		case 'U': ++src; t = &typeuint; break;
		default: t = &typeuchar, ordinary = true;
		}
		assert(*src == '\'');
		++src;
		src += decodechar(src, &chr, &hexoct, "character constant", &tok.loc);
		if (hexoct && !typehasint(t, chr, false))
			error(&tok.loc, "character constant escape is out of range");
		val = chr;
		if (ordinary) {
			if (typechar.u.arith.issigned)
				val = (val ^ 0x80) - 0x80;
			t = &typeint;
		}
		e = mkconstexpr(t, val);
		if (*src != '\'')
			error(&tok.loc, "character constant contains more than one character: %c", *src);
		next();
		break;
	case TNUMBER:
		e = mkexpr(EXPRCONST, NULL, NULL);
		/* length of a prefix that strtoull does not know */
		prefix = 0;
		if (tok.lit[0] == '0') {
			switch (tok.lit[1]) {
			case 'x': case 'X': base = 16; break;
			case 'b': case 'B': base = 2, prefix = 2; break;
			/* C2y octal constant, like 0o755 */
			case 'o': case 'O': base = 8, prefix = 2; break;
			default: base = 8; break;
			}
		} else {
			base = 10;
		}
		if (strpbrk(tok.lit, base == 16 ? ".pP" : ".eE")) {
			/* floating constant */
			e->u.constant.f = strtod(tok.lit, &end);
			if (end == tok.lit)
				error(&tok.loc, "invalid floating constant '%s'", tok.lit);
			if (!end[0])
				e->type = &typedouble;
			else if ((end[0] == 'f' || end[0] == 'F') && !end[1])
				e->type = &typefloat;
			else if ((end[0] == 'l' || end[0] == 'L') && !end[1])
				e->type = &typeldouble;
			else
				error(&tok.loc, "invalid floating constant suffix '%s'", end);
		} else {
			/* C2y makes octal constants without the 0o prefix obsolescent */
			if (base == 8 && !prefix && tok.lit[1] && strspn(tok.lit, "01234567'") > 1 && !tok.sys)
				warning(WARNOCTAL, &tok.loc, "octal constant '%s' has no '0o' prefix, which is obsolescent; write '0o%s'", tok.lit, tok.lit + 1);
			src = tok.lit + prefix;
			/* integer constant */
			e->u.constant.u = strtoull(src, &end, base);
			if (end == src)
				error(&tok.loc, "invalid integer constant '%s'", tok.lit);
			e->type = inttype(e->u.constant.u, base == 10, end);
		}
		next();
		break;
	case TTRUE:
	case TFALSE:
		e = mkexpr(EXPRCONST, &typebool, NULL);
		e->u.constant.u = tok.kind == TTRUE;
		next();
		break;
	case TNULLPTR:
		e = mkexpr(EXPRCONST, &typenullptr, NULL);
		e->u.constant.u = 0;
		next();
		break;
	case TLPAREN:
		next();
		e = expr(s);
		expect(TRPAREN, "after expression");
		break;
	case T_GENERIC:
		if (tok.c5)
			error(&tok.loc, "_Generic is not allowed in C5 files");
		e = generic(s);
		break;
	default:
		if (tok.kind >= TIDENT) {
			d = scopegetdecl(s, tokenstr(tok.kind), 1);
			if (!d)
				error(&tok.loc, "undeclared identifier: %s", tokenstr(tok.kind));
			if (d->kind == DECLCONST && d->gen && d->gen->params[d->u.enumconst].kind == GENCONSTNESS)
				error(&tok.loc, "constness parameter '%s' is not a value", d->name);
			if (d->kind == DECLCONST && d->gen) {
				/* size parameter */
				if (!d->gen->ismono && !allowerasedsize)
					error(&tok.loc, "size parameter '%s' of an erased declaration can only be used in array lengths", d->name);
				e = mksizeparamexpr(d->gen, d->u.enumconst);
				next();
				break;
			}
			if (d->kind == DECLALIAS) {
				/* a name bound by a pattern refers to part of the destructured object */
				e = exprdup(d->u.alias);
				next();
				break;
			}
			if (d->kind == DECLTYPE)
				error(&tok.loc, "unexpected type name '%s' in expression", d->name);
			e = exprident(d);
			next();
			if (d->gen) {
				if (d->kind == DECLFUNC)
					e->u.ident.expected = hint;
				genref(s, e);
			}
			if (d->kind != DECLBUILTIN)
				e = decay(e);
			break;
		}
		error(&tok.loc, "expected primary expression");
	}

	return e;
}

/*
A reference to a polymorphic function. With all type arguments given,
it has the substituted type. Otherwise, the arguments are inferred
when it is called.
*/
static void
genref(struct scope *s, struct expr *e)
{
	struct decl *d;
	struct genarg *args;
	size_t i;

	d = e->u.ident.decl;
	if (d->kind == DECLOBJECT) {
		if (tok.kind != TLESS)
			error(&tok.loc, "polymorphic variable '%s' requires type arguments", d->name);
		genbind(e, genargs(s, d->gen, false));
		return;
	}
	if (tok.kind == TLESS) {
		args = genargs(s, d->gen, true);
		e->u.ident.genargs = args;
		for (i = 0; i < d->gen->nparam; ++i) {
			if (!args[i].type && !args[i].size && !args[i].constset)
				break;
		}
		if (i == d->gen->nparam) {
			genbind(e, args);
			return;
		}
	}
	if (tok.kind != TLPAREN)
		error(&tok.loc, "polymorphic function '%s' requires type arguments", d->name);
}

/*
Give a reference to a polymorphic function its type for the arguments.
A mono function with known arguments refers to the instance for them;
inside a mono function, arguments depending on its parameters are
substituted when it is instantiated.
*/
static void
genbind(struct expr *e, struct genarg *args)
{
	struct decl *d;
	enum typequal q;

	d = e->u.ident.decl;
	e->u.ident.genargs = args;
	q = QUALNONE;
	e->type = typesubst(d->type, &q, d->gen, args);
	e->qual |= q;
	if (!d->gen->ismono)
		return;
	if (argshaveparam(d->gen, args, false))
		error(&tok.loc, "mono %s '%s' cannot be instantiated with erased type parameters", d->kind == DECLFUNC ? "function" : "variable", d->name);
	if (!argshaveparam(d->gen, args, true))
		e->u.ident.decl = monoinst(d, args);
}

/* whether all arguments for g are known */
static bool
argscomplete(struct generic *g, struct genarg *args)
{
	size_t i;

	if (!args)
		return false;
	for (i = 0; i < g->nparam; ++i) {
		if (!args[i].type && !args[i].size && !args[i].constset)
			return false;
	}
	return true;
}

/* number of existential constness parameters opened in the function being parsed */
static unsigned nexconst;

void
exopenreset(void)
{
	nexconst = 0;
}

/*
New types and constness for the existential parameters of a struct
value that is being destructured. The constness is not known, so what
it qualifies cannot be written, and it only converts to itself or
const.
*/
struct genarg *
exopen(struct generic *ex)
{
	static unsigned id;
	struct generic *g;
	struct genarg *args;
	char *name;
	size_t i, len;

	/* the types are only compatible with themselves, and are never substituted */
	g = mkgeneric(false);
	g->nparam = ex->nparam;
	g->params = xreallocarray(NULL, ex->nparam, sizeof(g->params[0]));
	args = xreallocarray(NULL, ex->nparam, sizeof(args[0]));
	++id;
	for (i = 0; i < ex->nparam; ++i) {
		len = strlen(ex->params[i].name) + 16;
		name = xmalloc(len);
		snprintf(name, len, "%s#%u", ex->params[i].name, id);
		g->params[i] = ex->params[i];
		g->params[i].name = name;
		memset(&args[i], 0, sizeof(args[i]));
		if (ex->params[i].kind == GENCONSTNESS) {
			if (nexconst == 16)
				error(&tok.loc, "too many values with existential constness are destructured in this function");
			g->params[i].bit = QUALXPARAM0 << nexconst++;
			args[i].qual = g->params[i].bit;
			args[i].constset = true;
			continue;
		}
		g->params[i].type = mkparamtype(g, i, name);
		args[i].type = g->params[i].type;
	}
	return args;
}

/*
The member m, at `offset`, of the struct or union of type t that r
points to. For a member that mentions existential parameters of t,
`exargs` are the types that stand for them.
*/
static struct expr *
mkmemberexpr(struct expr *r, struct type *t, struct member *m, unsigned long long offset, bool lvalue, struct genarg *exargs)
{
	struct expr *e;
	struct type *mt;
	enum typequal mq;

	mt = m->type;
	mq = m->qual;
	if (exargs) {
		mq = qualsubst(mq, t->u.structunion.exists, exargs);
		if (typehasparam(mt, t->u.structunion.exists))
			mt = typesubst(mt, &mq, t->u.structunion.exists, exargs);
	}
	mq |= r->type->qual;
	if (typedep(t) && !m->name)
		error(&tok.loc, "unnamed member of a struct depending on mono parameters cannot be accessed");
	r = mkbinaryexpr(&tok.loc, TADD, exprconvert(r, &typeulong), typedep(t) ? mklayoutexpr(LAYOUTOFFSET, t, m->name) : mkconstexpr(&typeulong, offset));
	r->type = mkpointertype(mt, mq);
	r = mkunaryexpr(TMUL, r);
	r->lvalue = lvalue;
	if (m->bits.before || m->bits.after) {
		e = mkexpr(EXPRBITFIELD, r->type, r);
		e->lvalue = lvalue;
		e->u.bitfield.bits = m->bits;
		if (typedep(t)) {
			e->u.bitfield.type = t;
			e->u.bitfield.member = m->name;
		}
		return e;
	}
	return r;
}

/* the member m of the struct or union object `obj` */
struct expr *
exprmember(struct expr *obj, struct type *t, struct member *m, unsigned long long offset, struct genarg *exargs)
{
	bool lvalue;

	lvalue = obj->lvalue;
	return mkmemberexpr(mkunaryexpr(TBAND, obj), t, m, offset, lvalue, exargs);
}

/* the data pointer of a slice, or e itself if it is not a slice */
static struct expr *
slicedata(struct expr *e)
{
	if (!typeisslice(e->type))
		return e;
	return exprmember(e, e->type, e->type->u.structunion.members, 0, NULL);
}

static struct expr *
mkcommaexpr(struct expr *first, struct expr *last)
{
	struct expr *e, **end;

	if (!first)
		return last;
	for (end = &first; *end; end = &(*end)->next)
		;
	*end = last;
	e = mkexpr(EXPRCOMMA, last->type, first);
	return e;
}

static struct expr *mkassignexpr(struct expr *, struct expr *);

/*
The slice r[lo ... hi] of a pointer, array, or slice. The bounds are
inclusive, and may be omitted: the lower bound defaults to 0, and the
upper bound to the last element of an array or slice.
*/
static struct expr *
mkslice(struct scope *s, struct expr *r, struct expr *lo, struct expr *hi)
{
	struct expr *e, *pre, **preend, *tmp, *data, *len, *lo2;
	struct type *t, *at;
	struct member *m;
	struct decl *d;
	struct init *init;

	pre = NULL;
	preend = &pre;
	lo2 = NULL;
	if (lo) {
		if (!(lo->type->prop & PROPINT))
			error(&tok.loc, "slice bound is not an integer type");
		lo = eval(exprconvert(lo, &typeulong));
		if (lo->kind == EXPRCONST) {
			lo2 = mkconstexpr(&typeulong, lo->u.constant.u);
		} else {
			/* the lower bound is used for both the pointer and the length */
			tmp = exprtemp(&typeulong);
			*preend = mkassignexpr(tmp, lo);
			preend = &(*preend)->next;
			lo = lo2 = tmp;
		}
	}
	if (hi) {
		if (!(hi->type->prop & PROPINT))
			error(&tok.loc, "slice bound is not an integer type");
		hi = exprconvert(hi, &typeulong);
		len = mkbinaryexpr(&tok.loc, TADD, hi, mkconstexpr(&typeulong, 1));
	} else {
		len = NULL;
	}
	if (typeisslice(r->type)) {
		t = r->type;
		m = t->u.structunion.members;
		if (len) {
			data = slicedata(r);
		} else {
			tmp = exprtemp(mkpointertype(t, r->qual));
			*preend = mkassignexpr(tmp, mkunaryexpr(TBAND, r));
			preend = &(*preend)->next;
			data = mkmemberexpr(tmp, t, m, 0, false, NULL);
			len = mkmemberexpr(tmp, t, m->next, m->next->offset, false, NULL);
		}
	} else {
		if (r->type->kind != TYPEPOINTER)
			error(&tok.loc, "sliced expression must be a pointer, array, or slice");
		if (r->type->base->incomplete || r->type->base->kind == TYPEFUNC)
			error(&tok.loc, "sliced pointer must be to a complete object type");
		if (!len) {
			at = r->decayed && r->base->type->kind == TYPEARRAY ? r->base->type : NULL;
			if (!at)
				error(&tok.loc, "slice of a pointer requires an upper bound");
			if (at->prop & PROPDEPLEN && !at->incomplete)
				len = exprdup(at->u.array.length);
			else if (at->u.array.length && at->u.array.length->kind == EXPRCONST)
				len = mkconstexpr(&typeulong, at->u.array.length->u.constant.u);
			else if (!at->incomplete && !(at->prop & (PROPVM|PROPDEPLEN)) && at->base->size)
				len = mkconstexpr(&typeulong, at->size / at->base->size);
			else
				error(&tok.loc, "slice of an array of unknown length requires an upper bound");
		}
		t = mkslicetype(r->type->base, r->type->qual);
		m = t->u.structunion.members;
		data = r;
	}
	if (lo) {
		data = mkbinaryexpr(&tok.loc, TADD, data, lo);
		len = mkbinaryexpr(&tok.loc, TSUB, len, lo2);
	}
	e = mkexpr(EXPRCOMPOUND, t, NULL);
	e->lvalue = true;
	d = mkdecl(NULL, DECLOBJECT, t, QUALNONE, LINKNONE);
	d->u.obj.storage = s == &filescope ? SDSTATIC : SDAUTO;
	init = mkinit(0, 8, (struct bitfield){0}, exprassign(data, m->type));
	init->next = mkinit(8, 16, (struct bitfield){0}, len);
	e->u.compound.decl = d;
	e->u.compound.init = init;
	return mkcommaexpr(pre, e);
}

/* an object initialized with the value of e, which lives until the end of the enclosing block */
static struct expr *
mktempobj(struct scope *s, struct expr *val)
{
	struct expr *e, *arr;
	struct decl *d;
	struct type *t;

	arr = exprunarray(val);
	if (arr)
		val = arr;
	t = val->type;
	e = mkexpr(EXPRCOMPOUND, t, NULL);
	e->lvalue = true;
	d = mkdecl(NULL, DECLOBJECT, t, QUALNONE, LINKNONE);
	d->u.obj.storage = s == &filescope ? SDSTATIC : SDAUTO;
	e->u.compound.decl = d;
	e->u.compound.init = mkinit(0, t->size, (struct bitfield){0}, val);
	return e;
}

struct callarg {
	/* parameter name, or NULL for a positional argument */
	char *name;
	struct expr *expr;
	/* where the argument starts */
	struct location loc;
};

static struct expr *mkcall(struct scope *, struct expr *, struct callarg *, size_t, struct type *, const struct location *);

/*
Report that the argument for the parameter p of a call, which is the
written argument `argi` or the given for an implicit parameter if that
is -1, cannot be converted to the parameter type pt.
*/
static void
argerror(const struct location *loc, struct callarg *args, size_t argi, const char *fname, struct decl *p, struct type *pt, struct expr *arg, const char *err)
{
	char what[64];
	struct type *at;

	if (argi == -1) {
		snprintf(what, sizeof(what), "the given for implicit parameter");
	} else {
		loc = &args[argi].loc;
		snprintf(what, sizeof(what), "argument %zu", argi + 1);
	}
	at = arg->type;
	if (pt->kind == TYPEARRAY && exprunarray(arg))
		at = exprunarray(arg)->type;
	softerror(loc, "%s%s%s%s has type '%s', but parameter%s%s%s has type '%s' (%s)",
		what, fname ? " of call to '" : "", fname ? fname : "", fname ? "'" : "",
		typespelling(at, QUALNONE),
		p->name ? " '" : "", p->name ? p->name : "", p->name ? "'" : "",
		typespelling(pt, QUALNONE), err);
}

/* a given that can be used for an implicit parameter */
struct givencand {
	struct decl *decl;
	/* whether the parameter is a pointer to the given */
	bool byaddr;
	/* arguments for the parameters of a forall given */
	struct genarg *args;
	/* arguments of the function being called, including those determined by this given */
	struct genarg *bind;
};

/* the type that a given provides: its own, or its result for a given function */
static struct type *
giventype(struct decl *d, enum typequal *q)
{
	if (d->kind == DECLFUNC) {
		*q = QUALNONE;
		return d->type->base;
	}
	*q = d->qual;
	return d->type;
}

/* whether t refers to a type parameter of g that has no argument in `bind` */
static bool
hasunbound(struct type *t, struct generic *g, struct genarg *bind)
{
	size_t i;

	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENTYPE && !bind[i].type && typeoccurs(t, g->params[i].type))
			return true;
	}
	return false;
}

/* whether t may refer to a type or size parameter of g that has no argument in `bind` */
static bool
notinferred(struct type *t, struct generic *g, struct genarg *bind)
{
	size_t i;

	if (hasunbound(t, g, bind))
		return true;
	for (i = 0; i < g->nparam; ++i) {
		if (g->params[i].kind == GENSIZE && !bind[i].size && typehasparam(t, g))
			return true;
	}
	return false;
}

/*
Whether the given d can be used for an implicit parameter of type pt,
either as its value or, if `byaddr` is set, as what it points to.
The parameter may refer to the parameters of the function being called,
g, which are bound in `bind` where they are known; matching the given may
determine more of them.

The types are unified without regard to constness, and the given must
then convert to the parameter. The constness parameters of a forall
given are chosen so that it does.
*/
static bool
matchgivenas(struct decl *d, struct generic *g, struct genarg *bind, struct type *pt, bool byaddr, struct givencand *c)
{
	struct unifier u;
	struct genarg *ident, *args;
	struct generic *fresh;
	struct type *ht, *want;
	enum typequal hq, q;
	size_t i;

	ht = giventype(d, &hq);
	fresh = NULL;
	ident = NULL;
	if (d->gen) {
		/* the parameters of the given are renamed, since pt may refer to them as well */
		fresh = genfresh(d->gen, &ident);
		q = QUALNONE;
		ht = typesubst(ht, &q, d->gen, ident);
	}
	u.lax = true;
	u.g[0] = g;
	u.bind[0] = NULL;
	if (g) {
		u.bind[0] = xreallocarray(NULL, g->nparam, sizeof(*bind));
		memcpy(u.bind[0], bind, g->nparam * sizeof(*bind));
	}
	u.g[1] = fresh;
	u.bind[1] = NULL;
	if (fresh) {
		u.bind[1] = xreallocarray(NULL, fresh->nparam, sizeof(*bind));
		memset(u.bind[1], 0, fresh->nparam * sizeof(*bind));
	}
	if (byaddr) {
		/* a pointer to a const given must be a pointer to const */
		if (!qualsubset(hq, pt->qual) || !unify(&u, pt->base, pt->qual, ht, hq | pt->qual))
			return false;
	} else if (!unify(&u, pt, QUALNONE, ht, QUALNONE)) {
		return false;
	}
	c->decl = d;
	c->byaddr = byaddr;
	c->args = NULL;
	args = NULL;
	if (fresh) {
		/* the type of the given must determine all of its parameters */
		args = xreallocarray(NULL, fresh->nparam, sizeof(*args));
		memset(args, 0, fresh->nparam * sizeof(*args));
		for (i = 0; i < fresh->nparam; ++i) {
			switch (fresh->params[i].kind) {
			case GENTYPE:
				if (!u.bind[1][i].type)
					return false;
				args[i].qual = u.bind[1][i].qual;
				args[i].type = unifyresolve(&u, u.bind[1][i].type, &args[i].qual);
				if (typehasparam(args[i].type, fresh) || g && hasunbound(args[i].type, g, u.bind[0]))
					return false;
				break;
			case GENSIZE:
				if (!u.bind[1][i].size)
					return false;
				args[i].size = unifyresolvesize(&u, u.bind[1][i].size);
				if (exprhasparam(args[i].size, fresh))
					return false;
				break;
			case GENCONSTNESS:
				break;
			}
		}
		c->args = args;
	}
	if (g) {
		for (i = 0; i < g->nparam; ++i) {
			if (g->params[i].kind == GENTYPE && u.bind[0][i].type && u.bind[0][i].type != g->params[i].type) {
				u.bind[0][i].type = unifyresolve(&u, u.bind[0][i].type, &u.bind[0][i].qual);
				if (fresh && typehasparam(u.bind[0][i].type, fresh))
					return false;
			} else if (g->params[i].kind == GENSIZE && u.bind[0][i].size) {
				u.bind[0][i].size = unifyresolvesize(&u, u.bind[0][i].size);
			}
		}
	}
	c->bind = u.bind[0];
	/* the type wanted of the given, now that the arguments of the call are known */
	q = QUALNONE;
	want = byaddr ? pt->base : pt;
	if (g)
		want = genpartial(g, u.bind[0], want, &q);
	if (fresh) {
		/*
		The given converts to the wanted type if its constness
		parameters are const wherever const is wanted of them, other
		than in positive positions, where the given may be less const.
		*/
		genscanconst(fresh, args, ht, want, -1);
		for (i = 0; i < fresh->nparam; ++i) {
			if (fresh->params[i].kind == GENCONSTNESS)
				args[i].constset = true;
		}
		q = QUALNONE;
		ht = typesubst(ht, &q, fresh, args);
	}
	if (typecompatible(ht, want))
		return true;
	/* through a pointer, the given is only seen as a const variant if it cannot be written */
	if (byaddr && !(pt->qual & QUALCONST))
		return false;
	return typeconstconv(ht, want);
}

static bool
matchgiven(struct decl *d, struct generic *g, struct genarg *bind, struct type *pt, struct givencand *c)
{
	if (matchgivenas(d, g, bind, pt, false, c))
		return true;
	/* a pointer parameter can also take the address of a given */
	return pt->kind == TYPEPOINTER && matchgivenas(d, g, bind, pt, true, c);
}

/* whether the type of the given p can be made the type of the given d by substituting the parameters of p */
static bool
givengeneralizes(struct decl *p, struct decl *d)
{
	struct unifier u;
	struct genarg *ident;
	struct type *pt, *dt;
	enum typequal q;

	pt = giventype(p, &q);
	dt = giventype(d, &q);
	if (!p->gen)
		return typecompatible(pt, dt);
	u.lax = false;
	u.g[0] = genfresh(p->gen, &ident);
	u.bind[0] = xreallocarray(NULL, p->gen->nparam, sizeof(*ident));
	memset(u.bind[0], 0, p->gen->nparam * sizeof(*ident));
	u.g[1] = NULL;
	u.bind[1] = NULL;
	q = QUALNONE;
	pt = typesubst(pt, &q, p->gen, ident);
	return unify(&u, pt, QUALNONE, dt, QUALNONE);
}

/*
Whether the given c is preferred to the given `other` for the same
implicit parameter: if it is more specific, in that its type can be
obtained from the type of `other` by substituting type variables, or,
between const variants, if it is more general, in that `other` converts
to it.
*/
static bool
givenbeats(struct decl *c, struct decl *other)
{
	struct type *ct, *ot;
	enum typequal q;

	if (givengeneralizes(other, c) && !givengeneralizes(c, other))
		return true;
	if (c->gen || other->gen)
		return false;
	ct = giventype(c, &q);
	ot = giventype(other, &q);
	if (typecompatible(ct, ot) || !typeconstvariant(ct, ot))
		return false;
	return typeconstconv(ot, ct) && !typeconstconv(ct, ot);
}

/* the types that are being resolved from given functions, to detect premises that never terminate */
static struct type *goals[32];
static size_t ngoals;

/*
Find the given for an implicit parameter of type pt: the one in the
innermost scope that has any, and the preferred one in that scope (see
givenbeats).
Returns the argument for the parameter.
*/
static struct expr *
resolvegiven(struct scope *s, struct generic *g, struct genarg *bind, struct type *pt, const char *func, const char *param)
{
	struct scope *sc;
	struct decl *d;
	struct array cands = {0};
	struct givencand *c, *other, *best;
	struct expr *e;
	struct type *t;
	size_t i;

	if (!param)
		param = "<unnamed>";
	for (sc = s; sc; sc = sc->parent) {
		for (d = sc->givens; d; d = d->nextgiven) {
			c = arrayadd(&cands, sizeof(*c));
			if (!matchgiven(d, g, bind, pt, c))
				cands.len -= sizeof(*c);
		}
		if (cands.len)
			break;
	}
	if (!cands.len)
		error(&tok.loc, "no given found for implicit parameter '%s' of '%s'", param, func);
	best = NULL;
	arrayforeach(&cands, c) {
		arrayforeach(&cands, other) {
			if (other != c && !givenbeats(c->decl, other->decl))
				break;
		}
		if (other == (void *)((char *)cands.val + cands.len)) {
			best = c;
			break;
		}
	}
	if (!best) {
		c = cands.val;
		error(&tok.loc, "ambiguous givens for implicit parameter '%s' of '%s': '%s' and '%s'", param, func, c[0].decl->name, c[1].decl->name);
	}
	c = best;
	if (g)
		memcpy(bind, c->bind, g->nparam * sizeof(*bind));
	d = c->decl;
	e = exprident(d);
	if (d->gen)
		genbind(e, c->args);
	if (d->kind != DECLFUNC) {
		e = c->byaddr ? mkunaryexpr(TBAND, e) : decay(e);
		free(cands.val);
		return e;
	}
	/* a given function is called, which resolves its premises in turn */
	t = e->type->base;
	for (i = 0; i < ngoals; ++i) {
		if (typecompatible(goals[i], t))
			error(&tok.loc, "resolving implicit parameter '%s' of '%s' with given function '%s' does not terminate", param, func, d->name);
	}
	if (ngoals == countof(goals))
		error(&tok.loc, "resolving implicit parameter '%s' of '%s' requires too many given functions", param, func);
	goals[ngoals++] = t;
	e = mkcall(s, decay(e), NULL, 0, NULL, &tok.loc);
	--ngoals;
	if (c->byaddr)
		e = mkunaryexpr(TBAND, mktempobj(s, e));
	free(cands.val);
	return e;
}

/*
Call the function r. Positional arguments fill the parameters that are
not implicit, in order, and named arguments fill the parameters they
name. The type arguments of a polymorphic function that were not given
are inferred from the arguments, then from the type expected of the
result (if any), then from the givens for its implicit parameters.
Implicit parameters that were not passed by name are resolved from the
givens in scope.
*/
static struct expr *
mkcall(struct scope *s, struct expr *r, struct callarg *args, size_t nargs, struct type *expected, const struct location *loc)
{
	struct decl *fd, *p, **params;
	struct generic *g;
	struct genarg *bind, *try;
	struct expr *e, **slots, **end, *a, *extra, **extraend;
	struct type *t, *at, *pt;
	enum typequal q;
	size_t i, pi, nparam, *argparam, *slotarg;
	const char *err, *fname;

	if (r->type->kind != TYPEPOINTER || r->type->base->kind != TYPEFUNC)
		error(loc, "called object is not a function");
	/* implicit parameters only apply when the function is called by name */
	fd = NULL;
	if (r->decayed && r->base->kind == EXPRIDENT && r->base->u.ident.decl->kind == DECLFUNC)
		fd = r->base->u.ident.decl;
	g = NULL;
	bind = NULL;
	if (fd && fd->gen && !argscomplete(fd->gen, r->base->u.ident.genargs)) {
		g = fd->gen;
		bind = xreallocarray(NULL, g->nparam, sizeof(*bind));
		if (r->base->u.ident.genargs)
			memcpy(bind, r->base->u.ident.genargs, g->nparam * sizeof(*bind));
		else
			memset(bind, 0, g->nparam * sizeof(*bind));
	}
	t = r->type->base;
	nparam = t->u.func.nparam;
	params = xreallocarray(NULL, nparam + 1, sizeof(*params));
	slots = xreallocarray(NULL, nparam + 1, sizeof(*slots));
	argparam = xreallocarray(NULL, nargs + 1, sizeof(*argparam));
	/* the argument written for each parameter, or -1 */
	slotarg = xreallocarray(NULL, nparam + 1, sizeof(*slotarg));
	fname = fd ? fd->name : NULL;
	for (p = t->u.func.params, pi = 0; p; p = p->next, ++pi) {
		params[pi] = p;
		slots[pi] = NULL;
		slotarg[pi] = -1;
	}
	extra = NULL;
	extraend = &extra;
	pi = 0;
	for (i = 0; i < nargs && !args[i].name; ++i) {
		while (fd && pi < nparam && params[pi]->implicit)
			++pi;
		if (pi == nparam) {
			if (!t->u.func.isvararg) {
				size_t want, got;

				for (want = 0, pi = 0; pi < nparam; ++pi)
					want += !(fd && params[pi]->implicit);
				for (got = 0; got < nargs && !args[got].name; ++got)
					;
				softerror(&args[i].loc, "too many arguments for function call%s%s%s: expected %zu, but got %zu", fname ? " to '" : "", fname ? fname : "", fname ? "'" : "", want, got);
				/* the surplus arguments are dropped */
				for (; i < nargs && !args[i].name; ++i)
					argparam[i] = -1;
				--i;
				pi = nparam;
				continue;
			}
			argparam[i] = -1;
			*extraend = args[i].expr;
			extraend = &args[i].expr->next;
			continue;
		}
		argparam[i] = pi;
		slotarg[pi] = i;
		slots[pi++] = args[i].expr;
	}
	for (; i < nargs; ++i) {
		for (pi = 0; pi < nparam; ++pi) {
			if (params[pi]->name && strcmp(params[pi]->name, args[i].name) == 0)
				break;
		}
		if (pi == nparam)
			error(&args[i].loc, "function has no parameter named '%s'", args[i].name);
		if (slots[pi])
			error(&args[i].loc, "parameter '%s' is given more than one argument", args[i].name);
		argparam[i] = pi;
		slotarg[pi] = i;
		slots[pi] = args[i].expr;
	}
	*extraend = NULL;
	if (g) {
		/* a constness parameter is const if any argument supplies const to it, and mut otherwise */
		for (i = 0; i < nargs; ++i) {
			if (argparam[i] == -1)
				continue;
			p = params[argparam[i]];
			a = args[i].expr;
			at = a->type;
			if (p->type->kind == TYPEARRAY && exprunarray(a))
				at = a->base->type;
			genscanconst(g, bind, p->type, at, 1);
		}
		for (i = 0; i < g->nparam; ++i) {
			if (g->params[i].kind == GENCONSTNESS)
				bind[i].constset = true;
		}
		/*
		A type or size parameter is bound by its first occurrence
		in the arguments, in the order they are written. An
		argument that does not agree with the parameters bound so
		far is left to be converted, below.
		*/
		for (i = 0; i < nargs; ++i) {
			if (argparam[i] == -1)
				continue;
			p = params[argparam[i]];
			a = args[i].expr;
			at = a->type;
			if (p->type->kind == TYPEARRAY && exprunarray(a))
				at = a->base->type;
			if (!genunify(g, bind, p->type, p->qual, at, QUALNONE) && notinferred(p->type, g, bind))
				error(&args[i].loc, "cannot infer type arguments of '%s' from argument %zu: it has type '%s', which is inconsistent with parameter type '%s' and the earlier arguments", fd->name, i + 1, typespelling(at, QUALNONE), typespelling(p->type, p->qual));
		}
		/* then from the type expected of the result, where that determines more */
		if (expected) {
			try = xreallocarray(NULL, g->nparam, sizeof(*try));
			memcpy(try, bind, g->nparam * sizeof(*try));
			if (genunify(g, try, t->base, QUALNONE, expected, QUALNONE))
				memcpy(bind, try, g->nparam * sizeof(*try));
			free(try);
		}
		/* the arguments must convert to the parameter types that are now known */
		for (i = 0; i < nargs; ++i) {
			if (argparam[i] == -1)
				continue;
			pi = argparam[i];
			if (notinferred(params[pi]->type, g, bind))
				continue;
			q = QUALNONE;
			pt = genpartial(g, bind, params[pi]->type, &q);
			err = assigncheck(slots[pi], pt);
			if (err) {
				argerror(loc, args, i, fname, params[pi], pt, slots[pi], err);
				slots[pi] = assignrecover(pt);
			}
		}
		/* then from the givens for the implicit parameters */
		for (pi = 0; pi < nparam; ++pi) {
			if (!slots[pi] && params[pi]->implicit)
				slots[pi] = resolvegiven(s, g, bind, params[pi]->type, fd->name, params[pi]->name);
		}
		for (i = 0; i < g->nparam; ++i) {
			if (!bind[i].type && !bind[i].size && !bind[i].constset)
				error(loc, "cannot infer %s parameter '%s' of '%s'", g->params[i].kind == GENSIZE ? "size" : g->params[i].kind == GENCONSTNESS ? "constness" : "type", g->params[i].name, fd->name);
		}
		genbind(r->base, bind);
		r->type = mkpointertype(r->base->type, QUALNONE);
		t = r->type->base;
		for (p = t->u.func.params, pi = 0; p; p = p->next, ++pi)
			params[pi] = p;
	} else if (fd) {
		for (pi = 0; pi < nparam; ++pi) {
			if (!slots[pi] && params[pi]->implicit)
				slots[pi] = resolvegiven(s, NULL, NULL, params[pi]->type, fd->name, params[pi]->name);
		}
	}
	e = mkexpr(EXPRCALL, t->base, r);
	e->u.call.args = NULL;
	e->u.call.nargs = 0;
	end = &e->u.call.args;
	for (pi = 0; pi < nparam; ++pi) {
		if (!slots[pi]) {
			if (params[pi]->name)
				softerror(loc, "not enough arguments for function call%s%s%s: no argument for parameter '%s' of type '%s'", fname ? " to '" : "", fname ? fname : "", fname ? "'" : "", params[pi]->name, typespelling(params[pi]->type, params[pi]->qual));
			else
				softerror(loc, "not enough arguments for function call%s%s%s: no argument for parameter %zu of type '%s'", fname ? " to '" : "", fname ? fname : "", fname ? "'" : "", pi + 1, typespelling(params[pi]->type, params[pi]->qual));
			slots[pi] = assignrecover(params[pi]->type);
		}
		err = assigncheck(slots[pi], params[pi]->type);
		if (err) {
			argerror(loc, args, slotarg[pi], fname, params[pi], params[pi]->type, slots[pi], err);
			a = assignrecover(params[pi]->type);
		} else {
			a = exprassign(slots[pi], params[pi]->type);
		}
		*end = a;
		end = &a->next;
		++e->u.call.nargs;
	}
	while (extra) {
		a = extra;
		extra = extra->next;
		a = exprpromote(a);
		*end = a;
		end = &a->next;
		++e->u.call.nargs;
	}
	*end = NULL;
	free(params);
	free(slots);
	free(argparam);
	free(slotarg);
	return decay(e);
}

/* TODO: merge with init.c:designator() */
static void
designator(struct scope *s, struct type *t, unsigned long long *offset)
{
	char *name;
	struct member *m;
	unsigned long long i;

	for (;;) {
		switch (tok.kind) {
		case TLBRACK:
			if (t->kind != TYPEARRAY)
				error(&tok.loc, "index designator is only valid for array types");
			next();
			i = intconstexpr(s, false);
			expect(TRBRACK, "for index designator");
			t = t->base;
			*offset += i * t->size;
			break;
		case TPERIOD:
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "member designator only valid for struct/union types");
			next();
			name = expect(TIDENT, "for member designator");
			m = typemember(t, name, offset);
			if (!m)
				error(&tok.loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", name);
			t = m->type;
			break;
		default:
			return;
		}
	}
}

static struct expr *
builtinfunc(struct scope *s, enum builtinkind kind)
{
	struct expr *e, *toeval;
	struct type *t;
	struct member *m;
	char *name;
	unsigned long long offset;

	switch (kind) {
	case BUILTINALLOCA:
		e = exprassign(assignexpr(s), &typeulong);
		e = mkexpr(EXPRBUILTIN, mkpointertype(&typevoid, QUALNONE), e);
		e->u.builtin.kind = BUILTINALLOCA;
		break;
	case BUILTINCONSTANTP:
		e = mkconstexpr(&typeint, eval(condexpr(s))->kind == EXPRCONST);
		break;
	case BUILTINEXPECT:
		/* just a no-op for now */
		/* TODO: check that the expression and the expected value have type 'long' */
		e = assignexpr(s);
		expect(TCOMMA, "after expression");
		delexpr(assignexpr(s));
		break;
	case BUILTININFF:
		e = mkexpr(EXPRCONST, &typefloat, NULL);
		/* TODO: use INFINITY here when we can handle musl's math.h */
		e->u.constant.f = strtod("inf", NULL);
		break;
	case BUILTINNANF:
		e = assignexpr(s);
		if (!e->decayed || e->base->kind != EXPRSTRING || e->base->u.string.size > 1)
			error(&tok.loc, "__builtin_nanf currently only supports empty string literals");
		e = mkexpr(EXPRCONST, &typefloat, NULL);
		/* TODO: use NAN here when we can handle musl's math.h */
		e->u.constant.f = strtod("nan", NULL);
		break;
	case BUILTINOFFSETOF:
		t = typename(s, NULL, NULL);
		expect(TCOMMA, "after type name");
		name = expect(TIDENT, "after ','");
		if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
			error(&tok.loc, "type is not a struct/union type");
		offset = 0;
		m = typemember(t, name, &offset);
		if (!m)
			error(&tok.loc, "struct/union has no member named '%s'", name);
		designator(s, m->type, &offset);
		e = mkconstexpr(&typeulong, offset);
		break;
	case BUILTINTYPESCOMPATIBLEP:
		t = typename(s, NULL, NULL);
		expect(TCOMMA, "after type name");
		e = mkconstexpr(&typeint, typecompatible(t, typename(s, NULL, NULL)));
		break;
	case BUILTINUNREACHABLE:
		e = mkexpr(EXPRBUILTIN, &typevoid, NULL);
		e->u.builtin.kind = BUILTINUNREACHABLE;
		break;
	case BUILTINVAARG:
		e = mkexpr(EXPRBUILTIN, NULL, assignexpr(s));
		e->u.builtin.kind = BUILTINVAARG;
		if (!typesame(e->base->type, typeadjvalist))
			error(&tok.loc, "va_arg argument must have type va_list");
		if (typeadjvalist == targ->typevalist)
			e->base = mkunaryexpr(TBAND, e->base);
		expect(TCOMMA, "after va_list");
		e->type = typename(s, &e->qual, &toeval);
		e->toeval = toeval;
		break;
	case BUILTINVACOPY:
		e = mkexpr(EXPRASSIGN, &typevoid, NULL);
		e->u.assign.l = assignexpr(s);
		if (!typesame(e->u.assign.l->type, typeadjvalist))
			error(&tok.loc, "va_copy destination must have type va_list");
		if (typeadjvalist != targ->typevalist)
			e->u.assign.l = mkunaryexpr(TMUL, e->u.assign.l);
		expect(TCOMMA, "after target va_list");
		e->u.assign.r = assignexpr(s);
		if (!typesame(e->u.assign.r->type, typeadjvalist))
			error(&tok.loc, "va_copy source must have type va_list");
		if (typeadjvalist != targ->typevalist)
			e->u.assign.r = mkunaryexpr(TMUL, e->u.assign.r);
		break;
	case BUILTINVAEND:
		e = assignexpr(s);
		if (!typesame(e->type, typeadjvalist))
			error(&tok.loc, "va_end argument must have type va_list");
		e = mkexpr(EXPRCAST, &typevoid, e);
		break;
	case BUILTINVASTART:
		e = mkexpr(EXPRBUILTIN, &typevoid, assignexpr(s));
		e->u.builtin.kind = BUILTINVASTART;
		if (!typesame(e->base->type, typeadjvalist))
			error(&tok.loc, "va_start argument must have type va_list");
		if (typeadjvalist == targ->typevalist)
			e->base = mkunaryexpr(TBAND, e->base);
		if (consume(TCOMMA))
			delexpr(assignexpr(s));
		break;
	default:
		fatal("internal error; unknown builtin");
	}
	return e;
}

static struct expr *
mkincdecexpr(enum tokenkind op, struct expr *base, bool post)
{
	struct expr *e;

	if (!base->lvalue)
		error(&tok.loc, "operand of '%s' operator must be an lvalue", tokenstr(op));
	if (base->qual & QUALCONSTANT)
		error(&tok.loc, "operand of '%s' operator is const qualified", tokenstr(op));
	e = mkexpr(EXPRINCDEC, base->type, base);
	e->op = op;
	e->u.incdec.post = post;
	return e;
}

static struct expr *
postfixexpr(struct scope *s, struct expr *r)
{
	struct expr *e, *arr, *idx, *tmp;
	struct type *t, *expected;
	struct member *m;
	unsigned long long offset;
	enum tokenkind op;
	bool lvalue, named;
	struct array args;
	struct callarg *arg;
	struct location callloc;

	if (!r)
		r = primaryexpr(s);
	for (;;) {
		switch (tok.kind) {
		case TLBRACK:  /* subscript or slice */
			next();
			arr = r;
			if (consume(TELLIPSIS)) {
				e = mkslice(s, arr, NULL, tok.kind == TRBRACK ? NULL : expr(s));
				expect(TRBRACK, "after slice");
				break;
			}
			idx = expr(s);
			if (consume(TELLIPSIS)) {
				e = mkslice(s, arr, idx, tok.kind == TRBRACK ? NULL : expr(s));
				expect(TRBRACK, "after slice");
				break;
			}
			arr = slicedata(arr);
			idx = slicedata(idx);
			if (arr->type->kind != TYPEPOINTER) {
				if (idx->type->kind != TYPEPOINTER)
					error(&tok.loc, "either array or index must be pointer type");
				tmp = arr;
				arr = idx;
				idx = tmp;
			}
			if (arr->type->base->incomplete)
				error(&tok.loc, "array is pointer to incomplete type");
			if (!(idx->type->prop & PROPINT))
				error(&tok.loc, "index is not an integer type");
			e = mkunaryexpr(TMUL, mkbinaryexpr(&tok.loc, TADD, arr, idx));
			expect(TRBRACK, "after array index");
			break;
		case TLPAREN:  /* function call */
			callloc = tok.loc;
			next();
			if (r->kind == EXPRIDENT && r->u.ident.decl->kind == DECLBUILTIN) {
				e = builtinfunc(s, r->u.ident.decl->u.builtin);
				expect(TRPAREN, "after builtin parameters");
				break;
			}
			if (r->type->kind != TYPEPOINTER || r->type->base->kind != TYPEFUNC)
				error(&tok.loc, "called object is not a function");
			expected = NULL;
			if (r->decayed && r->base->kind == EXPRIDENT)
				expected = r->base->u.ident.expected;
			args = (struct array){0};
			named = false;
			while (tok.kind != TRPAREN) {
				if (args.len)
					expect(TCOMMA, "or ')' after function call argument");
				arg = arrayadd(&args, sizeof(*arg));
				arg->name = NULL;
				arg->loc = tok.loc;
				if (consume(TPERIOD)) {
					arg->name = expect(TIDENT, "for argument name");
					expect(TASSIGN, "after argument name");
					named = true;
				} else if (named) {
					error(&tok.loc, "positional argument after named argument");
				}
				arg->expr = assignexpr(s);
			}
			next();
			/* the type expected of the expression only applies if the call is all of it */
			switch (tok.kind) {
			case TSEMICOLON:
			case TCOMMA:
			case TRPAREN:
			case TRBRACE:
				break;
			default:
				expected = NULL;
			}
			e = mkcall(s, r, args.val, args.len / sizeof(*arg), expected, &callloc);
			free(args.val);
			break;
		case TPERIOD:
			r = mkunaryexpr(TBAND, r);
			/* fallthrough */
		case TARROW:
			op = tok.kind;
			if (r->type->kind != TYPEPOINTER)
				error(&tok.loc, "'%s' operator must be applied to pointer to struct/union", tokenstr(op));
			t = r->type->base;
			if (t->kind != TYPESTRUCT && t->kind != TYPEUNION)
				error(&tok.loc, "'%s' operator must be applied to pointer to struct/union", tokenstr(op));
			if (t->incomplete)
				error(&tok.loc, "'%s' operator applied to incomplete struct/union type", tokenstr(op));
			next();
			if (tok.kind < TIDENT)
				error(&tok.loc, "expected identifier after '%s' operator", tokenstr(op));
			lvalue = op == TARROW || r->base->lvalue;
			offset = 0;
			m = typemember(t, tokenstr(tok.kind), &offset);
			if (!m)
				error(&tok.loc, "%s has no member named '%s'", t->kind == TYPEUNION ? "union" : "struct", tokenstr(tok.kind));
			/* each value has its own types for existential parameters, which are only named by destructuring it */
			if (t->u.structunion.exists && (typehasparam(m->type, t->u.structunion.exists) || m->qual & genconstbits(t->u.structunion.exists)))
				error(&tok.loc, "member '%s' has an existential type, so it can only be accessed by destructuring", m->name);
			e = mkmemberexpr(r, t, m, offset, lvalue, NULL);
			next();
			break;
		case TINC:
		case TDEC:
			e = mkincdecexpr(tok.kind, r, true);
			next();
			break;
		default:
			return r;
		}
		r = e;
	}
}

static struct expr *castexpr(struct scope *);

static struct expr *
unaryexpr(struct scope *s)
{
	enum tokenkind op;
	struct expr *e, *l;
	struct type *t;
	bool c5;

	op = tok.kind;
	switch (op) {
	case TINC:
	case TDEC:
		next();
		l = unaryexpr(s);
		e = mkincdecexpr(op, l, false);
		break;
	case TBAND:
	case TMUL:
		next();
		return mkunaryexpr(op, castexpr(s));
	case TADD:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPARITH))
			error(&tok.loc, "operand of unary '+' operator must have arithmetic type");
		if (e->type->prop & PROPINT)
			e = exprpromote(e);
		break;
	case TSUB:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPARITH))
			error(&tok.loc, "operand of unary '-' operator must have arithmetic type");
		if (e->type->prop & PROPINT)
			e = exprpromote(e);
		e = mkexpr(EXPRUNARY, e->type, e);
		e->op = op;
		break;
	case TBNOT:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPINT))
			error(&tok.loc, "operand of '~' operator must have integer type");
		e = exprpromote(e);
		e = mkbinaryexpr(&tok.loc, TXOR, e, mkconstexpr(e->type, -1));
		break;
	case TLNOT:
		next();
		e = castexpr(s);
		if (!(e->type->prop & PROPSCALAR))
			error(&tok.loc, "operator '!' must have scalar operand");
		e = mkbinaryexpr(&tok.loc, TEQL, e, mkconstexpr(&typeint, 0));
		break;
	case TSIZEOF:
	case TALIGNOF:
	case T__ALIGNOF__:
		/* in C5 files, sizeof requires parentheses */
		c5 = tok.c5;
		next();
		if (consume(TLPAREN)) {
			t = typename(s, NULL, NULL);
			if (t) {
				expect(TRPAREN, "after type name");
				/* might be part of a compound literal */
				if (op == TSIZEOF && tok.kind == TLBRACE)
					parseinit(s, t);
				e = NULL;
			} else {
				e = expr(s);
				expect(TRPAREN, "after expression");
				if (op == TSIZEOF)
					e = postfixexpr(s, e);
			}
		} else if (op == TSIZEOF && !c5) {
			t = NULL;
			e = unaryexpr(s);
		} else {
			error(&tok.loc, "expected '(' after '%s'", tokenstr(op));
		}
		if (!t) {
			if (e->decayed)
				e = e->base;
			if (e->kind == EXPRBITFIELD)
				error(&tok.loc, "%s operator applied to bitfield expression", tokenstr(op));
			t = e->type;
		}
		if (t->incomplete)
			error(&tok.loc, "%s operator applied to incomplete type", tokenstr(op));
		if (t->kind == TYPEFUNC)
			error(&tok.loc, "%s operator applied to function type", tokenstr(op));
		if (typedep(t)) {
			e = mklayoutexpr(op == TSIZEOF ? LAYOUTSIZE : LAYOUTALIGN, t, NULL);
		} else if (t->kind == TYPEARRAY && t->size == 0 && t->prop & PROPVM && op == TSIZEOF) {
			e = mkexpr(EXPRSIZEOF, &typeulong, e);
			e->u.szof.type = t;
		} else {
			/*
			XXX: __alignof__ is not the same as alignof on 32-bit archs
			this needs to be considered if we gain support for those archs
			*/
			e = mkconstexpr(&typeulong, op == TSIZEOF ? t->size : t->align);
		}
		break;
	default:
		e = postfixexpr(s, NULL);
	}

	return e;
}

static struct expr *
castexpr(struct scope *s)
{
	struct type *t, *ct;
	struct decl *d;
	enum typequal tq;
	struct expr *r, *e, **end, *toeval;

	ct = NULL;
	end = &r;
	while (consume(TLPAREN)) {
		tq = QUALNONE;
		t = typename(s, &tq, &toeval);
		if (!t) {
			e = expr(s);
			expect(TRPAREN, "after expression to match '('");
			e = postfixexpr(s, e);
			goto done;
		}
		expect(TRPAREN, "after type name");
		if (tok.kind == TLBRACE) {
			e = mkexpr(EXPRCOMPOUND, t, NULL);
			e->toeval = toeval;
			e->qual = tq;
			e->lvalue = true;
			d = mkdecl(NULL, DECLOBJECT, t, tq, LINKNONE);
			d->u.obj.storage = s == &filescope ? SDSTATIC : SDAUTO;
			e->u.compound.decl = d;
			e->u.compound.init = parseinit(s, t);
			e = postfixexpr(s, decay(e));
			goto done;
		}
		/* a struct or union can be cast to a const variant of its type */
		if (t != &typevoid && !(t->prop & PROPSCALAR) && t->kind != TYPESTRUCT && t->kind != TYPEUNION)
			error(&tok.loc, "cast type must be scalar, or a const variant of the operand type");
		if (ct && ct != &typevoid && !(ct->prop & t->prop & PROPSCALAR) && !typeconstvariant(t, ct))
			error(&tok.loc, "cast operand must have scalar type");
		e = mkexpr(EXPRCAST, t, NULL);
		e->toeval = toeval;
		*end = e;
		end = &e->base;
		ct = t;
	}
	e = unaryexpr(s);

done:
	if (ct && (ct->kind == TYPESTRUCT || ct->kind == TYPEUNION)) {
		if (!typeconstvariant(e->type, ct))
			error(&tok.loc, "cast to '%s' must be from a const variant of it, but the operand has type '%s'", typespelling(ct, QUALNONE), typespelling(e->type, QUALNONE));
	} else if (ct && ct != &typevoid && !(e->type->prop & PROPSCALAR)) {
		error(&tok.loc, "cast operand must have scalar type");
	}
	*end = e;
	return r;
}

static int
precedence(enum tokenkind t)
{
	switch (t) {
	case TLOR:     return 0;
	case TLAND:    return 1;
	case TBOR:     return 2;
	case TXOR:     return 3;
	case TBAND:    return 4;
	case TEQL:
	case TNEQ:     return 5;
	case TLESS:
	case TGREATER:
	case TLEQ:
	case TGEQ:     return 6;
	case TSHL:
	case TSHR:     return 7;
	case TADD:
	case TSUB:     return 8;
	case TMUL:
	case TDIV:
	case TMOD:     return 9;
	}
	return -1;
}

static struct expr *
binaryexpr(struct scope *s, struct expr *l, int i)
{
	struct expr *r;
	struct location loc;
	enum tokenkind op;
	int j, k;

	if (!l)
		l = castexpr(s);
	while ((j = precedence(tok.kind)) >= i) {
		op = tok.kind;
		loc = tok.loc;
		next();
		r = castexpr(s);
		while ((k = precedence(tok.kind)) > j)
			r = binaryexpr(s, r, k);
		l = mkbinaryexpr(&loc, op, l, r);
	}
	return l;
}

struct expr *
condexpr(struct scope *s)
{
	struct expr *e, *l, *r;
	struct type *t, *lt, *rt;
	enum typequal tq;

	e = binaryexpr(s, NULL, 0);
	if (!consume(TQUESTION))
		return e;
	l = tok.kind == TCOLON ? e : expr(s);
	expect(TCOLON, "in conditional expression");
	r = condexpr(s);

	lt = l->type;
	rt = r->type;
	if (lt == rt) {
		t = lt;
	} else if (lt->prop & PROPARITH && rt->prop & PROPARITH) {
		t = typecommonreal(lt, bitfieldwidth(l), rt, bitfieldwidth(r));
	} else if (lt == &typevoid && rt == &typevoid) {
		t = &typevoid;
	} else {
		l = eval(l);
		r = eval(r);
		if (nullpointer(l) && rt->kind == TYPEPOINTER) {
			t = rt;
		} else if (nullpointer(r) && lt->kind == TYPEPOINTER) {
			t = lt;
		} else if (lt->kind == TYPEPOINTER && rt->kind == TYPEPOINTER) {
			tq = lt->qual | rt->qual;
			lt = lt->base;
			rt = rt->base;
			if (lt == &typevoid || rt == &typevoid) {
				t = &typevoid;
			} else if (typecompatible(lt, rt)) {
				t = typecomposite(lt, rt);
			} else {
				error(&tok.loc, "operands of conditional operator must have compatible types");
			}
			t = mkpointertype(t, tq);
		} else {
			error(&tok.loc, "invalid operands to conditional operator");
		}
	}
	e = eval(e);
	if (e->kind == EXPRCONST && e->type->prop & PROPINT)
		return exprconvert(e->u.constant.u ? l : r, t);
	e = mkexpr(EXPRCOND, t, e);
	e->u.cond.t = l;
	e->u.cond.f = r;
	return e;
}

/* an unnamed object of type t with the initializer list that follows */
struct expr *
exprcompound(struct scope *s, struct type *t)
{
	struct expr *e;
	struct decl *d;

	e = mkexpr(EXPRCOMPOUND, t, NULL);
	e->lvalue = true;
	d = mkdecl(NULL, DECLOBJECT, t, QUALNONE, LINKNONE);
	d->u.obj.storage = SDAUTO;
	e->u.compound.decl = d;
	e->u.compound.init = parseinit(s, t);
	return decay(e);
}

/* whether size parameters of erased declarations may be used, as in array lengths */
bool allowerasedsize;

/* whether the value of e depends on mono or erased parameters, so is not yet known */
bool
exprdep(struct expr *e)
{
	struct expr *sub;

	if (!e)
		return false;
	switch (e->kind) {
	case EXPRLAYOUT:
	case EXPRSIZEPARAM:
		return true;
	case EXPRBINARY:
		return exprdep(e->u.binary.l) || exprdep(e->u.binary.r);
	case EXPRCOND:
		return exprdep(e->base) || exprdep(e->u.cond.t) || exprdep(e->u.cond.f);
	case EXPRCOMMA:
		for (sub = e->base; sub; sub = sub->next) {
			if (exprdep(sub))
				return true;
		}
		return false;
	case EXPRUNARY:
	case EXPRCAST:
		return exprdep(e->base);
	}
	return false;
}

/* whether e refers to a parameter of g, or of any declaration if g is NULL */
bool
exprhasparam(struct expr *e, struct generic *g)
{
	struct expr *sub;

	if (!e)
		return false;
	switch (e->kind) {
	case EXPRSIZEPARAM:
		return !g || e->u.sizeparam.gen == g;
	case EXPRLAYOUT:
		return typehasparam(e->u.layout.type, g);
	case EXPRBINARY:
		return exprhasparam(e->u.binary.l, g) || exprhasparam(e->u.binary.r, g);
	case EXPRCOND:
		return exprhasparam(e->base, g) || exprhasparam(e->u.cond.t, g) || exprhasparam(e->u.cond.f, g);
	case EXPRCOMMA:
		for (sub = e->base; sub; sub = sub->next) {
			if (exprhasparam(sub, g))
				return true;
		}
		return false;
	case EXPRUNARY:
	case EXPRCAST:
		return exprhasparam(e->base, g);
	}
	return false;
}

/* whether e refers to a parameter of a mono (or erased) declaration */
bool
exprhasparamkind(struct expr *e, bool mono)
{
	struct expr *sub;

	if (!e)
		return false;
	switch (e->kind) {
	case EXPRSIZEPARAM:
		return e->u.sizeparam.gen->ismono == mono;
	case EXPRLAYOUT:
		return mono || typehasparamkind(e->u.layout.type, mono);
	case EXPRBINARY:
		return exprhasparamkind(e->u.binary.l, mono) || exprhasparamkind(e->u.binary.r, mono);
	case EXPRCOND:
		return exprhasparamkind(e->base, mono) || exprhasparamkind(e->u.cond.t, mono) || exprhasparamkind(e->u.cond.f, mono);
	case EXPRCOMMA:
		for (sub = e->base; sub; sub = sub->next) {
			if (exprhasparamkind(sub, mono))
				return true;
		}
		return false;
	case EXPRUNARY:
	case EXPRCAST:
		return exprhasparamkind(e->base, mono);
	}
	return false;
}

/*
Parse the argument for a size parameter. It may not contain a top-level
relational, equality, or bitwise operator, so that the '>' closing the
argument list is not taken as part of it.
*/
struct expr *
sizeargexpr(struct scope *s)
{
	struct expr *e;

	e = eval(binaryexpr(s, NULL, 7));
	if (!(e->type->prop & PROPINT))
		error(&tok.loc, "size argument must have integer type");
	if (e->kind != EXPRCONST && !exprdep(e))
		error(&tok.loc, "size argument must be an integer constant expression");
	if (e->kind == EXPRCONST && e->type->u.arith.issigned && e->u.constant.u >> 63)
		error(&tok.loc, "size argument cannot be negative");
	/* fold the conversion, so that equal sizes compare equal */
	return eval(exprconvert(e, &typeulong));
}

unsigned long long
intconstexpr(struct scope *s, bool allowneg)
{
	struct expr *e;

	e = eval(condexpr(s));
	if (e->kind != EXPRCONST || !(e->type->prop & PROPINT))
		error(&tok.loc, "not an integer constant expression");
	if (!allowneg && e->type->u.arith.issigned && e->u.constant.u >> 63)
		error(&tok.loc, "integer constant expression cannot be negative");
	return e->u.constant.u;
}

static struct expr *
mkassignexpr(struct expr *l, struct expr *r)
{
	struct expr *e;

	e = mkexpr(EXPRASSIGN, l->type, NULL);
	e->u.assign.l = l;
	e->u.assign.r = exprassign(r, l->type);
	return e;
}

struct expr *
assignexpr(struct scope *s)
{
	struct expr *e, *l, *r, *tmp, *bit, *arr;
	enum tokenkind op;

	l = condexpr(s);
	if (l->kind == EXPRBINARY || l->kind == EXPRCOMMA || l->kind == EXPRCAST)
		return l;
	switch (tok.kind) {
	case TASSIGN:     op = TNONE; break;
	case TMULASSIGN:  op = TMUL;  break;
	case TDIVASSIGN:  op = TDIV;  break;
	case TMODASSIGN:  op = TMOD;  break;
	case TADDASSIGN:  op = TADD;  break;
	case TSUBASSIGN:  op = TSUB;  break;
	case TSHLASSIGN:  op = TSHL;  break;
	case TSHRASSIGN:  op = TSHR;  break;
	case TBANDASSIGN: op = TBAND; break;
	case TXORASSIGN:  op = TXOR;  break;
	case TBORASSIGN:  op = TBOR;  break;
	default:
		return l;
	}
	/* a C5 array is assigned as a whole */
	arr = exprunarray(l);
	if (arr) {
		if (op)
			error(&tok.loc, "invalid compound assignment to array");
		l = arr;
	}
	if (l->qual & QUALCONSTANT)
		softerror(&tok.loc, "assignment to const qualified object");
	else if (!l->lvalue)
		softerror(&tok.loc, "left side of assignment expression is not an lvalue");
	next();
	if (!op)
		exprexpect(l->type);
	r = assignexpr(s);
	if (!op) {
		e = mkassignexpr(l, r);
		return arr ? decay(e) : e;
	}
	/* rewrite `E1 OP= E2` as `T = &E1, *T = *T OP E2`, where T is a temporary slot */
	if (l->kind == EXPRBITFIELD) {
		bit = l;
		l = l->base;
	} else {
		bit = NULL;
	}
	tmp = mkexpr(EXPRTEMP, mkpointertype(l->type, l->qual), NULL);
	tmp->lvalue = true;
	tmp->u.temp = NULL;
	e = mkassignexpr(tmp, mkunaryexpr(TBAND, l));
	l = mkunaryexpr(TMUL, tmp);
	if (bit) {
		bit->base = l;
		l = bit;
	}
	r = mkbinaryexpr(&tok.loc, op, l, r);
	e->next = mkassignexpr(l, r);
	return mkexpr(EXPRCOMMA, l->type, e);
}

struct expr *
expr(struct scope *s)
{
	struct expr *r, *e, **end;

	end = &r;
	for (;;) {
		e = assignexpr(s);
		*end = e;
		end = &e->next;
		if (tok.kind != TCOMMA)
			break;
		next();
	}
	if (!r->next)
		return r;
	return mkexpr(EXPRCOMMA, e->type, r);
}
