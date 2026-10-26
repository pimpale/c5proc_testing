#include <assert.h>
#include <limits.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

static struct decl *tentativedefns, **tentativedefnsend = &tentativedefns;

/*
Parameters of the forall declaration being parsed, until the struct or
union it defines claims them (see tagspec), and the scope that the
declaration belongs to.
*/
static struct generic *pendinggen, *pendingexists;
static struct scope *pendinggenscope;

struct qualtype {
	struct type *type;
	enum typequal qual;
	struct expr *expr;
};

enum storageclass {
	SCNONE,

	SCTYPEDEF     = 1<<1,
	SCEXTERN      = 1<<2,
	SCSTATIC      = 1<<3,
	SCAUTO        = 1<<4,
	SCREGISTER    = 1<<5,
	SCTHREADLOCAL = 1<<6,
};

enum typespec {
	SPECNONE,

	SPECVOID     = 1<<1,
	SPECCHAR     = 1<<2,
	SPECBOOL     = 1<<3,
	SPECINT      = 1<<4,
	SPECFLOAT    = 1<<5,
	SPECDOUBLE   = 1<<6,
	SPECSHORT    = 1<<7,
	SPECLONG     = 1<<8,
	SPECLONG2    = 1<<9,
	SPECSIGNED   = 1<<10,
	SPECUNSIGNED = 1<<11,
	SPECCOMPLEX  = 1<<12,
	SPECBITINT   = 1<<13,

	SPECLONGLONG = SPECLONG|SPECLONG2,
};

enum funcspec {
	FUNCNONE,

	FUNCINLINE   = 1<<1,
	FUNCNORETURN = 1<<2,
};

struct structbuilder {
	struct type *type;
	struct member **last;
	struct structitem **lastitem;
	unsigned bits;  /* number of bits remaining in the last byte */
	bool pack;
};

static void placemember(struct structbuilder *, struct member *, struct type *, char *, int, unsigned long long);

struct decl *
mkdecl(char *name, enum declkind k, struct type *t, enum typequal tq, enum linkage linkage)
{
	struct decl *d;

	d = xmalloc(sizeof(*d));
	memset(d, 0, sizeof(*d));
	d->name = name;
	d->kind = k;
	d->linkage = linkage;
	d->type = t;
	d->qual = tq;
	if (k == DECLOBJECT && t)
		d->u.obj.align = t->align;

	return d;
}

/* 6.7.1 Storage-class specifiers */
static int
storageclass(enum storageclass *sc)
{
	enum storageclass allowed, new;

	switch (tok.kind) {
	case TTYPEDEF:       new = SCTYPEDEF;     break;
	case TEXTERN:        new = SCEXTERN;      break;
	case TSTATIC:        new = SCSTATIC;      break;
	case TTHREAD_LOCAL:  new = SCTHREADLOCAL; break;
	case TAUTO:          new = SCAUTO;        break;
	case TREGISTER:      new = SCREGISTER;    break;
	default: return 0;
	}
	if (!sc)
		error(&tok.loc, "storage class not allowed in this declaration");
	switch (*sc & ~SCAUTO) {
	case SCNONE:        allowed = ~SCNONE;           break;
	case SCTHREADLOCAL: allowed = SCSTATIC|SCEXTERN; break;
	case SCSTATIC:
	case SCEXTERN:      allowed = SCTHREADLOCAL;     break;
	default:            allowed = SCNONE;            break;
	}
	/* C23 6.7.1p2: auto may appear with any storage-class specifier except typedef */
	if (new == SCAUTO)
		allowed = *sc & (SCAUTO|SCTYPEDEF) ? SCNONE : SCAUTO;
	else if (*sc & SCAUTO && new == SCTYPEDEF)
		allowed = SCNONE;
	if (new & ~allowed)
		error(&tok.loc, "invalid combination of storage class specifiers");
	*sc |= new;
	next();

	return 1;
}

/* 6.7.3 Type qualifiers */
static int
typequal(struct scope *s, enum typequal *tq)
{
	struct decl *d;

	switch (tok.kind) {
	case TCONST:    *tq |= QUALCONST;    break;
	case TVOLATILE: *tq |= QUALVOLATILE; break;
	case TRESTRICT: *tq |= QUALRESTRICT; break;
	case T_ATOMIC: error(&tok.loc, "_Atomic type qualifier is not yet supported");
	default:
		/* constness parameter */
		if (tok.kind < TIDENT)
			return 0;
		d = scopegetdecl(s, tokenstr(tok.kind), true);
		if (!d || d->kind != DECLCONST || !d->gen || d->gen->params[d->u.enumconst].kind != GENCONSTNESS)
			return 0;
		*tq |= d->gen->params[d->u.enumconst].bit;
	}
	next();

	return 1;
}

/* 6.7.4 Function specifiers */
static int
funcspec(enum funcspec *fs)
{
	enum funcspec new;

	switch (tok.kind) {
	case TINLINE:    new = FUNCINLINE;   break;
	case T_NORETURN: new = FUNCNORETURN; break;
	default: return 0;
	}
	if (!fs)
		error(&tok.loc, "function specifier not allowed in this declaration");
	*fs |= new;
	next();

	return 1;
}

static void structdecl(struct scope *, struct structbuilder *);
static struct qualtype declspecs(struct scope *, enum storageclass *, enum funcspec *, int *);

static struct type *
tagspec(struct scope *s)
{
	static struct type *const inttypes[][2] = {
		{&typeuint, &typeint},
		{&typeulong, &typelong},
		{&typeullong, &typellong},
	};
	struct type *t, *et;
	char *tag, *name;
	enum typekind kind;
	struct decl *d, *enumconsts;
	struct expr *e;
	struct attr a;
	enum attrkind allowedattr;
	struct structbuilder b;
	struct generic *gen, *ex;
	struct scope *ts;
	enum typequal tq;
	unsigned long long value, max, min;
	bool sign;
	int i;

	allowedattr = 0;
	switch (tok.kind) {
	case TSTRUCT: kind = TYPESTRUCT, allowedattr |= ATTRPACKED; break;
	case TUNION:  kind = TYPEUNION, allowedattr |= ATTRPACKED; break;
	case TENUM:   kind = TYPEENUM; break;
	default: fatal("internal error: unknown tag kind");
	}
	next();
	a.kind = 0;
	attr(&a, allowedattr);
	gnuattr(&a, allowedattr);
	tag = 0;
	t = NULL;
	et = NULL;
	if (tok.kind >= TIDENT) {
		tag = tokenstr(tok.kind);
		next();
	}
	if (kind == TYPEENUM && consume(TCOLON)) {
		et = declspecs(s, NULL, NULL, NULL).type;
		if (!et)
			error(&tok.loc, "no type in enum type specifier");
	}
	/* a struct or union defined by a forall or exists declaration is polymorphic */
	gen = NULL;
	ex = NULL;
	ts = s;
	if ((pendinggen || pendingexists) && kind != TYPEENUM && (tok.kind == TLBRACE || tok.kind == TSEMICOLON)) {
		gen = pendinggen;
		ex = pendingexists;
		pendinggen = NULL;
		pendingexists = NULL;
		if (tag)
			ts = pendinggenscope;
	}
	if (tag)
		t = scopegettag(ts, tag, tok.kind != TLBRACE && tok.kind != TSEMICOLON);
	if (t) {
		if (t->kind != kind)
			error(&tok.loc, "redeclaration of tag '%s' with different kind", tag);
		if (gen || ex)
			error(&tok.loc, "redeclaration of tag '%s' with forall or exists", tag);
		if (kind != TYPEENUM && t->u.structunion.gen && tok.kind != TLBRACE) {
			if (tok.kind == TLESS)
				t = geninst(t->u.structunion.gen, genargs(s, t->u.structunion.gen, false), &tq);
			else if (tok.kind != TSEMICOLON)
				error(&tok.loc, "%s '%s' requires type arguments", kind == TYPESTRUCT ? "struct" : "union", tag);
		}
	} else {
		if (kind == TYPEENUM) {
			t = mktype(kind, PROPSCALAR|PROPARITH|PROPREAL|PROPINT);
			t->base = et;
		} else {
			t = mktype(kind, 0);
			t->size = 0;
			t->align = 0;
			t->u.structunion.tag = tag;
			t->u.structunion.members = NULL;
			if (gen) {
				gen->pattern = t;
				gen->name = tag;
				t->u.structunion.gen = gen;
				t->u.structunion.genargs = genidentity(gen);
			}
			if (ex) {
				ex->name = tag;
				t->u.structunion.exists = ex;
			}
		}
		t->incomplete = true;
		if (tag)
			scopeputtag(ts, tag, t);
	}
	if (tok.kind != TLBRACE)
		return t;
	if (!t->incomplete)
		error(&tok.loc, "redefinition of tag '%s'", tag);
	next();
	switch (t->kind) {
	case TYPESTRUCT:
	case TYPEUNION:
		b.type = t;
		b.last = &t->u.structunion.members;
		b.lastitem = &t->u.structunion.items;
		b.bits = 0;
		b.pack = a.kind & ATTRPACKED;
		t->u.structunion.packed = b.pack;
		do structdecl(s, &b);
		while (tok.kind != TRBRACE);
		if (!t->u.structunion.members)
			error(&tok.loc, "struct/union has no members");
		next();
		if (!b.pack)
			t->size = ALIGNUP(t->size, t->align);
		break;
	case TYPEENUM:
		enumconsts = NULL;
		if (et) {
			t->size = t->base->size;
			t->align = t->base->align;
			t->u.arith.issigned = t->base->u.arith.issigned;
			t->u.arith.width = t->base->u.arith.width;
			t->incomplete = false;
			et = t;
		} else {
			et = &typeint;
		}
		max = 0;
		min = 0;
		for (value = 0; tok.kind >= TIDENT; ++value) {
			name = tokenstr(tok.kind);
			next();
			attr(NULL, 0);
			if (consume(TASSIGN)) {
				e = eval(condexpr(s));
				if (e->kind != EXPRCONST || !(e->type->prop & PROPINT))
					error(&tok.loc, "expected integer constant expression");
				value = e->u.constant.u;
				if (!t->base)
					et = typehasint(&typeint, value, e->type->u.arith.issigned) ? &typeint : e->type;
				else if (!typehasint(et, value, e->type->u.arith.issigned))
					goto invalid;
			} else if (value == 0 && !et->u.arith.issigned || value == 1ull << 63 && et->u.arith.issigned) {
				error(&tok.loc, "no %ssigned integer type can represent enumerator value", et->u.arith.issigned ? "" : "un");
			} else if (!typehasint(et, value, et->u.arith.issigned)) {
				if (t->base) {
				invalid:
					/* fixed underlying type */
					error(&tok.loc, "enumerator '%s' value cannot be represented in underlying type", name);
				}
				sign = et->u.arith.issigned;
				for (i = 0; i < countof(inttypes); ++i) {
					et = inttypes[i][sign];
					if (typehasint(et, value, sign))
						break;
				}
				assert(i < countof(inttypes));
			}
			d = mkdecl(name, DECLCONST, et, QUALNONE, LINKNONE);
			d->u.enumconst = value;
			d->value = mkintconst(value);
			d->next = enumconsts;
			enumconsts = d;
			if (et->u.arith.issigned && value >= 1ull << 63) {
				if (-value > min)
					min = -value;
			} else if (value > max) {
				max = value;
			}
			scopeputdecl(s, d);
			if (!consume(TCOMMA))
				break;
		}
		expect(TRBRACE, "to close enum specifier");
		if (!t->base) {
			if (min <= 0x80000000 && max <= 0x7fffffff) {
				t->base = min ? &typeint : &typeuint;
			} else {
				sign = min > 0;
				for (i = 0; i < countof(inttypes); ++i) {
					et = inttypes[i][sign];
					if (typehasint(et, max, false) && typehasint(et, -min, true))
						break;
				}
				if (i == countof(inttypes))
					error(&tok.loc, "no integer type can represent all enumerator values");
				t->base = et;
				for (d = enumconsts; d; d = d->next)
					d->type = t;
			}
			t->size = t->base->size;
			t->align = t->base->align;
			t->u.arith.issigned = t->base->u.arith.issigned;
			t->u.arith.width = t->base->u.arith.width;
		}
	}
	t->incomplete = false;

	return t;
}

/* 6.7 Declarations */
static struct qualtype
declspecs(struct scope *s, enum storageclass *sc, enum funcspec *fs, int *align)
{
	struct type *t, *other;
	struct decl *d;
	struct expr *e;
	enum typespec ts = SPECNONE;
	enum typequal tq = QUALNONE;
	enum tokenkind op;
	int ntypes = 0;
	unsigned long long i, bits;
	struct expr *typeofexpr = NULL;

	t = NULL;
	if (sc)
		*sc = SCNONE;
	if (fs)
		*fs = FUNCNONE;
	if (align)
		*align = 0;
	for (;;) {
		if (typequal(s, &tq) || storageclass(sc) || funcspec(fs))
			continue;
		op = tok.kind;
		switch (op) {
		/* 6.7.2 Type specifiers */
		case TVOID:
			t = &typevoid;
			++ntypes;
			next();
			break;
		case TCHAR:
			ts |= SPECCHAR;
			++ntypes;
			next();
			break;
		case TSHORT:
			if (ts & SPECSHORT)
				error(&tok.loc, "duplicate 'short'");
			ts |= SPECSHORT;
			next();
			break;
		case TINT:
			ts |= SPECINT;
			++ntypes;
			next();
			break;
		case TLONG:
			if (ts & SPECLONG2)
				error(&tok.loc, "too many 'long'");
			if (ts & SPECLONG)
				ts |= SPECLONG2;
			ts |= SPECLONG;
			next();
			break;
		case TFLOAT:
			ts |= SPECFLOAT;
			++ntypes;
			next();
			break;
		case TDOUBLE:
			ts |= SPECDOUBLE;
			++ntypes;
			next();
			break;
		case TSIGNED:
			if (ts & SPECSIGNED)
				error(&tok.loc, "duplicate 'signed'");
			ts |= SPECSIGNED;
			next();
			break;
		case TUNSIGNED:
			if (ts & SPECUNSIGNED)
				error(&tok.loc, "duplicate 'unsigned'");
			ts |= SPECUNSIGNED;
			next();
			break;
		case T_BITINT:
			ts |= SPECBITINT;
			++ntypes;
			next();
			expect(TLPAREN, "after _BitInt");
			bits = intconstexpr(s, false);
			expect(TRPAREN, "after _BitInt width");
			break;
		case TBOOL:
			t = &typebool;
			++ntypes;
			next();
			break;
		case T_COMPLEX:
			error(&tok.loc, "_Complex is not yet supported");
			break;
		case T_ATOMIC:
			error(&tok.loc, "_Atomic is not yet supported");
			break;
		case TSTRUCT:
		case TUNION:
		case TENUM:
			t = tagspec(s);
			++ntypes;
			break;
		case TTYPEOF:
		case TTYPEOF_UNQUAL:
			next();
			expect(TLPAREN, "after 'typeof'");
			t = typename(s, &tq, &typeofexpr);
			if (!t) {
				e = expr(s);
				if (e->decayed)
					e = e->base;
				t = e->type;
				if (op == TTYPEOF)
					tq |= e->qual;
				if (t->prop & PROPVM)
					typeofexpr = e;
			}
			++ntypes;
			expect(TRPAREN, "to close 'typeof'");
			break;

		/* 6.7.5 Alignment specifier */
		case TALIGNAS:
			if (!align)
				error(&tok.loc, "alignment specifier not allowed in this declaration");
			next();
			expect(TLPAREN, "after 'alignas'");
			other = typename(s, NULL, NULL);
			i = other ? other->align : intconstexpr(s, false);
			if (i & i - 1 || i > INT_MAX)
				error(&tok.loc, "invalid alignment: %llu", i);
			if (i > *align)
				*align = i;
			expect(TRPAREN, "to close 'alignas' specifier");
			break;

		case T__ATTRIBUTE__:
			gnuattr(NULL, 0);
			break;

		default:
			if (op < TIDENT || t || ts)
				goto done;
			d = scopegetdecl(s, tokenstr(tok.kind), 1);
			if (!d || d->kind != DECLTYPE)
				goto done;
			t = d->type;
			tq |= d->qual;
			++ntypes;
			next();
			if (d->gen) {
				if (tok.kind != TLESS)
					error(&tok.loc, "typedef '%s' requires type arguments", d->name);
				t = geninst(d->gen, genargs(s, d->gen, false), &tq);
			}
			break;
		}
		if (ntypes > 1 || (t && ts))
			error(&tok.loc, "multiple types in declaration specifiers");
	}
done:
	switch ((int)ts) {
	case SPECNONE:                                            break;
	case SPECCHAR:                          t = &typechar;    break;
	case SPECSIGNED|SPECCHAR:               t = &typeschar;   break;
	case SPECUNSIGNED|SPECCHAR:             t = &typeuchar;   break;
	case SPECSHORT:
	case SPECSHORT|SPECINT:
	case SPECSIGNED|SPECSHORT:
	case SPECSIGNED|SPECSHORT|SPECINT:      t = &typeshort;   break;
	case SPECUNSIGNED|SPECSHORT:
	case SPECUNSIGNED|SPECSHORT|SPECINT:    t = &typeushort;  break;
	case SPECINT:
	case SPECSIGNED:
	case SPECSIGNED|SPECINT:                t = &typeint;     break;
	case SPECUNSIGNED:
	case SPECUNSIGNED|SPECINT:              t = &typeuint;    break;
	case SPECLONG:
	case SPECLONG|SPECINT:
	case SPECSIGNED|SPECLONG:
	case SPECSIGNED|SPECLONG|SPECINT:       t = &typelong;    break;
	case SPECUNSIGNED|SPECLONG:
	case SPECUNSIGNED|SPECLONG|SPECINT:     t = &typeulong;   break;
	case SPECLONGLONG:
	case SPECLONGLONG|SPECINT:
	case SPECSIGNED|SPECLONGLONG:
	case SPECSIGNED|SPECLONGLONG|SPECINT:   t = &typellong;   break;
	case SPECUNSIGNED|SPECLONGLONG:
	case SPECUNSIGNED|SPECLONGLONG|SPECINT: t = &typeullong;  break;
	case SPECBITINT:
	case SPECBITINT|SPECSIGNED:             t = mkbitinttype(bits, true); break;
	case SPECBITINT|SPECUNSIGNED:           t = mkbitinttype(bits, false); break;
	case SPECFLOAT:                         t = &typefloat;   break;
	case SPECDOUBLE:                        t = &typedouble;  break;
	case SPECLONG|SPECDOUBLE:               t = &typeldouble; break;
	default:
		error(&tok.loc, "invalid combination of type specifiers");
	}
	if (tq & QUALRESTRICT) {
		/* C23 6.7.4.1p2 */
		other = t;
		while (other->kind == TYPEARRAY)
			other = other->base;
		if (!other || other->kind != TYPEPOINTER)
			error(&tok.loc, "'restrict' applied to non-pointer type");
		if (other->base->kind == TYPEFUNC)
			error(&tok.loc, "'restrict' applied to function pointer");
	}
	/* C23 6.7.10 Type inference */
	if (!t && sc && *sc & SCAUTO)
		t = &typeauto;
	if (!t && (tq || sc && *sc || fs && *fs))
		error(&tok.loc, "declaration has no type specifier");
	/*
	TODO: consider delaying attribute parsing to declarator(),
	so we can tell the difference between the start of an
	attribute and an array declarator.
	*/
	attr(NULL, 0);

	return (struct qualtype){t, tq, typeofexpr};
}

/* 6.7.6 Declarators */
static struct decl *parameter(struct scope *);

static bool
istypename(struct scope *s, const char *name)
{
	struct decl *d;

	d = scopegetdecl(s, name, 1);
	return d && d->kind == DECLTYPE;
}

/*
When parsing a declarator, qualifiers for derived types are temporarily
stored in the `qual` field of the type itself (elsewhere this field
is used for the qualifiers of the base type). This is corrected in
declarator().
*/
static void
declaratortypes(struct scope *s, struct list *result, char **name, int *align, struct scope **funcscope, bool allowabstract)
{
	struct list *ptr;
	struct type *t;
	struct decl *d, **paramend;
	struct expr *e;
	struct attr a;
	enum typequal tq;
	int allowedattr;

	while (consume(TMUL)) {
		attr(NULL, 0);
		tq = QUALNONE;
		while (typequal(s, &tq))
			;
		t = mkpointertype(NULL, tq);
		listinsert(result, &t->link);
	}
	if (name)
		*name = NULL;
	a.kind = 0;
	ptr = result->next;
	switch (tok.kind) {
	case TLPAREN:
		next();
		if (allowabstract) {
			switch (tok.kind) {
			case TMUL:
			case TLPAREN:
				break;
			default:
				if (tok.kind >= TIDENT && !istypename(s, tokenstr(tok.kind)))
					break;
				goto func;
			}
		}
		declaratortypes(s, result, name, align, funcscope, allowabstract);
		expect(TRPAREN, "after parenthesized declarator");
		allowedattr = -1;
		break;
	default:
		if (tok.kind >= TIDENT) {
			if (!name)
				error(&tok.loc, "identifier not allowed in abstract declarator");
			*name = tokenstr(tok.kind);
			next();
		} else if (!allowabstract) {
			error(&tok.loc, "expected '(' or identifier");
		}
		/*
		the aligned attribute is used in the definition of
		max_align_t from gcc/clang (used with glibc),
		dragonflybsd, freebsd, and openbsd
		*/
		allowedattr = align ? ATTRALIGNED : 0;
	}
	for (;;) {
		switch (tok.kind) {
		case TLPAREN:  /* function declarator */
			next();
		func:
			t = mktype(TYPEFUNC, 0);
			t->qual = QUALNONE;
			t->u.func.isvararg = false;
			t->u.func.params = NULL;
			t->u.func.nparam = 0;
			paramend = &t->u.func.params;
			s = mkscope(s);
			d = NULL;
			do {
				if (consume(TELLIPSIS)) {
					t->u.func.isvararg = true;
					break;
				}
				if (tok.kind == TRPAREN)
					break;
				d = parameter(s);
				if (d->name)
					scopeputdecl(s, d);
				*paramend = d;
				paramend = &d->next;
				++t->u.func.nparam;
			} while (consume(TCOMMA));
			expect(TRPAREN, "to close function declarator");
			if (funcscope && ptr->prev == result) {
				/* we may need to re-open the scope later if this is a function definition */
				*funcscope = s;
				s = s->parent;
			} else {
				s = delscope(s);
			}
			if (t->u.func.nparam == 1 && !t->u.func.isvararg && d->type->kind == TYPEVOID && !d->name) {
				t->u.func.params = NULL;
				t->u.func.nparam = 0;
			}
			listinsert(ptr->prev, &t->link);
			allowedattr = 0;
			break;
		case TLBRACK:  /* array declarator */
			if (allowedattr != -1 && attr(&a, allowedattr))
				goto attr;
			next();
			t = mkarraytype(NULL, QUALNONE, 0);
			while (consume(TSTATIC) || typequal(s, &t->u.array.ptrqual))
				;
			if (tok.kind == TMUL && peek(TRBRACK)) {
				t->prop |= PROPVM;
				t->incomplete = false;
			} else if (!consume(TRBRACK)) {
				allowerasedsize = true;
				e = assignexpr(s);
				allowerasedsize = false;
				if (!(e->type->prop & PROPINT))
					error(&tok.loc, "array length expression must have integer type");
				t->u.array.length = e;
				t->incomplete = false;
				expect(TRBRACK, "after array length");
			}
			listinsert(ptr->prev, &t->link);
			allowedattr = 0;
			break;
		case T__ATTRIBUTE__:
			if (allowedattr == -1)
				error(&tok.loc, "attribute not allowed after parenthesized declarator");
			gnuattr(&a, allowedattr);
		attr:
			/* attribute applies to identifier if ptr->prev == result, otherwise type ptr->prev */
			if (ptr->prev == result) {
				if (a.kind & ATTRALIGNED && a.align > *align)
					*align = a.align;
			}
			break;
		default:
			return;
		}
	}
}

static struct qualtype
declarator(struct scope *s, struct qualtype base, char **name, int *align, struct scope **funcscope, bool allowabstract)
{
	struct type *t;
	enum typequal tq;
	struct expr *e;
	struct list result = {&result, &result}, *l, *prev;

	if (funcscope)
		*funcscope = NULL;
	declaratortypes(s, &result, name, align, funcscope, allowabstract);
	for (l = result.prev; l != &result; l = prev) {
		prev = l->prev;
		t = listelement(l, struct type, link);
		tq = t->qual;
		t->base = base.type;
		t->qual = base.qual;
		t->prop |= base.type->prop & PROPVM;
		switch (t->kind) {
		case TYPEFUNC:
			if (base.type->kind == TYPEFUNC)
				error(&tok.loc, "function declarator specifies function return type");
			if (base.type->kind == TYPEARRAY)
				error(&tok.loc, "function declarator specifies array return type");
			break;
		case TYPEARRAY:
			if (base.type->incomplete)
				error(&tok.loc, "array element has incomplete type");
			if (base.type->kind == TYPEFUNC)
				error(&tok.loc, "array element has function type");
			if (t->u.array.ptrqual) {
				/* TODO: check if we are in a function prototype
				if (?)
					error(&tok.loc, "array type has qualifiers outside of a function prototype");
				*/
				if (prev != &result)
					error(&tok.loc, "nested array type has qualifiers");
			}
			t->align = base.type->align;
			t->size = 0;
			if (t->u.array.length) {
				e = eval(t->u.array.length);
				if (e->kind == EXPRCONST && typedep(base.type)) {
					/* the size is computed when the element type is known */
					if (e->type->u.arith.issigned && e->u.constant.u >> 63)
						error(&tok.loc, "array length must be non-negative");
					t->u.array.length = e;
				} else if (exprdep(e)) {
					/* the length is computed for each instance, or never known if it is erased */
					t->prop |= PROPDEPLEN;
					t->u.array.length = e;
					if (exprhasparamkind(e, false))
						t->incomplete = true;
				} else if (e->kind == EXPRCONST && base.type->size) {
					if (e->type->u.arith.issigned && e->u.constant.u >> 63)
						error(&tok.loc, "array length must be non-negative");
					if (e->u.constant.u > ULLONG_MAX / base.type->size)
						error(&tok.loc, "array length is too large");
					t->size = base.type->size * e->u.constant.u;
				} else {
					t->prop |= PROPVM;
					t->u.array.length = e;
					t->u.array.size = NULL;
				}
			}
			break;
		}
		base.type = t;
		base.qual = tq;
	}

	return base;
}

static struct decl *
parameter(struct scope *s)
{
	struct decl *d;
	char *name;
	struct qualtype t;
	enum storageclass sc;

	attr(NULL, 0);
	t = declspecs(s, &sc, NULL, NULL);
	if (!t.type)
		error(&tok.loc, "no type in parameter declaration");
	if (sc && sc != SCREGISTER)
		error(&tok.loc, "parameter declaration has invalid storage-class specifier");
	t = declarator(s, t, &name, NULL, NULL, true);
	t.type = typeadjust(t.type, &t.qual);
	d = mkdecl(name, DECLOBJECT, t.type, t.qual, LINKNONE);
	d->u.obj.storage = SDAUTO;
	return d;
}

static void
addmember(struct structbuilder *b, struct qualtype mt, char *name, int align, unsigned long long width)
{
	struct type *t = b->type;
	struct member *m;
	struct structitem *item;

	if (t->kind == TYPESTRUCT && t->prop & PROPFLEX)
		error(&tok.loc, "struct has member '%s' after flexible array member", name);
	if (mt.type->incomplete) {
		if (mt.type->kind != TYPEARRAY)
			error(&tok.loc, "struct member '%s' has incomplete type", name);
		t->prop |= PROPFLEX;
	}
	if (mt.type->prop & PROPFLEX) {
		/*
		ISO C doesn't allow structures with members containing
		FAMs, but allow it as an extension
		*/
		t->prop |= PROPFLEX;
	}
	if (mt.type->kind == TYPEFUNC)
		error(&tok.loc, "struct member '%s' has function type", name);
	if (mt.type->prop & PROPVM)
		error(&tok.loc, "struct member '%s' has variably modified type", name);
	if (mt.type->kind == TYPEPARAM && mt.type->u.param.gen == t->u.structunion.exists) {
		/*
		A mono existential parameter can be the type of the last
		member, which is unsized like a flexible array member.
		*/
		if (!mt.type->u.param.gen->ismono)
			error(&tok.loc, "struct member '%s' has incomplete type", name);
		if (t->kind != TYPESTRUCT || !align)
			error(&tok.loc, "member '%s' with existential type must be in a struct and have an alignment specifier", name);
		m = xmalloc(sizeof(*m));
		m->type = mt.type;
		m->qual = mt.qual;
		m->name = name;
		m->next = NULL;
		m->bits = (struct bitfield){0};
		m->offset = ALIGNUP(t->size, align);
		t->size = m->offset;
		if (t->align < align)
			t->align = align;
		*b->last = m;
		b->last = &m->next;
		t->prop |= PROPFLEX;
		return;
	}
	/* the layout of a mono struct is computed for each instance */
	if (typedep(mt.type) && !(t->u.structunion.gen && t->u.structunion.gen->ismono))
		error(&tok.loc, "member '%s' with type depending on mono parameters requires a mono forall %s", name, t->kind == TYPESTRUCT ? "struct" : "union");
	assert(mt.type->align > 0 || typedep(mt.type));
	if (name || width == -1) {
		m = xmalloc(sizeof(*m));
		m->type = mt.type;
		m->qual = mt.qual;
		m->name = name;
		m->next = NULL;
		*b->last = m;
		b->last = &m->next;
	} else {
		m = NULL;
	}
	if (t->u.structunion.gen && t->u.structunion.gen->ismono) {
		item = xmalloc(sizeof(*item));
		item->member = m;
		item->type = mt.type;
		item->align = align;
		item->width = width;
		item->next = NULL;
		*b->lastitem = item;
		b->lastitem = &item->next;
	}
	placemember(b, m, mt.type, name, align, width);
}

/* place a member (or unnamed bit-field, if m is NULL) in the struct being built */
static void
placemember(struct structbuilder *b, struct member *m, struct type *mt, char *name, int align, unsigned long long width)
{
	struct type *t = b->type;
	size_t end;

	if (width == -1) {
		m->bits.before = 0;
		m->bits.after = 0;
		if (align < mt->align) {
			if (align)
				error(&tok.loc, "specified alignment of struct member '%s' is less strict than is required by type", name);
			align = b->pack ? 1 : mt->align;
		}
		if (!align)
			align = 1;
		if (t->kind == TYPESTRUCT) {
			m->offset = ALIGNUP(t->size, align);
			t->size = m->offset + mt->size;
		} else {
			m->offset = 0;
			if (t->size < mt->size)
				t->size = mt->size;
		}
		b->bits = 0;
	} else {  /* bit-field */
		if (!(mt->prop & PROPINT))
			error(&tok.loc, "bit-field '%s' has invalid type", name);
		if (align)
			error(&tok.loc, "alignment specified for bit-field '%s'", name);
		if (b->pack)
			error(&tok.loc, "bit-field '%s' in packed struct is not supported", name);
		if (!width && name)
			error(&tok.loc, "bit-field '%s' with zero width must not have declarator", name);
		if (width > mt->u.arith.width)
			error(&tok.loc, "bit-field '%s' exceeds width of underlying type", name);
		align = mt->align;
		if (t->kind == TYPESTRUCT) {
			/* calculate end of the storage-unit for this bit-field */
			end = ALIGNUP(t->size, mt->size);
			if (!width || width > (end - t->size) * 8 + b->bits) {
				/* no room, allocate a new storage-unit */
				t->size = end;
				b->bits = 0;
			}
			if (m) {
				m->offset = ALIGNDOWN(t->size - !!b->bits, mt->size);
				m->bits.before = (t->size - m->offset) * 8 - b->bits;
				m->bits.after = mt->size * 8 - width - m->bits.before;
			}
			t->size += (width - b->bits + 7) / 8;
			b->bits = (b->bits - width) % 8;
		} else if (m) {
			m->offset = 0;
			m->bits.before = 0;
			m->bits.after = mt->size * 8 - width;
			if (t->size < mt->size)
				t->size = mt->size;
		}
	}
	if (m && t->align < align)
		t->align = align;
}

/*
In a mono function, a static assertion depending on the type parameters
is checked for each instance, so it is added to `end`.
*/
static bool
staticassert(struct scope *s, struct stmt ***end)
{
	struct stringlit msg;
	struct location loc;
	struct expr *e;
	struct stmt *st;
	unsigned long long c;

	if (!consume(TSTATIC_ASSERT))
		return false;
	expect(TLPAREN, "after static_assert");
	loc = tok.loc;
	e = eval(condexpr(s));
	if (end && exprdep(e)) {
		st = addstmt(end, STMTSTATICASSERT);
		st->u.staticassert.cond = e;
		st->u.staticassert.loc = loc;
		if (consume(TCOMMA)) {
			tokencheck(&tok, TSTRINGLIT, "after static assertion expression");
			stringconcat(&st->u.staticassert.msg, true);
			st->u.staticassert.hasmsg = true;
		}
		expect(TRPAREN, "after static assertion");
		expect(TSEMICOLON, "after static assertion");
		return true;
	}
	if (e->kind != EXPRCONST || !(e->type->prop & PROPINT))
		error(&tok.loc, "not an integer constant expression");
	c = e->u.constant.u;
	if (consume(TCOMMA)) {
		tokencheck(&tok, TSTRINGLIT, "after static assertion expression");
		stringconcat(&msg, true);
		if (!c)
			error(&tok.loc, "static assertion failed: %.*s", (int)(msg.size - 1), (char *)msg.data);
	} else if (!c) {
		error(&tok.loc, "static assertion failed");
	}
	expect(TRPAREN, "after static assertion");
	expect(TSEMICOLON, "after static assertion");
	return true;
}

static void
structdecl(struct scope *s, struct structbuilder *b)
{
	struct qualtype base, mt;
	char *name;
	unsigned long long width;
	int align;

	if (staticassert(s, NULL))
		return;
	attr(NULL, 0);
	base = declspecs(s, NULL, NULL, &align);
	if (!base.type)
		error(&tok.loc, "no type in struct member declaration");
	if (tok.kind == TSEMICOLON) {
		if ((base.type->kind != TYPESTRUCT && base.type->kind != TYPEUNION) || base.type->u.structunion.tag)
			error(&tok.loc, "struct declaration must declare at least one member");
		next();
		addmember(b, base, NULL, align, -1);
		return;
	}
	for (;;) {
		if (consume(TCOLON)) {
			width = intconstexpr(s, false);
			addmember(b, base, NULL, 0, width);
		} else {
			mt = declarator(s, base, &name, &align, NULL, false);
			width = consume(TCOLON) ? intconstexpr(s, false) : -1;
			addmember(b, mt, name, align, width);
		}
		if (tok.kind == TSEMICOLON)
			break;
		expect(TCOMMA, "or ';' after declarator");
	}
	next();
}

/* 6.7.7 Type names */
struct type *
typename(struct scope *s, enum typequal *tq, struct expr **toeval)
{
	struct qualtype t;

	t = declspecs(s, NULL, NULL, NULL);
	if (t.type) {
		t = declarator(s, t, NULL, NULL, NULL, true);
		if (tq)
			*tq |= t.qual;
		if (toeval)
			*toeval = t.expr;
	}
	return t.type;
}

static enum linkage
getlinkage(enum declkind kind, enum storageclass sc, struct decl *prior, bool filescope)
{
	if (sc & SCSTATIC)
		return filescope ? LINKINTERN : LINKNONE;
	if (sc & SCEXTERN || kind == DECLFUNC)
		return prior ? prior->linkage : LINKEXTERN;
	return filescope ? LINKEXTERN : LINKNONE;
}

static struct decl *
declcommon(struct scope *s, enum declkind kind, char *name, char *asmname, struct type *t, enum typequal tq, enum storageclass sc, struct decl *prior)
{
	struct decl *d;
	enum linkage linkage;
	const char *kindstr = kind == DECLFUNC ? "function" : "object";

	if (prior) {
		if (prior->linkage == LINKNONE)
			error(&tok.loc, "%s '%s' with no linkage redeclared", kindstr, name);
		linkage = getlinkage(kind, sc, prior, s == &filescope);
		if (prior->linkage != linkage)
			error(&tok.loc, "%s '%s' redeclared with different linkage", kindstr, name);
		if (!typecompatible(t, prior->type) || tq != prior->qual)
			error(&tok.loc, "%s '%s' redeclared with incompatible type", kindstr, name);
		if (asmname && (!prior->asmname || strcmp(prior->asmname, asmname) != 0))
			error(&tok.loc, "%s '%s' redeclared with different assembler name", kindstr, name);
		prior->type = typecomposite(t, prior->type);
		return prior;
	}
	if (s->parent)
		prior = scopegetdecl(s->parent, name, true);
	linkage = getlinkage(kind, sc, prior, s == &filescope);
	if (linkage != LINKNONE && s->parent) {
		/* XXX: should maintain map of identifiers with linkage to their declaration, and use that */
		if (s->parent != &filescope)
			prior = scopegetdecl(&filescope, name, false);
		if (prior && prior->linkage != LINKNONE) {
			if (prior->kind != kind)
				error(&tok.loc, "'%s' redeclared with different kind", name);
			if (prior->linkage != linkage)
				error(&tok.loc, "%s '%s' redeclared with different linkage", kindstr, name);
			if (!typecompatible(t, prior->type) || tq != prior->qual)
				error(&tok.loc, "%s '%s' redeclared with incompatible type", kindstr, name);
			if (!asmname)
				asmname = prior->asmname;
			else if (!prior->asmname || strcmp(prior->asmname, asmname) != 0)
				error(&tok.loc, "%s '%s' redeclared with different assembler name", kindstr, name);
			t = typecomposite(t, prior->type);
		}
	}
	d = mkdecl(name, kind, t, tq, linkage);
	d->asmname = asmname;
	scopeputdecl(s, d);
	return d;
}

/*
Parse the initializer of a declaration with an inferred type (after the
'='), and store the inferred type in `t`.
*/
static struct init *
inferinit(struct scope *s, struct type **t)
{
	struct expr *e;
	bool braced;

	braced = consume(TLBRACE);
	e = assignexpr(s);
	if (braced) {
		consume(TCOMMA);
		expect(TRBRACE, "after initializer");
	}
	*t = e->type;
	if (*t == &typevoid)
		error(&tok.loc, "cannot infer type from expression with type 'void'");
	if ((*t)->prop & PROPSCALAR)
		e = exprassign(e, *t);
	return mkinit(0, (*t)->size, (struct bitfield){0}, e);
}

static void
defineobj(struct decl *d, struct init *init, bool hasinit, struct stmt ***end)
{
	struct stmt *st;

	if (d->type->incomplete)
		error(&tok.loc, "object '%s' has incomplete type", d->name);
	if (d->u.obj.align < d->type->align)
		d->u.obj.align = d->type->align;
	if (d->u.obj.storage == SDAUTO || d->u.obj.mono) {
		st = addstmt(end, STMTDECL);
		st->u.decl.decl = d;
		st->u.decl.init = init;
		st->u.decl.hasinit = hasinit;
	} else {
		emitdata(d, init);
	}
	d->defined = true;
}

/*
Parse a declaration. At block scope, `fc` is the function being
defined, and statements initializing automatic objects are added to
`end`.
*/
/* parse a parameter list `<...>` of a forall or exists clause into g, declaring the parameters in s */
static void
paramlist(struct scope *s, struct generic *g, const char *clause)
{
	struct array params = {0};
	struct genparam *p;
	struct decl *d;
	size_t i, j;
	int nconst;

	expect(TLESS, clause);
	nconst = 0;
	do {
		p = arrayadd(&params, sizeof(*p));
		switch (tok.kind) {
		case C5_TYPE:      p->kind = GENTYPE;      break;
		case C5_SIZE:      p->kind = GENSIZE;      break;
		case C5_CONSTNESS:
			p->kind = GENCONSTNESS;
			if (nconst == 3)
				error(&tok.loc, "too many constness parameters");
			p->bit = QUALCPARAM0 << nconst++;
			break;
		default:
			error(&tok.loc, "expected 'type', 'size', or 'constness' in parameter list");
		}
		next();
		p->name = expect(TIDENT, "after parameter kind");
		p->type = NULL;
	} while (consume(TCOMMA));
	closeangle();
	g->nparam = params.len / sizeof(*p);
	g->params = params.val;
	for (i = 0; i < g->nparam; ++i) {
		p = &g->params[i];
		for (j = 0; j < i; ++j) {
			if (strcmp(g->params[j].name, p->name) == 0)
				error(&tok.loc, "duplicate parameter '%s'", p->name);
		}
		if (scopegetdecl(s, p->name, false))
			error(&tok.loc, "duplicate parameter '%s'", p->name);
		if (p->kind == GENSIZE || p->kind == GENCONSTNESS) {
			/* a size parameter is a constant of type size_t; a constness parameter is a qualifier */
			d = mkdecl(p->name, DECLCONST, &typeulong, QUALNONE, LINKNONE);
			d->gen = g;
			d->u.enumconst = i;
			scopeputdecl(s, d);
			continue;
		}
		p->type = mkparamtype(g, i, p->name);
		scopeputdecl(s, mkdecl(p->name, DECLTYPE, p->type, QUALNONE, LINKNONE));
	}
}

/*
Parse `[mono|erased] [forall<...>] [exists<...>]`, declaring the
parameters in s. The parameters of the exists clause, if any, are
stored in *exists.
*/
static struct generic *
genparams(struct scope *s, struct generic **exists)
{
	struct generic *g, *ex;
	size_t i;
	bool ismono;

	ismono = consume(T_MONO);
	if (!ismono)
		consume(T_ERASED);
	g = NULL;
	if (consume(T_FORALL)) {
		g = mkgeneric(ismono);
		paramlist(s, g, "after 'forall'");
	}
	ex = NULL;
	if (consume(T_EXISTS)) {
		ex = mkgeneric(ismono);
		paramlist(s, ex, "after 'exists'");
		for (i = 0; i < ex->nparam; ++i) {
			if (ex->params[i].kind != GENTYPE)
				error(&tok.loc, "exists parameters must be type parameters");
		}
	} else if (!g) {
		error(&tok.loc, "expected 'forall' or 'exists' after 'mono' or 'erased'");
	}
	if (tok.kind == T_FORALL)
		error(&tok.loc, "'exists' must come after 'forall'");
	*exists = ex;
	return g;
}

/* check that an erased function does not pass or return a type parameter by value */
static void
checkerased(struct type *t, char *name)
{
	struct decl *p;

	if (t->base->kind == TYPEPARAM)
		error(&tok.loc, "erased function '%s' cannot return type parameter '%s' by value", name, t->base->u.param.name);
	for (p = t->u.func.params; p; p = p->next) {
		if (p->type->kind == TYPEPARAM)
			error(&tok.loc, "erased function '%s' cannot take type parameter '%s' by value", name, p->type->u.param.name);
	}
}

bool
decl(struct scope *s, struct funcctx *fc, struct stmt ***end)
{
	struct qualtype base, qt;
	struct type *t;
	enum typequal tq;
	enum storageclass sc;
	enum funcspec fs;
	struct attr a;
	struct init *init, *autoinit;
	bool hasinit;
	char *name, *asmname;
	int allowfunc = !fc;
	struct decl *d, *prior;
	enum declkind kind;
	struct scope *funcscope;
	struct funcctx bodyctx;
	struct func *f;
	struct stmt *body;
	struct generic *gen, *exgen;
	struct genarg *args;
	struct scope *ls;
	enum typequal q;
	size_t i;
	int align;

	if (staticassert(s, fc && fc->mono ? end : NULL))
		return true;
	a.kind = 0;
	if (attr(&a, ATTRNORETURN) && consume(TSEMICOLON))
		return true;
	/* names are looked up in ls, which contains the forall parameters, but declared in s */
	ls = s;
	gen = NULL;
	exgen = NULL;
	switch (tok.kind) {
	case T_MONO:
	case T_ERASED:
	case T_FORALL:
	case T_EXISTS:
		if (fc)
			error(&tok.loc, "polymorphic declarations must be at file scope");
		ls = mkscope(s);
		gen = genparams(ls, &exgen);
		pendinggen = gen;
		pendingexists = exgen;
		pendinggenscope = s;
		break;
	}
	base = declspecs(ls, &sc, &fs, &align);
	pendinggen = NULL;
	if (pendingexists) {
		pendingexists = NULL;
		error(&tok.loc, "exists can only be used in struct and union declarations");
	}
	if (!base.type) {
		if (gen)
			error(&tok.loc, "expected declaration after forall parameter list");
		return false;
	}
	/* with an inferred type, auto has no effect on storage duration or linkage */
	if (base.type == &typeauto)
		sc &= ~SCAUTO;
	else if (sc & SCAUTO && sc != SCAUTO)
		error(&tok.loc, "'auto' with another storage-class specifier requires an inferred type");
	if (fc) {
		if (sc == SCTHREADLOCAL)
			error(&tok.loc, "block scope declaration containing 'thread_local' must contain 'static' or 'extern'");
	} else {
		/* 6.9p2 */
		if (sc & SCAUTO)
			error(&tok.loc, "external declaration must not contain 'auto'");
		if (sc & SCREGISTER)
			error(&tok.loc, "external declaration must not contain 'register'");
	}
	if (consume(TSEMICOLON)) {
		if (gen && !gen->pattern)
			error(&tok.loc, "forall declaration declares nothing");
		if (base.type == &typeauto)
			error(&tok.loc, "declaration with inferred type has no declarator");
		/* XXX 6.7p2 error unless in function parameter/struct/union, or tag/enum members are declared */
		return true;
	}
	for (;;) {
		qt = declarator(ls, base, &name, NULL, &funcscope, false);
		t = qt.type;
		tq = qt.qual;
		autoinit = NULL;
		if (base.type == &typeauto) {
			if (t != &typeauto)
				error(&tok.loc, "declarator of '%s' with inferred type must be an identifier", name);
			if (sc & SCTYPEDEF)
				error(&tok.loc, "typedef '%s' cannot have inferred type", name);
			if (!consume(TASSIGN))
				error(&tok.loc, "declaration of '%s' with inferred type must have an initializer", name);
			autoinit = inferinit(ls, &t);
		}
		if (consume(T__ASM__)) {
			struct stringlit lit;

			expect(TLPAREN, "after __asm__");
			tokencheck(&tok, TSTRINGLIT, "after __asm__");
			stringconcat(&lit, true);
			asmname = lit.data;
			expect(TRPAREN, "after assembler name");
			allowfunc = 0;
		} else {
			asmname = NULL;
		}
		gnuattr(&a, 0);  /* appertains to identifier */
		kind = sc & SCTYPEDEF ? DECLTYPE : t->kind == TYPEFUNC ? DECLFUNC : DECLOBJECT;
		prior = scopegetdecl(s, name, false);
		if (prior && prior->kind != kind)
			error(&tok.loc, "'%s' redeclared with different kind", name);
		if (prior && !prior->gen != !gen)
			error(&tok.loc, "'%s' redeclared %s forall", name, gen ? "with" : "without");
		if (gen && prior) {
			/* compare with the prior declaration in terms of its parameters */
			if (prior->gen->nparam != gen->nparam)
				error(&tok.loc, "'%s' redeclared with different number of forall parameters", name);
			args = xreallocarray(NULL, gen->nparam, sizeof(*args));
			for (i = 0; i < gen->nparam; ++i) {
				args[i].type = prior->gen->params[i].type;
				args[i].qual = QUALNONE;
			}
			q = QUALNONE;
			t = typesubst(t, &q, gen, args);
		}
		switch (kind) {
		case DECLTYPE:
			if (align)
				error(&tok.loc, "typedef '%s' declared with alignment specifier", name);
			if (asmname)
				error(&tok.loc, "typedef '%s' declared with assembler label", name);
			if (gen) {
				if (prior)
					error(&tok.loc, "forall typedef '%s' redefined", name);
				d = mkdecl(name, DECLTYPE, t, tq, LINKNONE);
				d->gen = gen;
				if (!gen->name)
					gen->name = name;
				if (!gen->pattern)
					gen->pattern = t;
				else if (gen->pattern != t)
					error(&tok.loc, "forall declaration must declare a single type");
				scopeputdecl(s, d);
			} else if (!prior) {
				scopeputdecl(s, mkdecl(name, DECLTYPE, t, tq, LINKNONE));
			} else if (!typesame(prior->type, t) || prior->qual != tq) {
				error(&tok.loc, "typedef '%s' redefined with different type", name);
			}
			break;
		case DECLOBJECT:
			if (align && align < t->align)
				error(&tok.loc, "object '%s' requires alignment %d, which is stricter than specified alignment %d", name, t->align, align);
			if (gen && !gen->name)
				gen->name = name;
			d = declcommon(s, kind, name, asmname, t, tq, sc, prior);
			if (gen && !prior)
				d->gen = gen;
			if (gen && !gen->ismono != !d->gen->ismono)
				error(&tok.loc, "'%s' redeclared with different mono and erased behavior", name);
			if (d->u.obj.align < align)
				d->u.obj.align = align;
			if (gen && gen->ismono) {
				/* the initializer is instantiated for each set of arguments */
				if (asmname)
					error(&tok.loc, "mono variable '%s' cannot have an assembler label", name);
				d->u.obj.storage = SDSTATIC;
				if (autoinit || consume(TASSIGN)) {
					if (d->defined)
						error(&tok.loc, "object '%s' redefined", name);
					d->u.obj.geninit = autoinit ? autoinit : parseinit(ls, qt.type);
					d->u.obj.deftype = qt.type;
					d->u.obj.defgen = gen;
					d->defined = true;
				} else if (!(sc & SCEXTERN) && !d->defined) {
					d->u.obj.deftype = qt.type;
					d->u.obj.defgen = gen;
					d->defined = true;
				}
				break;
			}
			if (d->linkage == LINKNONE && !(sc & SCSTATIC)) {
				d->u.obj.storage = SDAUTO;
			} else {
				d->u.obj.storage = sc & SCTHREADLOCAL ? SDTHREAD : SDSTATIC;
				if (t->prop & PROPVM)
					error(&tok.loc, "object '%s' with %s storage duration cannot have variably modified type", name, d->u.obj.storage == SDSTATIC ? "static" : "thread");
				/* the static locals of a mono function are created for each instance */
				if (fc && fc->mono && d->linkage == LINKNONE)
					d->u.obj.mono = true;
				else
					d->value = mkglobal(d);
			}

			if (base.expr)
				addstmt(end, STMTDECL)->u.decl.vm = base.expr;
			init = NULL;
			hasinit = false;
			if (autoinit || consume(TASSIGN)) {
				if (fc && d->linkage != LINKNONE)
					error(&tok.loc, "object '%s' with block scope and %s linkage cannot have initializer", name, d->linkage == LINKEXTERN ? "external" : "internal");
				if (d->defined)
					error(&tok.loc, "object '%s' redefined", name);
				init = autoinit ? autoinit : parseinit(ls, d->type);
				hasinit = true;
			} else if (sc & SCEXTERN) {
				break;
			} else if (d->linkage != LINKNONE && d->u.obj.storage == SDSTATIC) {
				if (!d->defined && !d->tentative) {
					d->tentative = true;
					*tentativedefnsend = d;
					tentativedefnsend = &d->next;
				}
				break;
			}
			defineobj(d, init, hasinit, end);
			break;
		case DECLFUNC:
			if (align)
				error(&tok.loc, "function '%s' declared with alignment specifier", name);
			if (fc && sc && sc != SCEXTERN)  /* 6.7.1p7 */
				error(&tok.loc, "function '%s' with block scope may only have storage class 'extern'", name);
			if (gen && !gen->ismono)
				checkerased(t, name);
			if (gen && !gen->name)
				gen->name = name;
			d = declcommon(s, kind, name, asmname, t, tq, sc, prior);
			if (gen && !prior)
				d->gen = gen;
			if (gen && !gen->ismono != !d->gen->ismono)
				error(&tok.loc, "'%s' redeclared with different mono and erased behavior", name);
			d->value = mkglobal(d);
			d->u.func.inlinedefn = d->linkage == LINKEXTERN && fs & FUNCINLINE && !(sc & SCEXTERN) && (!prior || prior->u.func.inlinedefn);
			d->u.func.isnoreturn = fs & FUNCNORETURN || a.kind & ATTRNORETURN;
			if (tok.kind == TLBRACE) {
				if (!allowfunc)
					error(&tok.loc, "function definition not allowed");
				if (d->defined)
					error(&tok.loc, "function '%s' redefined", name);
				/* re-open scope from function declarator */
				assert(funcscope);
				s = funcscope;
				if (gen && gen->ismono) {
					/* the body is checked once, and instantiated for each set of arguments */
					d->u.func.namedecl = mkdecl("__func__", DECLOBJECT, mkarraytype(&typechar, QUALCONST, strlen(name) + 1), QUALNONE, LINKNONE);
					d->u.func.namedecl->u.obj.storage = SDSTATIC;
					scopeputdecl(s, d->u.func.namedecl);
					bodyctx.type = qt.type;
					bodyctx.mono = true;
					d->u.func.body = funcbody(&bodyctx, s);
					d->u.func.deftype = qt.type;
					d->u.func.defgen = gen;
					s = delscope(s);
					d->defined = true;
					return true;
				}
				bodyctx.mono = false;
				/* the body uses the declarator's own forall parameters */
				f = mkfunc(d, name, qt.type, s);
				bodyctx.type = qt.type;
				body = funcbody(&bodyctx, s);
				lower(f, body);
				delstmt(body);
				if (d->u.func.isnoreturn)
					funchlt(f);
				/* XXX: need to keep track of function in case a later declaration specifies extern */
				if (!d->u.func.inlinedefn)
					emitfunc(f, d->linkage == LINKEXTERN);
				s = delscope(s);
				delfunc(f);
				d->defined = true;
				return true;
			} else if (funcscope) {
				delscope(funcscope);
			}
			break;
		}
		if (consume(TSEMICOLON))
			return true;
		expect(TCOMMA, "or ';' after declarator");
		allowfunc = 0;
	}
}

/*
Compute the layout of an instance of a mono struct or union from the
fields of the pattern it was instantiated from.
*/
void
structlayout(struct type *t, struct type *pattern)
{
	struct structbuilder b;
	struct structitem *item;
	struct member *pm, *m;

	b.type = t;
	b.bits = 0;
	b.pack = pattern->u.structunion.packed;
	t->size = 0;
	t->align = 0;
	for (item = pattern->u.structunion.items; item; item = item->next) {
		m = NULL;
		if (item->member) {
			/* the instance's members correspond to the pattern's in order */
			for (pm = pattern->u.structunion.members, m = t->u.structunion.members; pm != item->member; pm = pm->next)
				m = m->next;
		}
		if (m && m->type->incomplete && !(m->type->kind == TYPEARRAY && !m->next))
			error(&tok.loc, "member '%s' of mono %s instance has incomplete type", m->name, t->kind == TYPESTRUCT ? "struct" : "union");
		placemember(&b, m, m ? m->type : item->type, m ? m->name : NULL, item->align, item->width);
	}
	if (!b.pack)
		t->size = ALIGNUP(t->size, t->align);
}

struct decl *
stringdecl(struct expr *expr)
{
	static struct map strings;
	struct mapkey key;
	struct decl *d;
	size_t i;

	if (!strings.len)
		mapinit(&strings, 64);
	assert(expr->kind == EXPRSTRING);
	mapkey(&key, expr->u.string.data, expr->u.string.size);
	if (mapput(&strings, &key, &i)) {
		d = mkdecl("string", DECLOBJECT, expr->type, QUALNONE, LINKNONE);
		d->value = mkglobal(d);
		emitdata(d, mkinit(0, expr->type->size, (struct bitfield){0}, expr));
		strings.vals[i].p = d;
	} else {
		d = strings.vals[i].p;
	}
	return d;
}

void
emittentativedefns(void)
{
	struct decl *d;

	for (d = tentativedefns; d; d = d->next) {
		if (!d->defined)
			defineobj(d, NULL, false, NULL);
	}
}
