#include <stdio.h>

struct func;
struct funcctx;
struct stmt;
struct generic;
struct genarg;

enum tokenkind {
#define TOKEN(t, s) t,
#include "tokens.h"
#undef TOKEN

	TPPIDENT = TALIGNAS,
	TIDENT = TDEFINE
};

struct location {
	const char *file;
	size_t line, col;
};

struct token {
	enum tokenkind kind;
	/* whether or not the token is ineligible for expansion */
	bool hide;
	/* whether or not the token was preceeded by a space */
	bool space;
	struct location loc;
	char *lit;
};

enum typequal {
	QUALNONE,

	QUALCONST    = 1<<1,
	QUALRESTRICT = 1<<2,
	QUALVOLATILE = 1<<3,
	QUALATOMIC   = 1<<4
};

enum typekind {
	TYPENONE,

	TYPEVOID,
	TYPEBOOL,
	TYPECHAR,
	TYPESHORT,
	TYPEINT,
	TYPEENUM,
	TYPELONG,
	TYPELLONG,
	TYPEFLOAT,
	TYPEDOUBLE,
	TYPELDOUBLE,
	TYPEPOINTER,
	TYPEARRAY,
	TYPEFUNC,
	TYPESTRUCT,
	TYPEUNION,
	TYPENULLPTR,
	TYPEBITINT,
	/* parameter of a generic or template declaration */
	TYPEPARAM,
};

enum typeprop {
	PROPNONE,

	PROPCHAR    = 1<<0,
	PROPINT     = 1<<1,
	PROPREAL    = 1<<2,
	PROPARITH   = 1<<3,
	PROPSCALAR  = 1<<4,
	PROPFLOAT   = 1<<5,
	PROPVM      = 1<<6, /* variably-modified type */
	PROPFLEX    = 1<<7, /* struct with flexible array member */
};

struct bitfield {
	short before;  /* number of bits in the storage unit before the bit-field */
	short after;   /* number of bits in the storage unit after the bit-field */
};

struct member {
	char *name;
	struct type *type;
	enum typequal qual;
	unsigned long long offset;
	struct bitfield bits;
	struct member *next;
};

struct type {
	enum typekind kind;
	enum typeprop prop;
	int align;
	unsigned long long size;
	struct value *value;  /* used by the backend */
	struct type *base;
	struct list link;  /* used only during construction of type */
	/* qualifiers of the base type */
	enum typequal qual;
	bool incomplete;
	union {
		struct {
			bool issigned, iscomplex;
			int width;
		} arith;
		struct {
			struct expr *length;
			enum typequal ptrqual;
			struct value *size;
		} array;
		struct {
			bool isvararg;
			struct decl *params;
			size_t nparam;
		} func;
		struct {
			char *tag;
			struct member *members;
			/*
			generic struct this is an instance of, and its
			arguments (for the generic struct itself, the
			arguments are its own parameters)
			*/
			struct generic *gen;
			struct genarg *genargs;
		} structunion;
		struct {
			struct generic *gen;
			size_t index;
			char *name;
		} param;
	} u;
};

enum declkind {
	DECLTYPE,
	DECLOBJECT,
	DECLFUNC,
	DECLCONST,
	DECLBUILTIN,
};

enum linkage {
	LINKNONE,
	LINKINTERN,
	LINKEXTERN,
};

enum storageduration {
	SDSTATIC,
	SDTHREAD,
	SDAUTO,
};

enum builtinkind {
	BUILTINALLOCA,
	BUILTINCONSTANTP,
	BUILTINEXPECT,
	BUILTININFF,
	BUILTINNANF,
	BUILTINOFFSETOF,
	BUILTINTYPESCOMPATIBLEP,
	BUILTINUNREACHABLE,
	BUILTINVAARG,
	BUILTINVACOPY,
	BUILTINVAEND,
	BUILTINVALIST,
	BUILTINVASTART,
};

struct decl {
	char *name;
	enum declkind kind;
	enum linkage linkage;
	struct type *type;
	enum typequal qual;
	struct value *value;
	char *asmname;
	bool defined;
	bool tentative;
	struct decl *next;
	/* parameters, if this is a generic or template declaration */
	struct generic *gen;

	union {
		struct {
			/* alignment of object storage (may be stricter than type requires) */
			int align;
			enum storageduration storage;
		} obj;
		struct {
			/* the function might have an "inline definition" (C11 6.7.4p7) */
			bool inlinedefn;
			bool isnoreturn;
			/*
			for mono functions, the definition, which is
			instantiated for each set of arguments: the body,
			the type and parameters it was parsed with, and the
			placeholder for __func__
			*/
			struct stmt *body;
			struct type *deftype;
			struct generic *defgen;
			struct decl *namedecl;
		} func;
		unsigned long long enumconst;
		enum builtinkind builtin;
	} u;
};

struct scope {
	struct map tags;
	struct map decls;
	/* innermost enclosing statements targeted by break, continue, and case labels */
	struct stmt *breakstmt;
	struct stmt *continuestmt;
	struct stmt *switchstmt;
	/* innermost deferred block in effect, and deferred block being parsed */
	struct stmt *defer;
	struct stmt *indefer;
	struct scope *parent;
};

enum exprkind {
	/* primary expression */
	EXPRIDENT,
	EXPRCONST,
	EXPRSTRING,

	/* postfix expression */
	EXPRCALL,
	/* member E.M gets transformed to *(typeof(E.M) *)((char *)E + offsetof(typeof(E), M)) */
	EXPRBITFIELD,
	EXPRINCDEC,
	EXPRCOMPOUND,
	/* subscript E1[E2] gets transformed to *((E1)+(E2)) */

	EXPRUNARY,
	EXPRCAST,
	EXPRBINARY,
	EXPRCOND,
	EXPRASSIGN,
	EXPRCOMMA,

	EXPRBUILTIN,
	EXPRTEMP,
	EXPRSIZEOF,
	/* size, alignment, or member offset of a type depending on mono parameters */
	EXPRLAYOUT,
};

enum layoutkind {
	LAYOUTSIZE,
	LAYOUTALIGN,
	LAYOUTOFFSET,
};

struct stringlit {
	size_t size;
	void *data;
};

struct expr {
	enum exprkind kind;
	/* whether this expression is an lvalue */
	bool lvalue;
	/* whether this expression is a pointer decayed from an array or function designator */
	bool decayed;
	/* the unqualified type of the expression */
	struct type *type;
	/* the type qualifiers of the object this expression refers to (ignored for non-lvalues) */
	enum typequal qual;
	enum tokenkind op;
	struct expr *base;
	struct expr *next;
	struct expr *toeval;
	union {
		struct {
			struct decl *decl;
			/* explicit arguments of a generic function whose arguments are not all known */
			struct genarg *genargs;
		} ident;
		union {
			unsigned long long u;
			long long i;
			double f;
		} constant;
		struct stringlit string;
		struct {
			struct expr *args;
			size_t nargs;
		} call;
		struct {
			struct bitfield bits;
		} bitfield;
		struct {
			struct decl *decl;
			struct init *init;
		} compound;
		struct {
			bool post;
		} incdec;
		struct {
			struct expr *l, *r;
		} binary;
		struct {
			struct expr *t, *f;
		} cond;
		struct {
			struct expr *l, *r;
		} assign;
		struct {
			enum builtinkind kind;
		} builtin;
		struct {
			struct type *type;
		} szof;
		struct {
			enum layoutkind kind;
			struct type *type;
			char *member;
		} layout;
		struct value *temp;
	} u;
};

/* a step from an object to a subobject: an array index, or a member position */
struct initstep {
	bool isindex;
	unsigned long long n;
};

struct init {
	unsigned long long start, end;
	struct expr *expr;
	struct bitfield bits;
	struct init *next;
	/*
	for objects with types depending on mono parameters, the
	subobject being initialized; its offset is computed when the
	type is instantiated (see initresolve)
	*/
	struct initstep *path;
	size_t npath;
};

/* token */

extern struct token tok;

void tokeninit(void);
int tokenget(const void *, size_t);
void tokenprint(const struct token *, FILE *);
char *tokenstr(enum tokenkind);
char *tokencheck(const struct token *, enum tokenkind, const char *);
void diagloc(const struct location *);
noreturn void error(const struct location *, const char *, ...);

/* scan */

void scanfrom(const char *, FILE *);
void scanopen(void);
void scansetloc(struct location loc);
void scan(struct token *);

/* preprocessor */

enum ppflags {
	/* preserve newlines in preprocessor output */
	PPNEWLINE   = 1 << 0,
};

extern enum ppflags ppflags;

void ppinit(void);

bool c5file(const char *);
void next(void);
bool peek(enum tokenkind);
char *expect(enum tokenkind, const char *);
bool consume(enum tokenkind);

/* type */

struct type *mktype(enum typekind, enum typeprop);
struct type *mkpointertype(struct type *, enum typequal);
struct type *mkarraytype(struct type *, enum typequal, unsigned long long);
struct type *mkbitinttype(int width, bool sign);

bool typecompatible(struct type *, struct type *);
bool typesame(struct type *, struct type *);
struct type *typecomposite(struct type *, struct type *);
struct type *typeunqual(struct type *, enum typequal *);
struct type *typecommonreal(struct type *, unsigned, struct type *, unsigned);
struct type *typepromote(struct type *, unsigned);
struct type *typeadjust(struct type *, enum typequal *);
enum typeprop typeprop(struct type *);
struct member *typemember(struct type *, const char *, unsigned long long *);
bool typehasint(struct type *, unsigned long long, bool);

extern struct type typevoid;
extern struct type typebool;
extern struct type typechar, typeschar, typeuchar;
extern struct type typeshort, typeushort;
extern struct type typeint, typeuint;
extern struct type typelong, typeulong;
extern struct type typellong, typeullong;
extern struct type typefloat, typedouble, typeldouble;
extern struct type typenullptr;
extern struct type typeauto;
extern struct type *typeadjvalist;

/* generic */

struct genparam {
	char *name;
	/* TYPEPARAM type for the parameter */
	struct type *type;
};

/* parameters of a forall declaration */
struct generic {
	bool ismono;
	/* name of the declared entity, for instance names */
	char *name;
	size_t nparam;
	struct genparam *params;
	/* the generic type, for generic structs and typedefs */
	struct type *pattern;
	/* instantiations of the pattern */
	struct geninst *insts;
};

/* argument for a generic parameter; a NULL type is not yet known */
struct genarg {
	struct type *type;
	enum typequal qual;
};

struct generic *mkgeneric(bool);
struct type *mkparamtype(struct generic *, size_t, char *);
bool typehasparam(struct type *, struct generic *);
bool typehasparamkind(struct type *, bool);
bool typedep(struct type *);
bool argshaveparam(struct generic *, struct genarg *, bool);
char *geninstname(struct generic *, struct genarg *);
struct type *typesubst(struct type *, enum typequal *, struct generic *, struct genarg *);
struct type *geninst(struct generic *, struct genarg *, enum typequal *);
bool genunify(struct generic *, struct genarg *, struct type *, enum typequal, struct type *, enum typequal);
struct genarg *genargs(struct scope *, struct generic *, bool);
struct genarg *genidentity(struct generic *);
void closeangle(void);

/* mono */

struct decl *monoinst(struct decl *, struct genarg *);
void emitmonoinsts(void);

/* targ */

struct target {
	const char *name;
	struct type *typevalist;
	struct type *typewchar;
	int signedchar;
};

extern const struct target *targ;

void targinit(const char *);

/* attr */

enum attrkind {
	ATTRNORETURN    = 1<<0,

	/* GNU attributes */
	ATTRALIGNED     = 1<<2,
	ATTRCONSTRUCTOR = 1<<3,
	ATTRDESTRUCTOR  = 1<<4,
	ATTRPACKED      = 1<<5,
	ATTRSECTION     = 1<<6,
};

struct attr {
	enum attrkind kind;
	int align;
	char *section;
};

bool attr(struct attr *, enum attrkind);
bool gnuattr(struct attr *, enum attrkind);

/* decl */

struct decl *mkdecl(char *name, enum declkind, struct type *, enum typequal, enum linkage);
bool decl(struct scope *, struct funcctx *, struct stmt ***);
struct type *typename(struct scope *, enum typequal *, struct expr **);

struct decl *stringdecl(struct expr *);

void emittentativedefns(void);

/* scope */

void scopeinit(void);
struct scope *mkscope(struct scope *);
struct scope *delscope(struct scope *);

void scopeputdecl(struct scope *, struct decl *);
struct decl *scopegetdecl(struct scope *, const char *, bool);

void scopeputtag(struct scope *, const char *, struct type *);
struct type *scopegettag(struct scope *, const char *, bool);

extern struct scope filescope;

/* expr */

struct type *stringconcat(struct stringlit *, bool);

struct expr *expr(struct scope *);
struct expr *assignexpr(struct scope *);
struct expr *condexpr(struct scope *);
unsigned long long intconstexpr(struct scope *, bool);
void delexpr(struct expr *);

struct expr *exprassign(struct expr *, struct type *);
struct expr *exprpromote(struct expr *);

/* eval */

struct expr *eval(struct expr *);

/* init */

struct init *mkinit(unsigned long long, unsigned long long, struct bitfield, struct expr *);
struct init *parseinit(struct scope *, struct type *);
struct init *initresolve(struct init *, struct type *);


/* backend */

struct switchcases {
	void *root;
	struct type *type;
	struct block *defaultlabel;
};

/* stmt */

/* state needed while parsing a function body */
struct funcctx {
	/* type of the function being defined */
	struct type *type;
	/* whether the function is mono, so is instantiated rather than lowered */
	bool mono;
	/* labels defined in the function, and goto statements to resolve */
	struct map labels;
	struct stmt *gotos;
};

enum stmtkind {
	STMTCOMPOUND,
	STMTEXPR,
	STMTDECL,
	STMTIF,
	STMTSWITCH,
	STMTCASE,
	STMTDEFAULT,
	STMTWHILE,
	STMTDO,
	STMTFOR,
	STMTLABEL,
	STMTGOTO,
	STMTBREAK,
	STMTCONTINUE,
	STMTRETURN,
	STMTDEFER,
};

/*
Statements are parsed into a tree before any code is generated. Lists
of statements (compound statement bodies, and the labels and statement
making up the body of a selection or iteration statement) are linked
through `next`.

Deferred blocks in effect at a point in the function form a chain
through `u.defer.prev`, innermost first. When control leaves a block,
the deferred blocks between the chain at the jump and the chain at
the target are executed.
*/
struct stmt {
	enum stmtkind kind;
	struct stmt *next;
	/* innermost deferred block in effect at the start of this statement */
	struct stmt *defer;
	/* targets of break and continue (iteration and switch statements); set during lowering */
	struct block *breaklabel, *continuelabel;
	union {
		struct {
			struct stmt *body;
			/* innermost deferred block in effect at the end of the block */
			struct stmt *enddefer;
		} compound;
		/* expression statement, or return value (NULL for void return) */
		struct expr *expr;
		struct {
			/* NULL if this only evaluates `vm` */
			struct decl *decl;
			struct init *init;
			bool hasinit;
			/* side effects of a variably-modified typeof in the declaration specifiers */
			struct expr *vm;
		} decl;
		struct {
			struct expr *cond;
			struct stmt *then, *els;
			bool haselse;
		} ifstmt;
		struct {
			struct expr *cond;
			struct stmt *body;
			/* case values seen while parsing, for detecting duplicates */
			void *seen;
			bool hasdefault;
			/* filled in during lowering */
			struct switchcases cases;
		} switchstmt;
		/* while, do, and for statements */
		struct {
			struct stmt *init;
			struct expr *cond, *post;
			struct stmt *body;
		} loop;
		/* case and default labels */
		struct {
			struct stmt *switchstmt;
			unsigned long long value;
		} caselabel;
		struct {
			char *name;
			/* deferred block containing the label, if any */
			struct stmt *indefer;
			/* block for the label in the current lowering of its enclosing code */
			struct block *block;
			unsigned epoch;
		} label;
		/* goto, break, and continue */
		struct {
			/* label, or iteration or switch statement */
			struct stmt *target;
			/* for goto */
			char *name;
			struct location loc;
			struct stmt *indefer;
			struct stmt *nextgoto;
		} jump;
		struct {
			struct stmt *body;
			/* next outer deferred block in effect */
			struct stmt *prev;
		} defer;
	} u;
};

struct stmt *addstmt(struct stmt ***, enum stmtkind);
void stmt(struct funcctx *, struct scope *, struct stmt ***);
struct stmt *funcbody(struct funcctx *, struct scope *);
void delstmt(struct stmt *);

/* lower */

void lower(struct func *, struct stmt *);

void switchcase(struct switchcases *, unsigned long long, struct block *);

struct block *mkblock(char *);

struct value *mkglobal(struct decl *);

struct value *mkintconst(unsigned long long);

struct func *mkfunc(struct decl *, char *, struct type *, struct scope *);
void delfunc(struct func *);
struct type *functype(struct func *);
void funclabel(struct func *, struct block *);
struct value *funcbranch(struct func *, struct expr *, struct block *, struct block *);
struct value *funcexpr(struct func *, struct expr *);
void funcjmp(struct func *, struct block *);
void funcjnz(struct func *, struct value *, struct type *, struct block *, struct block *);
void funcret(struct func *, struct value *);
void funchlt(struct func *);
struct value *funcsave(struct func *, struct type *, struct value *);
void funcswitch(struct func *, struct value *, struct switchcases *, struct block *);
void funcinit(struct func *, struct decl *, struct init *, bool);

void emitfunc(struct func *, bool);
void emitdata(struct decl *, struct init *);
