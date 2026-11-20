#include <ctype.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "util.h"
#include "cc.h"

struct buffer {
	unsigned char *str;
	size_t len, cap;
};

struct scanner {
	int chr;
	bool usebuf;
	bool sawspace;
	FILE *file;
	struct location loc;
	struct buffer buf;
	struct scanner *next;
};

static struct scanner *scanner;

static void
bufadd(struct buffer *b, int c)
{
	if (b->len >= b->cap) {
		b->cap = b->cap ? b->cap * 2 : 1<<8;
		b->str = xreallocarray(b->str, b->cap, 1);
	}
	b->str[b->len++] = c;
}

static char *
bufget(struct buffer *b)
{
	char *s;

	bufadd(b, '\0');
	s = xmalloc(b->len);
	memcpy(s, b->str, b->len);
	b->len = 0;

	return s;
}

static void
nextchar(struct scanner *s)
{
	int c;

	if (s->usebuf)
		bufadd(&s->buf, s->chr);
	for (;;) {
		s->chr = getc(s->file);
		if (s->chr == '\n') {
			++s->loc.line, s->loc.col = 0;
			break;
		}
		++s->loc.col;
		if (s->chr != '\\')
			break;
		c = getc(s->file);
		if (c != '\n') {
			ungetc(c, s->file);
			break;
		}
		++s->loc.line, s->loc.col = 0;
	}
}

static int
op2(struct scanner *s, int t1, int t2)
{
	nextchar(s);
	if (s->chr != '=')
		return t1;
	nextchar(s);
	return t2;
}

static int
op3(struct scanner *s, int t1, int t2, int t3)
{
	int c;

	c = s->chr;
	nextchar(s);
	if (s->chr == '=') {
		nextchar(s);
		return t2;
	}
	if (s->chr != c)
		return t1;
	nextchar(s);
	return t3;
}

static int
op4(struct scanner *s, int t1, int t2, int t3, int t4)
{
	int c;

	c = s->chr;
	nextchar(s);
	if (s->chr == '=') {
		nextchar(s);
		return t2;
	}
	if (s->chr != c)
		return t1;
	nextchar(s);
	if (s->chr != '=')
		return t3;
	nextchar(s);
	return t4;
}

static enum tokenkind charconst(struct scanner *);
static int stringlit(struct scanner *);

/*
Whether an identifier is an encoding prefix: L, u, U, u8, or for strings
also n (native encoding), and any of these or nothing after p (no null
terminator) or c (null terminator).
*/
static bool
isprefix(const unsigned char *p, size_t n, bool string)
{
	if (string && n > 0 && (*p == 'p' || *p == 'c')) {
		++p, --n;
		if (n == 0)
			return true;
	}
	switch (n) {
	case 1: return *p == 'L' || *p == 'u' || *p == 'U' || string && *p == 'n';
	case 2: return p[0] == 'u' && p[1] == '8';
	}
	return false;
}

static int
ident(struct scanner *s)
{
	int tok;

	s->usebuf = true;
	while (isalnum(s->chr) || s->chr == '_')
		nextchar(s);
	if (s->chr == '"' && isprefix(s->buf.str, s->buf.len, true))
		return stringlit(s);
	if (s->chr == '\'' && isprefix(s->buf.str, s->buf.len, false))
		return charconst(s);
	tok = tokenget(s->buf.str, s->buf.len);
	s->usebuf = false;
	s->buf.len = 0;
	return tok;
}

static int
isodigit(int c)
{
	return (unsigned)c - '0' < 8;
}

static enum tokenkind
number(struct scanner *s)
{
	bool allowsign = false;

	s->usebuf = true;
	for (;;) {
		nextchar(s);
		switch (s->chr) {
		case 'e':
		case 'E':
		case 'p':
		case 'P':
			allowsign = true;
			break;
		case '+':
		case '-':
			if (!allowsign)
				goto done;
			break;
		case '.':
			allowsign = false;
			break;
		case '\'':
			nextchar(s);
			--s->buf.len;  /* ignore separator */
			/* fallthrough */
		default:
			if (!isalnum(s->chr) && s->chr != '_')
				goto done;
			allowsign = false;
		}
	}
done:
	return TNUMBER;
}

static void
escape(struct scanner *s)
{
	nextchar(s);
	if (s->chr == 'x') {
		nextchar(s);
		if (!isxdigit(s->chr))
			error(&s->loc, "invalid hexadecimal escape sequence");
		do nextchar(s);
		while (isxdigit(s->chr));
	} else if (isodigit(s->chr)) {
		nextchar(s);
		if (isodigit(s->chr)) {
			nextchar(s);
			if (isodigit(s->chr))
				nextchar(s);
		}
	} else if (strchr("'\"?\\abfnrtv", s->chr)) {
		nextchar(s);
	} else {
		error(&s->loc, "invalid escape sequence");
	}
}

static enum tokenkind
charconst(struct scanner *s)
{
	s->usebuf = true;
	nextchar(s);
	for (;;) {
		switch (s->chr) {
		case '\\':
			escape(s);
			break;
		case '\'':
			nextchar(s);
			return TCHARCONST;
		case '\n':
			error(&s->loc, "newline in character constant");
		case EOF:
			error(&s->loc, "EOF in character constant");
		default:
			nextchar(s);
			break;
		}
	}
}

static int
stringlit(struct scanner *s)
{
	s->usebuf = true;
	nextchar(s);
	for (;;) {
		switch (s->chr) {
		case '\\':
			escape(s);
			break;
		case '"':
			nextchar(s);
			return TSTRINGLIT;
		case '\n':
			error(&s->loc, "newline in string literal");
		case EOF:
			error(&s->loc, "EOF in string literal");
		default:
			nextchar(s);
			break;
		}
	}
}

static bool
comment(struct scanner *s)
{
	int last;

	switch (s->chr) {
	case '/':  /* C++-style comment */
		do nextchar(s);
		while (s->chr != '\n' && s->chr != EOF);
		break;
	case '*':  /* C-style comment */
		nextchar(s);
		do {
			last = s->chr;
			nextchar(s);
			if (s->chr == EOF)
				error(&s->loc, "EOF in comment");
		} while (last != '*' || s->chr != '/');
		nextchar(s);
		break;
	default:
		return false;
	}
	s->sawspace = true;
	return true;
}

static int
scankind(struct scanner *s, struct location *loc)
{
	enum tokenkind tok;
	struct location oldloc;

again:
	*loc = s->loc;
	switch (s->chr) {
	case ' ':
	case '\t':
	case '\f':
	case '\v':
		s->sawspace = true;
		nextchar(s);
		goto again;
	case '!':
		return op2(s, TLNOT, TNEQ);
	case '"':
		return stringlit(s);
	case '#':
		nextchar(s);
		if (s->chr != '#')
			return THASH;
		nextchar(s);
		return THASHHASH;
	case '%':
		return op2(s, TMOD, TMODASSIGN);
	case '&':
		return op3(s, TBAND, TBANDASSIGN, TLAND);
	case '\'':
		return charconst(s);
	case '*':
		return op2(s, TMUL, TMULASSIGN);
	case '+':
		return op3(s, TADD, TADDASSIGN, TINC);
	case '-':
		tok = op3(s, TSUB, TSUBASSIGN, TDEC);
		if (tok != TSUB || s->chr != '>')
			return tok;
		nextchar(s);
		return TARROW;
	case '/':
		tok = op2(s, TDIV, TDIVASSIGN);
		if (tok == TDIV && comment(s))
			goto again;
		return tok;
	case '<':
		return op4(s, TLESS, TLEQ, TSHL, TSHLASSIGN);
	case '=':
		return op2(s, TASSIGN, TEQL);
	case '>':
		return op4(s, TGREATER, TGEQ, TSHR, TSHRASSIGN);
	case '^':
		return op2(s, TXOR, TXORASSIGN);
	case '|':
		return op3(s, TBOR, TBORASSIGN, TLOR);
	case '\n':
		nextchar(s);
		return TNEWLINE;
	case '[':
		nextchar(s);
		return TLBRACK;
	case ']':
		nextchar(s);
		return TRBRACK;
	case '(':
		nextchar(s);
		return TLPAREN;
	case ')':
		nextchar(s);
		return TRPAREN;
	case '{':
		nextchar(s);
		return TLBRACE;
	case '}':
		nextchar(s);
		return TRBRACE;
	case '.':
		nextchar(s);
		if (isdigit(s->chr)) {
			bufadd(&s->buf, '.');
			return number(s);
		}
		if (s->chr != '.')
			return TPERIOD;
		oldloc = s->loc;
		nextchar(s);
		if (s->chr != '.') {
			ungetc(s->chr, s->file);
			s->loc = oldloc;
			s->chr = '.';
			return TPERIOD;
		}
		nextchar(s);
		return TELLIPSIS;
	case '~':
		nextchar(s);
		return TBNOT;
	case '?':
		nextchar(s);
		return TQUESTION;
	case ':':
		nextchar(s);
		if (s->chr != ':')
			return TCOLON;
		nextchar(s);
		return TCOLONCOLON;
	case ';':
		nextchar(s);
		return TSEMICOLON;
	case ',':
		nextchar(s);
		return TCOMMA;
	case EOF:
		return TEOF;
	default:
		if (isdigit(s->chr))
			return number(s);
		if (isalpha(s->chr) || s->chr == '_')
			return ident(s);
		s->usebuf = true;
		nextchar(s);
		return TOTHER;
	}
}

void
scanfrom(const char *name, FILE *file)
{
	struct scanner *s;

	s = xmalloc(sizeof(*s));
	s->file = file;
	s->buf.str = NULL;
	s->buf.len = 0;
	s->buf.cap = 0;
	s->usebuf = false;
	s->loc.file = name;
	s->loc.line = 1;
	s->loc.col = 0;
	s->next = scanner;
	if (file)
		nextchar(s);
	scanner = s;
}

void
scanopen(void)
{
	if (!scanner->file) {
		scanner->file = fopen(scanner->loc.file, "r");
		if (!scanner->file)
			fatal("open %s:", scanner->loc.file);
		nextchar(scanner);
	}
}

void
scansetloc(struct location loc)
{
	/*
	loc is for the next line, whose first character was already
	read. If that line is empty, the character is its newline,
	which is located at the start of the following line.
	*/
	if (scanner->chr == '\n')
		++loc.line, loc.col = 0;
	scanner->loc = loc;
}

static void
scanclose(void)
{
	fclose(scanner->file);
	free(scanner->buf.str);
	free(scanner);
}

void
scan(struct token *t)
{
	scanner->sawspace = false;
	for (;;) {
		t->kind = scankind(scanner, &t->loc);
		if (t->kind != TEOF || !scanner->next)
			break;
		scanclose();
		scanner = scanner->next;
		scanopen();
	}
	if (scanner->usebuf) {
		t->lit = bufget(&scanner->buf);
		scanner->usebuf = false;
	} else {
		t->lit = NULL;
	}
	t->space = scanner->sawspace;
	t->hide = false;
	t->c5 = c5file(t->loc.file);
}

/*
Scan a string consisting of a single token, as needed for the '##'
operator. Errors are reported at the location in t. Returns false if
the string is not exactly one token.
*/
bool
scanstring(const char *str, struct token *t)
{
	struct scanner s = {0};
	struct location loc;
	bool single;

	s.file = fmemopen((char *)str, strlen(str), "r");
	if (!s.file)
		fatal("fmemopen:");
	s.loc = t->loc;
	nextchar(&s);
	t->kind = scankind(&s, &loc);
	single = t->kind != TEOF && s.chr == EOF;
	if (s.usebuf)
		t->lit = bufget(&s.buf);
	else
		t->lit = NULL;
	t->space = false;
	t->hide = false;
	fclose(s.file);
	free(s.buf.str);
	return single;
}
