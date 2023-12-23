/*
Current problems:
- all constants need to be explicitly cast
- the source code is just messy
- casting to/from booleans: should it be "smart?"

Feature ideas:
- functions return nples
- loops can have multiple exits

Improvments:
- implement hash table as a symbol table (but then how does scoping work?)
- fix space leaks (there have to be some)
- type names are really annoying as-is...

References:
- https://llvm.org/docs/LangRef.html
- https://redirect.cs.umbc.edu/courses/331/papers/lexyacc.pdf
*/

%{
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "header.h"

extern int yylineno;
extern int yyerror(const char *restrict msg);

/* single counter for giving unique names to everything */
int varctr;

/* symbol table */

struct symbol {
	char *id; /* actual name in user code */
	int n; /* unique identifier to avoid capturing */
	enum type t;
	struct symbol *next;
};

/* currently implemented as an alist */
static struct symbol *symbols;

/* create a new scope (this pushes a symbol NULL to the list) */
static void pushscope(void);
/* delete the last scope (this pops everything until the next NULL) */
static void popscope(void);
/* add a symbol to the list and return a unique identifier */
static int pushsymbol(char *id, enum type t);
/* return a pointer to the symbol, or NULL if it does not exist */
static struct symbol *symbolinfo(char *id);

/* list of functions */

struct function {
	char *name;
	enum type result, param;
	struct function *next;
};

/* currently implemented as an alist */
static struct function *functionlist;

/* add a function */
static void pushfunction(char *name, enum type result, enum type param);
/* look up a function */
static struct function *functioninfo(char *name);

/* stack of labels */

/* this is needed to save labels for conditionals, loops, etc. between
actions */

/* only stores the number in the label's name */
struct labelnode {
	int n;
	struct labelnode *next;
};

/* currently implemented as a linked list */
static struct labelnode *labelstack;

static void pushlabel(int);
static int poplabel(void);

/* utilities for working with types */

/* write the name of the llvm type to the buffer */
extern void type2str(char *buf, enum type t);

/* is this an unsigned, integral type? */
static int isunsigned(enum type t);
/* is this a floating-point, numeric type? */
static int isfloat(enum type t);

/* generating code */

static void cast(struct expressionresult *r, struct expressionresult s,
		enum type desttyp);
static void arithbinop(const char *signedinstr, const char *unsignedinstr,
		const char *floatinstr, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t);
static void cmpbinop(const char *cond, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t);
static void beginconditional(struct expressionresult cond);
static void middleconditional(void);
static void endconditional(void);
static void beginloop(void);
static void middleloop(struct expressionresult cond);
static void endloop(void);

%}

%union {
	/* lexer outputs */
	char *identifier;
	long int constant;
	/* parser outputs */
	enum type type;
	struct expressionresult expression;
}

%token <identifier> IDENTIFIER
%token <constant> CONSTANT
/* types */
%token U0 U1 I32 I64 U32 U64 F32 F64
/* expressions */
%token CAST
/* statements */
%token IF
%token WHILE
%token RETURN
%nonassoc IFX
%nonassoc ELSE
/* expressions */
%right '='
%left EQUALEQUAL BANGEQUAL '>' '<' GREATEREQUAL LESSEQUAL
%left '+' '-'
%left '*' '/' '%'

%type <type> typename
%type <expression> expression expression_0

%start program

%%

typename : U1  {$$ = U1T;}
typename : I32 {$$ = I32T;}
typename : I64 {$$ = I64T;}
typename : U32 {$$ = U32T;}
typename : U64 {$$ = U64T;}
typename : F32 {$$ = F32T;}
typename : F64 {$$ = F64T;}

expression_0 : '(' expression ')' {
	$$ = $2;
}

expression_0 : IDENTIFIER {
	struct symbol *sym;
	char tbuf[32];

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undefined variable");
	}
	$$.var = varctr++;
	$$.t = sym->t;
	type2str(tbuf, sym->t);
	printf("\t%%tmp%d = load %s, ptr %%%s%d\n", $$.var, tbuf, $1, sym->n);
}

expression_0 : CONSTANT {
	$$.var = varctr++;
	$$.t = I64T;
	printf("\t%%tmp%d = add i64 %lu, 0\n", $$.var, $1);
}

expression_0 : CAST '(' expression ',' typename ')' {cast(&$$, $3, $5);}

expression_0 : IDENTIFIER '(' expression ')' {
	struct function *node;
	char tbuf1[64], tbuf2[64];

	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (node->param != $3.t) {
		yyerror("function argument type mismatch");
	}
	$$.t = node->result;
	$$.var = varctr++;
	type2str(tbuf1, node->result);
	type2str(tbuf2, node->result);
	printf("\t%%tmp%d = call %s @%s(%s %%tmp%d)\n",
			$$.var, tbuf1, $1, tbuf2, $3.var);
}

expression : expression_0 {$$ = $1;}

expression : expression '*' expression {
	arithbinop("mul", "mul", "fmul", &$$, $1, $3);
}

expression : expression '/' expression {
	arithbinop("sdiv", "udiv", "fdiv", &$$, $1, $3);
}

expression : expression '%' expression {
	arithbinop("srem", "urem", "frem", &$$, $1, $3);
}

expression : expression '+' expression {
	arithbinop("add", "add", "fadd", &$$, $1, $3);
}

expression : expression '-' expression {
	arithbinop("sub", "sub", "fsub", &$$, $1, $3);
}

expression : expression EQUALEQUAL expression {cmpbinop("eq", &$$, $1, $3);}
expression : expression BANGEQUAL expression {cmpbinop("ne", &$$, $1, $3);}
expression : expression LESSEQUAL expression {cmpbinop("le", &$$, $1, $3);}
expression : expression GREATEREQUAL expression {cmpbinop("ge", &$$, $1, $3);}
expression : expression '<' expression {cmpbinop("lt", &$$, $1, $3);}
expression : expression '>' expression {cmpbinop("gt", &$$, $1, $3);}

expression : IDENTIFIER '=' expression {
	char tbuf[64];
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undeclared variable");
	}
	if (sym->t != $3.t) {
		yyerror("type mismatch");
	}
	type2str(tbuf, sym->t);
	$$ = $3;
	printf("\tstore %s %%tmp%d, ptr %%%s%d\n", tbuf, $3.var, $1, sym->n);
}

statement : '{' {pushscope();} block '}' {popscope();}

statement : ';';

statement : expression ';';

ifheader : '(' expression ')' {beginconditional($2);}

statement : IF ifheader statement %prec IFX {
	middleconditional();
	endconditional();
}

statement : IF ifheader statement ELSE {middleconditional();} statement {
	endconditional();
}

statement : WHILE {beginloop();} '(' expression ')' {middleloop($4);} statement {
	endloop();
}

statement : RETURN expression ';' {
	char tbuf[64];

	if ($2.t != I32T) {
		yyerror("type mismatch");
	}
	type2str(tbuf, $2.t);
	printf("\tret %s %%tmp%d\n", tbuf, $2.var);
}

statement : typename IDENTIFIER ';' {
	int n;
	char tbuf[64];
	struct symbol *sym;

	sym = symbolinfo($2);
	if (sym != NULL) {
		yyerror("already declared");
	}
	n = pushsymbol($2, $1);
	type2str(tbuf, $1);
	printf("\t%%%s%d = alloca %s\n", $2, n, tbuf);
}

block : ;

block : block statement;

/* XXX merge this with the next production */
declaration : typename IDENTIFIER '(' U0 ')' {
	char tbuf[64];
	struct function *node;

	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	pushfunction($2, $1, -1);
	type2str(tbuf, $1);
	pushscope();
	printf("define %s @%s() {\n", tbuf, $2);
} '{' block '}' {
	popscope();
	printf("}\n");
}

declaration : typename IDENTIFIER '(' typename IDENTIFIER ')' {
	int n;
	char tbuf1[64], tbuf2[64];
	struct function *node;

	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	pushfunction($2, $1, $4);
	type2str(tbuf1, $1);
	type2str(tbuf2, $4);
	pushscope();
	n = pushsymbol($5, $4);
	printf("define %s @%s(%s %%%s%dvar) {\n", tbuf1, $2, tbuf2, $5, n);
	printf("\t%%%s%d = alloca %s\n\tstore %s %%%s%dvar, ptr %%%s%d\n",
			$5, n, tbuf2, tbuf2, $5, n, $5, n);
} '{' block '}' {
	popscope();
	printf("}\n");
}

program : ;
program : program declaration;

%%

int
yyerror(const char *restrict msg)
{
	return fprintf(stderr, "line %d: %s\n", yylineno, msg);
}

void
pushscope(void)
{
	pushsymbol(NULL, 0);
}

void
popscope(void)
{
	struct symbol *ptr, *dead;

	ptr = symbols;
	while (ptr != NULL && ptr->id != NULL) {
		dead = ptr;
		ptr = ptr->next;
		free(dead->id);
		free(dead);
	}
	if (ptr == NULL)
		return;
	symbols = ptr->next;
	free(ptr);
}

int
pushsymbol(char *id, enum type t)
{
	struct symbol *new;

	new = malloc(sizeof(struct symbol));
	new->id = id;
	new->n = varctr++;
	new->t = t;
	new->next = symbols;
	symbols = new;
	return new->n;
}

struct symbol *
symbolinfo(char *id)
{
	struct symbol *ptr;

	for (ptr = symbols; ptr != NULL; ptr = ptr->next) {
		if (ptr->id == NULL)
			continue;
		if (strcmp(ptr->id, id) == 0)
			return ptr;
	}
	return NULL;
}

void
pushfunction(char *name, enum type result, enum type param)
{
	struct function *node;

	node = malloc(sizeof(struct function));
	node->name = name;
	node->result = result;
	node->param = param;
	node->next = functionlist;
	functionlist = node;
}

struct function *
functioninfo(char *name)
{
	struct function *node;

	for (node = functionlist; node != NULL; node = node->next)
		if (strcmp(node->name, name) == 0)
			return node;
	return NULL;
}

void
type2str(char *buf, enum type t)
{
	static const char *names[LAST_TYPE] = {
		[U1T] = "i1",
		[I32T] = "i32", [I64T] = "i64",
		[U32T] = "i32", [U64T] = "i64",
		[F32T] = "float", [F64T] = "double",
	};
	sprintf(buf, "%s", names[t]);
}

int
isunsigned(enum type t)
{
	return t == U32T || t == U64T;
}

int
isfloat(enum type t)
{
	return t == F32T || t == F64T;
}

void
binop(const char *restrict instr, YYSTYPE r, YYSTYPE s, YYSTYPE t)
{
	char tbuf[512];

	type2str(tbuf, r.expression.t);
	printf("\t%%tmp%d = %s %s %%tmp%d, %%tmp%d\n",
			r.expression.var, instr, tbuf,
			s.expression.var, t.expression.var);
}

void
pushlabel(int n)
{
	struct labelnode *l;

	l = malloc(sizeof(struct labelnode));
	l->n = n;
	l->next = labelstack;
	labelstack = l;
}

int
poplabel(void)
{
	int n;
	struct labelnode *l;

	if (labelstack == NULL)
		return -1;
	l = labelstack;
	n = l->n;
	labelstack = l->next;
	free(l);
	return n;
}

void
cast(struct expressionresult *r, struct expressionresult s,
		enum type desttyp)
{
	/* converting between numeric types */
	static const char *casttable[LAST_TYPE /* from */][LAST_TYPE /* to */] = {
		[U1T] = {
			[U1T] = "bitcast",
			[I32T] = "zext", [I64T] = "zext",
			[U32T] = "zext", [U64T] = "zext",
			[F32T] = "uitofp", [F64T] = "uitofp",
		},
		[I32T] = {
			[U1T] = "trunc",
			[I32T] = "bitcast", [I64T] = "sext",
			[U32T] = "bitcast", [U64T] = "zext",
			[F32T] = "sitofp", [F64T] = "sitofp",
		},
		[I64T] = {
			[U1T] = "trunc",
			[I32T] = "trunc", [I64T] = "bitcast",
			[U32T] = "trunc", [U64T] = "bitcast",
			[F32T] = "sitofp", [F64T] = "sitofp",
		},
		[U32T] = {
			[U1T] = "trunc",
			[I32T] = "bitcast", [I64T] = "sext",
			[U32T] = "bitcast", [U64T] = "zext",
			[F32T] = "uitofp", [F64T] = "uitofp",
		},
		[U64T] = {
			[U1T] = "trunc",
			[I32T] = "trunc", [I64T] = "bitcast",
			[U32T] = "trunc", [U64T] = "bitcast",
			[F32T] = "uitofp", [F64T] = "uitofp",
		},
		[F32T] = {
			[U1T] = "fptoui",
			[I32T] = "fptosi", [I64T] = "fptosi",
			[U32T] = "fptoui", [U64T] = "fptoui",
			[F32T] = "bitcast", [F64T] = "fpext",
		},
		[F64T] = {
			[U1T] = "fptoui",
			[I32T] = "fptosi", [I64T] = "fptosi",
			[U32T] = "fptoui", [U64T] = "fptoui",
			[F32T] = "fptrunc", [F64T] = "bitcast",
		},
	};
	const char *cast;
	char tbuf1[64], tbuf2[64];

	r->var = varctr++;
	r->t = desttyp;
	cast = casttable[s.t][desttyp];
	type2str(tbuf1, s.t);
	type2str(tbuf2, desttyp);
	printf("\t%%tmp%d = %s %s %%tmp%d to %s\n",
			r->var, cast, tbuf1, s.var, tbuf2);
}

void
arithbinop(const char *signedinstr, const char *unsignedinstr,
		const char *floatinstr, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t)
{
	char tbuf[64];
	const char *instr;

	if (s.t != t.t)
		yyerror("type mismatch");
	r->var = varctr++;
	r->t = s.t;
	if (isfloat(r->t)) {
		instr = floatinstr;
	} else if (isunsigned(r->t)) {
		instr = unsignedinstr;
	} else {
		instr = signedinstr;
	}
	type2str(tbuf, r->t);
	printf("\t%%tmp%d = %s %s %%tmp%d, %%tmp%d\n", r->var, instr, tbuf,
			s.var, t.var);
}

void
cmpbinop(const char *cond, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t)
{
	char instr, tbuf[64];
	const char *prefix;
	int isequality;

	if (s.t != t.t) {
		yyerror("type mismatch");
	}
	isequality = strcmp(cond, "eq") == 0 || strcmp(cond, "ne") == 0;
	if (s.t == U1T && !isequality) {
		yyerror("can't order booleans");
	}
	r->var = varctr++;
	r->t = U1T;
	instr = isfloat(r->t) ? 'f' : 'i';
	if (isfloat(r->t)) {
		prefix = "o";
	} else if (isequality) {
		prefix = "";
	} else if (isunsigned(r->t)) {
		prefix = "u";
	} else {
		prefix = "s";
	}
	type2str(tbuf, s.t);
	printf("\t%%tmp%d = %ccmp %s%s %s %%tmp%d, %%tmp%d\n", r->var, instr,
			prefix, cond, tbuf, s.var, t.var);
}

void
beginconditional(struct expressionresult cond)
{
	int label1, label2, label3;

	if (cond.t != U1T) {
		yyerror("conditions must be booleans");
	}
	label1 = varctr++;
	label2 = varctr++;
	label3 = varctr++;
	pushlabel(label2);
	pushlabel(label3);
	printf("\tbr i1 %%tmp%d, label %%l%d, label %%l%d\nl%d:\n",
			cond.var, label1, label2, label1);
}

void
middleconditional(void)
{
	int label2, label3;

	label3 = poplabel();
	label2 = poplabel();
	printf("\tbr label %%l%d\nl%d:\n", label3, label2);
	pushlabel(label3);
}

void
endconditional(void)
{
	int label3;

	label3 = poplabel();
	printf("\tbr label %%l%d\nl%d:\n", label3, label3);
}

void
beginloop(void)
{
	int label1, label2, label3;

	label1 = varctr++;
	label2 = varctr++;
	label3 = varctr++;
	pushlabel(label1);
	pushlabel(label2);
	pushlabel(label3);
	printf("\tbr label %%l%d\nl%d:\n", label1, label1);
}

void
middleloop(struct expressionresult cond)
{
	int label1, label2, label3;

	if (cond.t != U1T) {
		yyerror("conditions must be booleans");
	}
	label3 = poplabel();
	label2 = poplabel();
	label1 = poplabel();
	printf("\tbr i1 %%tmp%d, label %%l%d, label %%l%d\nl%d:\n",
			 cond.var, label2, label3, label2);
	pushlabel(label1);
	pushlabel(label3);
}

void
endloop(void)
{
	int label1, label3;

	label3 = poplabel();
	label1 = poplabel();
	printf("\tbr label %%l%d\nl%d:\n", label1, label3);
}


int
main()
{
#ifdef YYDEBUG
	yydebug = 1;
#endif
	return yyparse();
}
