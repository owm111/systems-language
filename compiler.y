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
	char id[MAX_IDENTIFIER_SIZE]; /* actual name in user code */
	int n; /* unique identifier to avoid capturing */
	struct type t;
	struct symbol *next;
};

/* currently implemented as an alist */
static struct symbol *symbols;

/* create a new scope (this pushes a symbol NULL to the list) */
static void pushscope(void);
/* delete the last scope (this pops everything until the next NULL) */
static void popscope(void);
/* add a symbol to the list and return a unique identifier */
static int pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t);
/* return a pointer to the symbol, or NULL if it does not exist */
static struct symbol *symbolinfo(char id[MAX_IDENTIFIER_SIZE]);

/* list of functions */

struct function {
	char name[MAX_IDENTIFIER_SIZE];
	struct type result, param;
	struct function *next;
};

/* currently implemented as an alist */
static struct function *functionlist;

/* add a function */
static void pushfunction(char name[MAX_IDENTIFIER_SIZE], struct type result,
		struct type param);
/* look up a function */
static struct function *functioninfo(char name[MAX_IDENTIFIER_SIZE]);

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

/* is this an unsigned, integral type? */
static int isunsigned(struct type t);
/* is this a floating-point, numeric type? */
static int isfloat(struct type t);

/* generating code */

static void cast(struct expressionresult *r, struct expressionresult s,
		struct type desttyp);
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
	char identifier[MAX_IDENTIFIER_SIZE];
	long int constant;
	/* parser outputs */
	struct type type;
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

typename : U1  {$$ = u1t;}
typename : I32 {$$ = i32t;}
typename : I64 {$$ = i64t;}
typename : U32 {$$ = u32t;}
typename : U64 {$$ = u64t;}
typename : F32 {$$ = f32t;}
typename : F64 {$$ = f64t;}

expression_0 : '(' expression ')' {
	$$ = $2;
}

expression_0 : IDENTIFIER {
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undefined variable");
	}
	$$.var = varctr++;
	$$.t = sym->t;
	printf("\t%%tmp%d = load %s, ptr %%%s%d\n",
			$$.var, sym->t.lltype, $1, sym->n);
}

expression_0 : CONSTANT {
	$$.var = varctr++;
	$$.t = i64t;
	strcpy($$.t.lltype, "i64");
	printf("\t%%tmp%d = add %s %lu, 0\n", $$.var, $$.t.lltype, $1);
}

expression_0 : CAST '(' expression ',' typename ')' {cast(&$$, $3, $5);}

expression_0 : IDENTIFIER '(' expression ')' {
	struct function *node;

	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (node->param.tag != $3.t.tag) {
		yyerror("function argument type mismatch");
	}
	$$.t = node->result;
	$$.var = varctr++;
	printf("\t%%tmp%d = call %s @%s(%s %%tmp%d)\n",
			$$.var, $$.t.lltype, $1, $3.t.lltype, $3.var);
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
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undeclared variable");
	}
	if (sym->t.tag != $3.t.tag) {
		yyerror("type mismatch");
	}
	$$ = $3;
	printf("\tstore %s %%tmp%d, ptr %%%s%d\n",
			sym->t.lltype, $3.var, $1, sym->n);
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
	if ($2.t.tag != I32T) {
		yyerror("type mismatch");
	}
	printf("\tret %s %%tmp%d\n", $2.t.lltype, $2.var);
}

statement : typename IDENTIFIER ';' {
	int n;
	struct symbol *sym;

	sym = symbolinfo($2);
	if (sym != NULL) {
		yyerror("already declared");
	}
	n = pushsymbol($2, $1);
	printf("\t%%%s%d = alloca %s\n", $2, n, $1.lltype);
}

block : ;

block : block statement;

/* XXX merge this with the next production */
declaration : typename IDENTIFIER '(' U0 ')' {
	struct type unit;
	struct function *node;

	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	unit.tag = LAST_TYPE;
	pushfunction($2, $1, unit);
	pushscope();
	printf("define %s @%s() {\n", $1.lltype, $2);
} '{' block '}' {
	popscope();
	printf("}\n");
}

declaration : typename IDENTIFIER '(' typename IDENTIFIER ')' {
	int n;
	struct function *node;

	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	pushfunction($2, $1, $4);
	pushscope();
	n = pushsymbol($5, $4);
	printf("define %s @%s(%s %%%s%dvar) {\n",
			$1.lltype, $2, $4.lltype, $5, n);
	printf("\t%%%s%d = alloca %s\n\tstore %s %%%s%dvar, ptr %%%s%d\n",
			$5, n, $4.lltype, $4.lltype, $5, n, $5, n);
} '{' block '}' {
	popscope();
	printf("}\n");
}

program : ;
program : program declaration;

%%

const struct type u1t  = {.tag = U1T,  .lltype = "i1"};
const struct type i32t = {.tag = I32T, .lltype = "i32"};
const struct type i64t = {.tag = I64T, .lltype = "i64"};
const struct type u32t = {.tag = U32T, .lltype = "i32"};
const struct type u64t = {.tag = U64T, .lltype = "i64"};
const struct type f32t = {.tag = F32T, .lltype = "float"};
const struct type f64t = {.tag = F64T, .lltype = "double"};

int
yyerror(const char *restrict msg)
{
	return fprintf(stderr, "line %d: %s\n", yylineno, msg);
}

void
pushscope(void)
{
	char nil[MAX_IDENTIFIER_SIZE];
	struct type t;

	nil[0] = '\0';
	t.tag = LAST_TYPE;
	pushsymbol(nil, t);
}

void
popscope(void)
{
	struct symbol *ptr, *dead;

	ptr = symbols;
	while (ptr != NULL && ptr->id[0] != '\0') {
		dead = ptr;
		ptr = ptr->next;
		free(dead);
	}
	if (ptr == NULL)
		return;
	symbols = ptr->next;
	free(ptr);
}

int
pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t)
{
	struct symbol *new;

	new = malloc(sizeof(struct symbol));
	strcpy(new->id, id);
	new->n = varctr++;
	new->t = t;
	new->next = symbols;
	symbols = new;
	return new->n;
}

struct symbol *
symbolinfo(char id[MAX_IDENTIFIER_SIZE])
{
	struct symbol *ptr;

	for (ptr = symbols; ptr != NULL; ptr = ptr->next) {
		if (ptr->id[0] == '\0')
			continue;
		if (strcmp(ptr->id, id) == 0)
			return ptr;
	}
	return NULL;
}

void
pushfunction(char name[MAX_IDENTIFIER_SIZE], struct type result,
		struct type param)
{
	struct function *node;

	node = malloc(sizeof(struct function));
	strcpy(node->name, name);
	node->result = result;
	node->param = param;
	node->next = functionlist;
	functionlist = node;
}

struct function *
functioninfo(char name[MAX_IDENTIFIER_SIZE])
{
	struct function *node;

	for (node = functionlist; node != NULL; node = node->next)
		if (strcmp(node->name, name) == 0)
			return node;
	return NULL;
}

int
isunsigned(struct type t)
{
	return t.tag == U32T || t.tag == U64T;
}

int
isfloat(struct type t)
{
	return t.tag == F32T || t.tag == F64T;
}

void
binop(const char *restrict instr, YYSTYPE r, YYSTYPE s, YYSTYPE t)
{
	printf("\t%%tmp%d = %s %s %%tmp%d, %%tmp%d\n",
			r.expression.var, instr, r.expression.t.lltype,
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
		struct type desttyp)
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

	r->var = varctr++;
	r->t = desttyp;
	cast = casttable[s.t.tag][desttyp.tag];
	printf("\t%%tmp%d = %s %s %%tmp%d to %s\n",
			r->var, cast, s.t.lltype, s.var, desttyp.lltype);
}

void
arithbinop(const char *signedinstr, const char *unsignedinstr,
		const char *floatinstr, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t)
{
	const char *instr;

	if (s.t.tag != t.t.tag)
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
	printf("\t%%tmp%d = %s %s %%tmp%d, %%tmp%d\n",
			r->var, instr, r->t.lltype, s.var, t.var);
}

void
cmpbinop(const char *cond, struct expressionresult *r,
		struct expressionresult s, struct expressionresult t)
{
	char instr;
	const char *prefix;
	int isequality;

	if (s.t.tag != t.t.tag) {
		yyerror("type mismatch");
	}
	isequality = strcmp(cond, "eq") == 0 || strcmp(cond, "ne") == 0;
	if (s.t.tag == U1T && !isequality) {
		yyerror("can't order booleans");
	}
	r->var = varctr++;
	r->t = u1t;
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
	printf("\t%%tmp%d = %ccmp %s%s %s %%tmp%d, %%tmp%d\n",
			r->var, instr, prefix, cond, s.t.lltype, s.var, t.var);
}

void
beginconditional(struct expressionresult cond)
{
	int label1, label2, label3;

	if (cond.t.tag != U1T) {
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

	if (cond.t.tag != U1T) {
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
