/*
Current problems:
- error handling is bad
- all constants need to be explicitly cast
- the source code is just messy
- returns from u0 functions must be explicit
- casting to/from booleans: should it be "smart?"

Feature ideas:
- detect functions that do not return
- first-class arrays
- multidimensional arrays
- nested arrays
- compile-time array bounds checking
- function pointers
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
	int isarray;
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
static int pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t, int isarray);
/* return a pointer to the symbol, or NULL if it does not exist */
static struct symbol *symbolinfo(char id[MAX_IDENTIFIER_SIZE]);

/* list of functions */

struct function {
	char name[MAX_IDENTIFIER_SIZE];
	int nresults, nparams;
	struct type results[MAX_NPLE_SIZE], params[MAX_NPLE_SIZE];
	struct function *next;
};

/* currently implemented as an alist */
static struct function *functionlist;

/* add a function */
static void pushfunction(char name[MAX_IDENTIFIER_SIZE], int nresults,
		struct type *result, int nparams, struct type *param);
/* look up a function */
static struct function *functioninfo(char name[MAX_IDENTIFIER_SIZE]);

/* the current function's return type */

static int nrettypes;
static struct type rettypes[MAX_NPLE_SIZE];

/* type lists */

static int typelistlen(struct typelist *lst);
static struct typelist *snoctypelist(struct typelist *lst, struct type t,
		char ident[MAX_IDENTIFIER_SIZE]);
static void storetypelist(struct typelist *lst, struct type *results,
		char (*ident)[MAX_IDENTIFIER_SIZE]);

/* expression lists */

static int expressionlistlen(struct expressionlist *lst);
static struct expressionlist *snocexpressionlist(struct expressionlist *lst,
		int var, struct type t);
static void storeexpressionlist(struct expressionlist *lst,
		struct expressionresult *results);

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

static void printresultlltype(int nresults, struct type *results);
static void storei8(int ptr, int idx, char i8);
static int call(struct function *fn, int nargs, struct expressionresult *args,
		int returnsvalue);
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
	char strlit[MAX_STRLIT_SIZE];
	long int constant;
	/* parser outputs */
	struct type type;
	struct expressionresult expression;
	struct expressionlist *expressionlist;
	struct typelist *typelist;
}

%token <identifier> IDENTIFIER
%token <constant> CONSTANT
%token <strlit> STRING_LITERAL
/* types */
%token U0 U1 I32 I64 U32 U64 F32 F64
/* expressions */
%token CAST
%token PRINTF
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
%type <expression> expression expression_0 lvalue
%type <typelist> anon_nple anon_nple_nonempty named_nple named_nple_nonempty
%type <expressionlist> expression_nple expression_nple_nonempty
%type <expressionlist> lvalue_nple_2plus

%expect 1

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

expression_0 : lvalue {
	$$.var = varctr++;
	$$.t = $1.t;
	printf("\t%%tmp%d = load %s, ptr %%tmp%d\n",
			$$.var, $1.t.lltype, $1.var);
}

expression_0 : CONSTANT {
	$$.var = varctr++;
	$$.t = i64t;
	strcpy($$.t.lltype, "i64");
	printf("\t%%tmp%d = add %s %lu, 0\n", $$.var, $$.t.lltype, $1);
}

expression_0 : CAST '(' expression ',' typename ')' {cast(&$$, $3, $5);}

expression_0 : IDENTIFIER '(' expression_nple ')' {
	int i;
	int narguments;
	struct function *node;

	narguments = expressionlistlen($3);
	struct expressionresult arguments[narguments];
	storeexpressionlist($3, arguments);
	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (narguments != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = 0; i < narguments; i++) {
		if (node->params[i].tag != arguments[i].t.tag) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != 1) {
		yyerror("function result count ≠ 1");
	}
	$$.t = node->results[0];
	$$.var = call(node, narguments, arguments, 1);
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

lvalue : IDENTIFIER {
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undeclared variable");
	}
	if (sym->isarray) {
		yyerror("cannot assign an array itself");
	}
	$$.var = varctr++;
	$$.t = sym->t;
	printf("\t%%tmp%d = getelementptr %s, ptr %%%s%d, i32 0\n",
			$$.var, sym->t.lltype, $1, sym->n);
}
lvalue : IDENTIFIER '[' expression ']' {
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undeclared variable");
	}
	if (!sym->isarray) {
		yyerror("cannot subscript assign a scalar");
	}
	if (isfloat($3.t) || isunsigned($3.t)) {
		yyerror("subscripts must be signed integers");
	}
	$$.var = varctr++;
	$$.t = sym->t;
	printf("\t%%tmp%d = getelementptr %s, ptr %%%s%d, %s %%tmp%d\n",
			$$.var, sym->t.lltype, $1, sym->n, $3.t.lltype, $3.var);
}

expression : lvalue '=' expression {
	if ($1.t.tag != $3.t.tag) {
		yyerror("type mismatch");
	}
	$$ = $3;
	printf("\tstore %s %%tmp%d, ptr %%tmp%d\n",
			$1.t.lltype, $3.var, $1.var);
}

expression_nple : {$$ = NULL;}
expression_nple : expression_nple_nonempty {$$ = $1;}
expression_nple_nonempty : expression {
	$$ = snocexpressionlist(NULL, $1.var, $1.t);
}
expression_nple_nonempty : expression_nple_nonempty ',' expression {
	$$ = snocexpressionlist($1, $3.var, $3.t);
}

statement : '{' {pushscope();} block '}' {popscope();}

statement : ';';

statement : expression ';';

statement : IDENTIFIER '(' expression_nple ')' ';' {
	int i;
	int narguments;
	struct function *node;

	narguments = expressionlistlen($3);
	struct expressionresult arguments[narguments];
	storeexpressionlist($3, arguments);
	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (narguments != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = 0; i < narguments; i++) {
		if (node->params[i].tag != arguments[i].t.tag) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != 0) {
		yyerror("function result count ≠ 0");
	}
	call(node, narguments, arguments, 0);
}

statement : lvalue_nple_2plus '=' IDENTIFIER '(' expression_nple ')' ';' {
	int i;
	int narguments, nresults;
	int agg, tmp;
	struct function *node;

	/* store nples */
	narguments = expressionlistlen($5);
	nresults = expressionlistlen($1);
	struct expressionresult results[nresults], arguments[narguments];
	storeexpressionlist($5, arguments);
	storeexpressionlist($1, results);
	/* get function info */
	node = functioninfo($3);
	/* check function */
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (narguments != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = 0; i < narguments; i++) {
		if (node->params[i].tag != arguments[i].t.tag) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != nresults) {
		yyerror("function result count does not match number of "
				"identifiers");
	}
	/* check results */
	for (i = 0; i < nresults; i++) {
		if (results[i].t.tag != node->results[i].tag) {
			yyerror("result type mismtach");
		}
	}
	/* write the instructions */
	agg = call(node, narguments, arguments, 1);
	for (i = 0; i < nresults; i++) {
		tmp = varctr++;
		printf("\t%%tmp%d = extractvalue ", tmp);
		printresultlltype(nresults, node->results);
		printf("%%tmp%d, %d\n", agg, i);
		printf("\tstore %s %%tmp%d, ptr %%tmp%d\n",
				results[i].t.lltype, tmp, results[i].var);
	}
}

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

statement : RETURN expression_nple ';' {
	int i, nresults, agg, lastagg;

	nresults = expressionlistlen($2);
	struct expressionresult results[nresults];
	storeexpressionlist($2, results);
	if (nrettypes != nresults) {
		yyerror("return type count mismatch");
	}
	for (i = 0; i < nresults; i++) {
		if (results[i].t.tag != rettypes[i].tag) {
			yyerror("return type mismatch");
		}
	}
	if (nresults == 0) {
		printf("\tret void\n");
	} else if (nresults == 1) {
		printf("\tret %s %%tmp%d\n",
				results[0].t.lltype, results[0].var);
	} else {
		agg = varctr++;
		printf("\t%%tmp%d = insertvalue ", agg);
		printresultlltype(nresults, rettypes);
		printf(" undef, %s %%tmp%d, 0\n",
				rettypes[0].lltype, results[0].var);
		for (i = 1, lastagg = agg, agg = varctr++; i < nresults;
				i++, lastagg = agg, agg = varctr++) {
			printf("\t%%tmp%d = insertvalue ", agg);
			printresultlltype(nresults, rettypes);
			printf(" %%tmp%d, %s %%tmp%d, %d\n",
					lastagg, rettypes[i].lltype,
					results[i].var, i);
		}
		printf("\tret ");
		printresultlltype(nresults, rettypes);
		printf(" %%tmp%d\n", lastagg);
	}
}

statement : typename IDENTIFIER ';' {
	int n;
	struct symbol *sym;

	sym = symbolinfo($2);
	if (sym != NULL) {
		yyerror("already declared");
	}
	n = pushsymbol($2, $1, 0);
	printf("\t%%%s%d = alloca %s\n", $2, n, $1.lltype);
}

statement : typename IDENTIFIER '[' expression ']' ';' {
	int n;
	struct symbol *sym;

	sym = symbolinfo($2);
	if (sym != NULL) {
		yyerror("already declared");
	}
	if (isfloat($4.t) || isunsigned($4.t)) {
		yyerror("subscripts must be signed integers");
	}
	n = pushsymbol($2, $1, 1);
	printf("\t%%%s%d = alloca %s, %s %%tmp%d\n",
			$2, n, $1.lltype, $4.t.lltype, $4.var);
}

statement : PRINTF '(' STRING_LITERAL ',' expression_nple ')' ';' {
	int i, len, nargs, strlit;

	len = strlen($3);
	nargs = expressionlistlen($5);
	struct expressionresult args[nargs];
	storeexpressionlist($5, args);
	/* store the string literal */
	strlit = varctr++;
	printf("\t%%tmp%d = alloca i8, i32 %d\n", strlit, len + 1);
	for (i = 0; i < len; i++)
		storei8(strlit, i, $3[i]);
	storei8(strlit, len, '\0');
	/* call printf */
	printf("\tcall i32(ptr, ...) @printf(ptr %%tmp%d", strlit);
	for (i = 0; i < nargs; i++) {
		printf(", %s %%tmp%d", args[i].t.lltype, args[i].var);
	}
	printf(")\n");
}

block : ;

block : block statement;

anon_nple : U0 {$$ = NULL;}
anon_nple : anon_nple_nonempty {$$ = $1;}
anon_nple_nonempty : typename {
	char nil[MAX_IDENTIFIER_SIZE];

	nil[0] = '\0';
	$$ = snoctypelist(NULL, $1, nil);
}
anon_nple_nonempty : anon_nple_nonempty ',' typename {
	char nil[MAX_IDENTIFIER_SIZE];

	nil[0] = '\0';
	$$ = snoctypelist($1, $3, nil);
}

lvalue_nple_2plus : lvalue ',' lvalue {
	$$ = snocexpressionlist(NULL, $1.var, $1.t);
	$$ = snocexpressionlist($$, $3.var, $3.t);
}
lvalue_nple_2plus : lvalue_nple_2plus ',' lvalue {
	$$ = snocexpressionlist($1, $3.var, $3.t);
}

named_nple : U0 {$$ = NULL;}
named_nple : named_nple_nonempty {$$ = $1;}
named_nple_nonempty : typename IDENTIFIER {
	$$ = snoctypelist(NULL, $1, $2);
}
named_nple_nonempty : named_nple_nonempty ',' typename IDENTIFIER {
	$$ = snoctypelist($1, $3, $4);
}

declaration : anon_nple IDENTIFIER '(' named_nple ')' {
	int i;
	int nparams, nresults;
	struct function *node;

	nresults = typelistlen($1);
	nparams = typelistlen($4);
	struct type params[nparams], results[nresults];
	char names[nparams][MAX_IDENTIFIER_SIZE];
	int nums[nparams];
	storetypelist($1, results, NULL);
	storetypelist($4, params, names);
	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	pushfunction($2, nresults, results, nparams, params);
	pushscope();
	nrettypes = nresults;
	memcpy(rettypes, results, sizeof(struct type) * nresults);
	printf("define ");
	printresultlltype(nresults, results);
	printf(" @%s(", $2);
	for (i = 0; i < nparams; i++) {
		if (i != 0) {
			printf(", ");
		}
		nums[i] = pushsymbol(names[i], params[i], 0);
		printf("%s %%%s%dvar", params[i].lltype, names[i], nums[i]);
	}
	printf(") {\n");
	for (i = 0; i < nparams; i++) {
		printf("\t%%%s%d = alloca %s\n",
				names[i], nums[i], params[i].lltype);
		printf("\tstore %s %%%s%dvar, ptr %%%s%d\n", params[i].lltype,
				names[i], nums[i], names[i], nums[i]);
	}
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
	pushsymbol(nil, t, 0);
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
pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t, int isarray)
{
	struct symbol *new;

	new = malloc(sizeof(struct symbol));
	strcpy(new->id, id);
	new->n = varctr++;
	new->isarray = isarray;
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
pushfunction(char name[MAX_IDENTIFIER_SIZE], int nresults, struct type *results,
		int nparams, struct type *params)
{
	struct function *node;

	node = malloc(sizeof(struct function));
	strcpy(node->name, name);
	node->nresults = nresults;
	memcpy(node->results, results, sizeof(struct type) * nresults);
	node->nparams = nparams;
	memcpy(node->params, params, sizeof(struct type) * nparams);
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

int
typelistlen(struct typelist *lst)
{
	int i;

	for (i = 0; lst != NULL; lst = lst->next, i++);
	return i;
}

struct typelist *
snoctypelist(struct typelist *lst, struct type t,
		char ident[MAX_IDENTIFIER_SIZE])
{
	struct typelist *result;

	result = malloc(sizeof(struct typelist));
	result->next = lst;
	result->t = t;
	strcpy(result->ident, ident);
	return result;
}

void
storetypelist(struct typelist *lst, struct type *results,
		char (*ident)[MAX_IDENTIFIER_SIZE])
{
	int len;
	struct typelist *ptr, *dead;

	if (lst == NULL)
		return;
	len = typelistlen(lst);
	for (ptr = lst, len--; ptr != NULL;
			dead = ptr, ptr = ptr->next, free(dead), len--) {
		if (results) {
			results[len] = ptr->t;
		}
		if (ident) {
			strcpy(ident[len], ptr->ident);
		}
	}
}

int
expressionlistlen(struct expressionlist *lst)
{
	int i;

	i = 0;
	while (lst != NULL) {
		lst = lst->next;
		i++;
	}
	return i;
}

struct expressionlist *
snocexpressionlist(struct expressionlist *lst, int var, struct type t)
{
	struct expressionlist *result;

	result = malloc(sizeof(struct expressionlist));
	result->next = lst;
	result->var = var;
	result->t = t;
	return result;
}

void
storeexpressionlist(struct expressionlist *lst,
		struct expressionresult *results)
{
	int len;
	struct expressionlist *ptr, *dead;

	if (lst == NULL)
		return;
	len = expressionlistlen(lst);
	for (ptr = lst, len--; ptr != NULL;
			dead = ptr, ptr = ptr->next, free(dead), len--) {
		results[len].var = ptr->var;
		results[len].t = ptr->t;
	}
}

void
printresultlltype(int nresults, struct type *results)
{
	int i;

	if (nresults == 0) {
		printf("void");
		return;
	}
	if (nresults == 1) {
		printf("%s", results[0].lltype);
		return;
	}
	printf("{");
	for (i = 0; i < nresults; i++) {
		if (i != 0)
			printf(", ");
		printf("%s", results[i].lltype);
	}
	printf("}");
}

void
storei8(int ptr, int idx, char i8)
{
	int elemptr;

	elemptr = varctr++;
	printf("\t%%tmp%d = getelementptr i8, ptr %%tmp%d, i32 %d\n",
			elemptr, ptr, idx);
	printf("\tstore i8 u0x%x, ptr %%tmp%d\n",
			i8, elemptr);
}

int
call(struct function *fn, int nargs, struct expressionresult *args,
		int returnsvalue)
{
	int i, result;

	printf("\t");
	if (returnsvalue) {
		result = varctr++;
		printf("%%tmp%d = ", result);
	} else {
		result = -1;
	}
	printf("call ");
	printresultlltype(fn->nresults, fn->results);
	printf(" @%s(", fn->name);
	for (i = 0; i < nargs; i++) {
		if (i != 0) {
			printf(", ");
		}
		printf("%s %%tmp%d", args[i].t.lltype, args[i].var);
	}
	printf(")\n");
	return result;
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
	printf("declare i32 @printf(i8* noalias nocapture, ...)\n");
	return yyparse();
}
