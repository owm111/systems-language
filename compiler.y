/*
Current problems:
- error handling is bad
- all constants need to be explicitly cast
- the source code is just messy
- casting to/from booleans: should it be "smart?"

Feature ideas:
- detect functions that do not return
- structure types
- union types
- array size given by expressions
- array slicing
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

static unsigned int mkhash(const char *key);

/* single counter for giving unique names to everything */
int varctr;

/* symbol table */

/* a hash table would probably be faster in theory, but i'm not sure
how to deal with shadowing using a hash table but not using a stack or
two to track scopes */

struct symbol {
	char id[MAX_IDENTIFIER_SIZE]; /* actual name in user code */
	int n; /* unique identifier to avoid capturing */
	struct type t;
};

/* currently implemented an array that stores a stack */
static struct symbol symbols[MAX_SYMBOL_COUNT];
static int nsymbols;

/* create a new scope (this pushes a symbol NULL to the list) */
static void pushscope(void);
/* delete the last scope (this pops everything until the next NULL) */
static void popscope(void);
/* add a symbol to the list and return a unique identifier */
static int pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t);
/* return a pointer to the symbol, or NULL if it does not exist */
static struct symbol *symbolinfo(char id[MAX_IDENTIFIER_SIZE]);

/* list of functions */

struct param {
	char name[MAX_IDENTIFIER_SIZE];
	struct type type;
};
struct function {
	char name[MAX_IDENTIFIER_SIZE];
	int nresults, nparams;
	struct type results[MAX_NPLE_SIZE];
	struct param params[MAX_NPLE_SIZE];
};

/* currently implemented as a hash table */
static struct function functiontable[MAX_FUNCTION_COUNT];
static int lookupfunction(const char *name);

/* add a function */
static void pushfunction(char name[MAX_IDENTIFIER_SIZE]);
/* look up a function */
static struct function *functioninfo(char name[MAX_IDENTIFIER_SIZE]);

/* the current function's return type */

static int nrettypes;
static struct type rettypes[MAX_NPLE_SIZE];

/* the current function's parameters */

static int nparams;
static struct param params[MAX_NPLE_SIZE];

/* stack of expression results (for fn call args, return stmts, etc.) */

static struct expressionresult expressions[MAX_EXPRESSION_COUNT];
static int nexpressions;

/* Expressions and Lvalues */

/*
Expressions and lvalues are passed around by the name of a temporary
variable and their type. What that temporary variable contains is
determined by its type and where it is used.

- Lvalues for base types store a pointer to the actual value.
- Lvalues for array references store the pointer to the array.
- Expressions for base types store the value itself.
- Expressions for array references store the pointer to the array.
*/

/* stack of labels */

/* this is needed to save labels for conditionals, loops, etc. between
actions */

/* only stores the number in the label's name */
/* currently implemented as an array that contains a stack */
static int labels[MAX_LABEL_COUNT];
static int nlabels;

static void pushlabel(int);
static int poplabel(void);

/* utilities for working with types */

/* are these types the same? */
static int aretypesequal(struct type t1, struct type t2);
/* is this an array reference type? */
static int isarrayref(struct type t);
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
	int arrayspec[MAX_ARRAY_DIMS];
	struct expressionresult expression;
	int expressionlistidx;
}

%token <identifier> IDENTIFIER
%token <constant> CONSTANT
%token <strlit> STRING_LITERAL
/* types */
%token U0 U1 I32 I64 U32 U64 F32 F64
%token REF
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

%type <type> basetype typename
%type <arrayspec> arrayspec
%type <expression> expression expression_0 lvalue
%type <expressionlistidx> expression_nple expression_nple_nonempty
%type <expressionlistidx> lvalue_nple_2plus

%expect 1

%start program

%%

basetype : U1  {$$ = u1t;}
basetype : I32 {$$ = i32t;}
basetype : I64 {$$ = i64t;}
basetype : U32 {$$ = u32t;}
basetype : U64 {$$ = u64t;}
basetype : F32 {$$ = f32t;}
basetype : F64 {$$ = f64t;}

arrayspec : '[' CONSTANT ']' {
	int i;

	$$[0] = $2;
	for (i = 1; i < MAX_ARRAY_DIMS; i++)
		$$[i] = 0;
}
arrayspec : arrayspec '[' CONSTANT ']' {
	int i;

	for (i = 0; $1[i] != 0; i++)
		$$[i] = $1[i];
	$$[i++] = $3;
	for (; i < MAX_ARRAY_DIMS; i++)
		$$[i] = 0;
}

typename : basetype {$$ = $1;}
typename : REF basetype arrayspec {
	int i;

	$$ = $2;
	for (i = 0; i < MAX_ARRAY_DIMS; i++)
		$$.dimension[i] = $3[i];
}

lvalue : IDENTIFIER {
	struct symbol *sym;

	sym = symbolinfo($1);
	if (sym == NULL) {
		yyerror("undeclared variable");
	}
	$$.var = varctr++;
	$$.t = sym->t;
	printf("\t%%tmp%d = getelementptr %s, ptr %%%s%d, i32 0\n",
			$$.var, sym->t.lltype, $1, sym->n);
}
lvalue : expression_0 '[' expression ']' {
	int i, remainingproduct, tmp;

	if (!isarrayref($1.t)) {
		yyerror("cannot subscript assign a scalar");
	}
	if (isfloat($3.t) || isunsigned($3.t)) {
		yyerror("subscripts must be signed integers");
	}
	$$.var = varctr++;
	$$.t = $1.t;
	for (i = 1; i < MAX_ARRAY_DIMS; i++)
		$$.t.dimension[i - 1] = $$.t.dimension[i];
	$$.t.dimension[MAX_ARRAY_DIMS - 1] = 0;
	remainingproduct = 1;
	for (i = 0; $$.t.dimension[i] != 0; i++)
		remainingproduct *= $$.t.dimension[i];
	tmp = varctr++;
	printf("\t%%tmp%d = mul %s %%tmp%d, %d\n",
			tmp, $3.t.lltype, $3.var, remainingproduct);
	printf("\t%%tmp%d = getelementptr %s, ptr %%tmp%d, %s %%tmp%d\n",
			$$.var, $1.t.lltype, $1.var, $3.t.lltype, tmp);
}

expression_0 : '(' expression ')' {
	$$ = $2;
}

expression_0 : lvalue {
	if (isarrayref($1.t)) {
		$$ = $1;
	} else {
		$$.var = varctr++;
		$$.t = $1.t;
		printf("\t%%tmp%d = load %s, ptr %%tmp%d\n",
				$$.var, $1.t.lltype, $1.var);
	}
}

expression_0 : CONSTANT {
	$$.var = varctr++;
	$$.t = i64t;
	printf("\t%%tmp%d = add %s %lu, 0\n", $$.var, $$.t.lltype, $1);
}

expression_0 : CAST '(' expression ',' typename ')' {cast(&$$, $3, $5);}

expression_0 : IDENTIFIER '(' expression_nple ')' {
	int i;
	struct function *node;

	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (nexpressions - $3 != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = $3; i < nexpressions; i++) {
		if (!aretypesequal(node->params[i].type, expressions[i].t)) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != 1) {
		yyerror("function result count ≠ 1");
	}
	$$.t = node->results[0];
	$$.var = call(node, nexpressions - $3, &expressions[$3], 1);
	nexpressions = $3;
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

expression : lvalue '=' expression {
	if (!aretypesequal($1.t, $3.t)) {
		yyerror("type mismatch");
	}
	if (isarrayref($1.t)) {
		yyerror("cannot assign array references");
	}
	$$ = $3;
	printf("\tstore %s %%tmp%d, ptr %%tmp%d\n",
			$1.t.lltype, $3.var, $1.var);
}

expression_nple : {$$ = nexpressions;}
expression_nple : expression_nple_nonempty {$$ = $1;}
expression_nple_nonempty : expression {
	$$ = nexpressions;
	expressions[nexpressions].var = $1.var;
	expressions[nexpressions].t = $1.t;
	nexpressions++;
}
expression_nple_nonempty : expression_nple_nonempty ',' expression {
	$$ = $1;
	expressions[nexpressions].var = $3.var;
	expressions[nexpressions].t = $3.t;
	nexpressions++;
}

statement : '{' {pushscope();} block '}' {popscope();}

statement : ';';

statement : expression ';';

statement : IDENTIFIER '(' expression_nple ')' ';' {
	int i;
	struct function *node;

	node = functioninfo($1);
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (nexpressions - $3 != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = $3; i < nexpressions; i++) {
		if (!aretypesequal(node->params[i].type, expressions[i].t)) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != 0) {
		yyerror("function result count ≠ 0");
	}
	call(node, nexpressions - $3, &expressions[$3], 0);
	nexpressions = $3;
}

statement : lvalue_nple_2plus '=' IDENTIFIER '(' expression_nple ')' ';' {
	int i, j;
	int agg, tmp;
	struct function *node;

	/* get function info */
	node = functioninfo($3);
	/* check function */
	if (node == NULL) {
		yyerror("undeclared function");
	}
	if (nexpressions - $5 != node->nparams) {
		yyerror("function argument number mismatch");
	}
	for (i = $5; i < nexpressions - $5; i++) {
		if (!aretypesequal(node->params[i].type, expressions[i].t)) {
			yyerror("function argument type mismatch");
		}
	}
	if (node->nresults != $5 - $1) {
		yyerror("function result count does not match number of "
				"identifiers");
	}
	/* check results */
	for (i = $1; i < $5; i++) {
		if (!aretypesequal(expressions[i].t, node->results[i])) {
			yyerror("result type mismtach");
		}
	}
	/* write the instructions */
	agg = call(node, nexpressions - $5, &expressions[$5], 1);
	for (i = $1, j = 0; i < $5; i++, j++) {
		tmp = varctr++;
		printf("\t%%tmp%d = extractvalue ", tmp);
		printresultlltype(node->nresults, node->results);
		printf("%%tmp%d, %d\n", agg, j);
		printf("\tstore %s %%tmp%d, ptr %%tmp%d\n",
				expressions[i].t.lltype, tmp, expressions[i].var);
	}
	nexpressions = $1;
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
	int i, j, agg, lastagg;

	if (nrettypes != nexpressions - $2) {
		yyerror("return type count mismatch");
	}
	for (i = $2; i < nexpressions; i++) {
		if (!aretypesequal(expressions[i].t, rettypes[i])) {
			yyerror("return type mismatch");
		}
	}
	if (nexpressions - $2 == 0) {
		printf("\tret void\n");
	} else if (nexpressions - $2 == 1) {
		printf("\tret %s %%tmp%d\n",
				expressions[$2].t.lltype, expressions[$2].var);
	} else {
		agg = varctr++;
		printf("\t%%tmp%d = insertvalue ", agg);
		printresultlltype(nrettypes, rettypes);
		printf(" undef, %s %%tmp%d, 0\n",
				expressions[$2].t.lltype, expressions[$2].var);
		for (i = $2 + 1, j = 1, lastagg = agg, agg = varctr++;
				i < nexpressions;
				i++, j++, lastagg = agg, agg = varctr++) {
			printf("\t%%tmp%d = insertvalue ", agg);
			printresultlltype(nrettypes, rettypes);
			printf(" %%tmp%d, %s %%tmp%d, %d\n",
					lastagg, expressions[i].t.lltype,
					expressions[i].var, j);
		}
		printf("\tret ");
		printresultlltype(nrettypes, rettypes);
		printf(" %%tmp%d\n", lastagg);
	}
	nexpressions = $2;
}

/*
The first form declares a scalar identifier, while the second form
declares an array. The second form produces an array reference.
*/

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

statement : typename IDENTIFIER arrayspec ';' {
	int i, n, product;
	struct symbol *sym;

	sym = symbolinfo($2);
	if (sym != NULL) {
		yyerror("already declared");
	}
	for (i = 0, product = 1; $3[i] != 0; i++) {
		product *= $3[i];
		$1.dimension[i] = $3[i];
	}
	n = pushsymbol($2, $1);
	printf("\t%%%s%d = alloca %s, i32 %d\n",
			$2, n, $1.lltype, product);
}

statement : PRINTF '(' STRING_LITERAL ',' expression_nple ')' ';' {
	int i, len, strlit;

	len = strlen($3);
	/* store the string literal */
	strlit = varctr++;
	printf("\t%%tmp%d = alloca i8, i32 %d\n", strlit, len + 1);
	for (i = 0; i < len; i++)
		storei8(strlit, i, $3[i]);
	storei8(strlit, len, '\0');
	/* call printf */
	printf("\tcall i32(ptr, ...) @printf(ptr %%tmp%d", strlit);
	for (i = $5; i < nexpressions; i++) {
		printf(", %s %%tmp%d", expressions[i].t.lltype,
				expressions[i].var);
	}
	printf(")\n");
	nexpressions = $5;
}

block : ;

block : block statement;

result_nple : U0 {nrettypes = 0;}
result_nple : nonempty_result_nple ;
nonempty_result_nple : basetype {
	nrettypes = 1;
	rettypes[0] = $1;
}
nonempty_result_nple : nonempty_result_nple ',' basetype {
	rettypes[nrettypes++] = $3;
}

lvalue_nple_2plus : lvalue ',' lvalue {
	$$ = nexpressions;
	expressions[nexpressions].var = $1.var;
	expressions[nexpressions].t = $1.t;
	nexpressions++;
	expressions[nexpressions].var = $3.var;
	expressions[nexpressions].t = $3.t;
	nexpressions++;
}
lvalue_nple_2plus : lvalue_nple_2plus ',' lvalue {
	$$ = $1;
	expressions[nexpressions].var = $3.var;
	expressions[nexpressions].t = $3.t;
	nexpressions++;
}

param_nple : U0 {nparams = 0;}
param_nple : nonempty_param_nple ;
nonempty_param_nple : typename IDENTIFIER {
	nparams = 1;
	strcpy(params[0].name, $2);
	params[0].type = $1;
}
nonempty_param_nple : nonempty_param_nple ',' typename IDENTIFIER {
	strcpy(params[nparams].name, $4);
	params[nparams].type = $3;
	nparams++;
}

declaration : result_nple IDENTIFIER '(' param_nple ')' {
	int i;
	struct function *node;

	int nums[nparams];
	node = functioninfo($2);
	if (node != NULL) {
		yyerror("function redeclared");
	}
	pushfunction($2);
	pushscope();
	printf("define ");
	printresultlltype(nrettypes, rettypes);
	printf(" @%s(", $2);
	for (i = 0; i < nparams; i++) {
		if (i != 0) {
			printf(", ");
		}
		nums[i] = pushsymbol(params[i].name, params[i].type);
		if (isarrayref(params[i].type)) {
			/* passing an array reference */
			printf("ptr %%%s%d", params[i].name, nums[i]);
		} else {
			/* passing a scalar */
			printf("%s %%%s%dvar", params[i].type.lltype,
					params[i].name, nums[i]);
		}
	}
	printf(") {\n");
	for (i = 0; i < nparams; i++) {
		if (isarrayref(params[i].type))
			continue;
		printf("\t%%%s%d = alloca %s\n",
				params[i].name, nums[i], params[i].type.lltype);
		printf("\tstore %s %%%s%dvar, ptr %%%s%d\n", params[i].type.lltype,
				params[i].name, nums[i], params[i].name, nums[i]);
	}
} '{' block '}' {
	if (nrettypes == 0) {
		printf("\tret void\n");
	} else {
		printf("\tret ");
		printresultlltype(nrettypes, rettypes);
		printf(" undef\n");
	}
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

/* from http://www.azillionmonkeys.com/qed/hash.html */
unsigned int
mkhash(const char *key)
{
	int len, rem;
	unsigned int hash, tmp;
	const short int *sixteen;

	sixteen = (const short int *)key;
	len = strlen(key);
	hash = len;
	if (len <= 0 || key == NULL)
		return 0;
	rem = len & 3;
	len >>= 2;
	while (len > 0) {
		hash += sixteen[0];
		tmp = (sixteen[1] << 11) ^ hash;
		hash = (hash << 16) ^ tmp;
		sixteen = &sixteen[2];
		hash += hash >> 11;
		len--;
	}
	switch (rem) {
	case 3:
		hash += sixteen[0];
		hash ^= hash << 16;
		hash ^= key[len - 1] << 18;
		hash += hash >> 11;
		break;
	case 2:
		hash += sixteen[0];
		hash ^= hash << 11;
		hash ^= hash >> 17;
		break;
	case 1:
		hash += key[len - 1];
		hash ^= hash << 10;
		hash += hash >> 1;
		break;
	}
	hash ^= hash << 3;
	hash += hash >> 5;
	hash ^= hash << 4;
	hash += hash >> 17;
	hash ^= hash << 25;
	hash += hash >> 6;
	return hash;
}

void
pushscope(void)
{
	symbols[nsymbols++].id[0] = '\0';
}

void
popscope(void)
{
	while (symbols[nsymbols - 1].id[0] != '\0')
		nsymbols--;
	nsymbols--;
}

int
pushsymbol(char id[MAX_IDENTIFIER_SIZE], struct type t)
{
	int idx;

	idx = nsymbols++;
	strcpy(symbols[idx].id, id);
	symbols[idx].t = t;
	return symbols[idx].n = varctr++;
}

struct symbol *
symbolinfo(char id[MAX_IDENTIFIER_SIZE])
{
	int idx;

	for (idx = nsymbols - 1; idx >= 0 && strcmp(symbols[idx].id, id) != 0;
			idx--);
	return idx < 0 ? NULL : &symbols[idx];
}

int
lookupfunction(const char *name)
{
	int idx;
	unsigned int hash;

	hash = mkhash(name);
	idx = hash % MAX_FUNCTION_COUNT;
	while (functiontable[idx].name[0] != '\0' &&
			strcmp(functiontable[idx].name, name) != 0) {
		idx = (idx + 1) % MAX_FUNCTION_COUNT;
	}
	return idx;
}

void
pushfunction(char name[MAX_IDENTIFIER_SIZE])
{
	int idx;

	idx = lookupfunction(name);
	strcpy(functiontable[idx].name, name);
	functiontable[idx].nresults = nrettypes;
	memcpy(functiontable[idx].results, rettypes,
			sizeof(struct type) * nrettypes);
	functiontable[idx].nparams = nparams;
	memcpy(functiontable[idx].params, params,
			sizeof(struct param) * nparams);
}

struct function *
functioninfo(char name[MAX_IDENTIFIER_SIZE])
{
	int idx;

	idx = lookupfunction(name);
	return functiontable[idx].name[0] == '\0' ? NULL : &functiontable[idx];
}

int
aretypesequal(struct type t1, struct type t2)
{
	int i;

	if (t1.tag != t2.tag)
		return 0;
	for (i = 0; i < MAX_ARRAY_DIMS; i++) {
		if (t1.dimension[i] != t2.dimension[i]) {
			return 0;
		}
	}
	return 1;
}

int
isarrayref(struct type t)
{
	return t.dimension[0] > 0;
}

int
isunsigned(struct type t)
{
	return !isarrayref(t) && (t.tag == U32T || t.tag == U64T);
}

int
isfloat(struct type t)
{
	return !isarrayref(t) && (t.tag == F32T || t.tag == F64T);
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
	labels[nlabels++] = n;
}

int
poplabel(void)
{
	return labels[--nlabels];
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
		if (isarrayref(args[i].t)) {
			printf("ptr %%tmp%d", args[i].var);
		} else {
			printf("%s %%tmp%d", args[i].t.lltype, args[i].var);
		}
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
