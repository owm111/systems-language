#define MAX_IDENTIFIER_SIZE 64
#define MAX_LLTYPE_SIZE 64
#define MAX_NPLE_SIZE 8
#define MAX_STRLIT_SIZE 512
#define MAX_SYMBOL_COUNT 1024
#define MAX_SCOPE_COUNT 64
#define MAX_FUNCTION_COUNT 1024
#define MAX_LABEL_COUNT 64
#define MAX_EXPRESSION_COUNT 512
#define MAX_ARRAY_DIMS 8

/* the type system */

/*
The "base" types are those enumerated by typetag. They represent a 1-bit
boolean and 32- and 64-bit variants of signed integers, unsigned integers,
and floating-point numbers.

The only non-"base" types are references to arrays (in C terms,
pointers that are guaranteed to point to allocated memory). Currently,
the compiler must know the sizes of array at compile-time and those
sizes must be specified as constants, but a more advanced version
could use expressions and in-scope variables to specify array sizes
and generate compile-time warnings for out-of-bounds errors. Arrays
are represented by the .dimensions member of type: it can be thought
of as a 0-terminated string of dimension sizes (e.g., [0] is a scalar,
[3, 0] is a 1D array with 3 elements, [5, 4, 0] is a 5 by 4 2D matrix).
*/

enum typetag {U1T, I32T, I64T, U32T, U64T, F32T, F64T, LAST_TYPE};

struct type {
	enum typetag tag;
	int dimension[MAX_ARRAY_DIMS];
	char lltype[MAX_LLTYPE_SIZE];
};

struct expressionresult {
	int var;
	struct type t;
};

extern int yyerror(const char *restrict msg);

extern const struct type u1t, i32t, i64t, u32t, u64t, f32t, f64t;
