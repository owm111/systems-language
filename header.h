#define MAX_IDENTIFIER_SIZE 64
#define MAX_LLTYPE_SIZE 64
#define MAX_NPLE_SIZE 8
#define MAX_STRLIT_SIZE 512
#define MAX_FUNCTION_COUNT 1024

enum typetag {U1T, I32T, I64T, U32T, U64T, F32T, F64T, LAST_TYPE};

struct type {
	enum typetag tag;
	char lltype[MAX_LLTYPE_SIZE];
};

struct expressionresult {
	int var;
	struct type t;
};

struct typelist {
	struct type t;
	char ident[MAX_IDENTIFIER_SIZE];
	int isarray;
	struct typelist *next;
};

struct expressionlist {
	int var;
	struct type t;
	int isarray;
	struct expressionlist *next;
};

extern int yyerror(const char *restrict msg);

extern const struct type u1t, i32t, i64t, u32t, u64t, f32t, f64t;
