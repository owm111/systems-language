enum type {U1T, I32T, I64T, U32T, U64T, F32T, F64T, LAST_TYPE};

struct expressionresult {
	int var;
	enum type t;
};

extern int yyerror(const char *restrict msg);
