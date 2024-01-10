%{
#include <stdlib.h>
#include <string.h>

#include "header.h"
#include "y.tab.h"
%}

%option noyywrap

%%

\n ++yylineno;
[ \t\n] ;
^#.*$ ;

[(){},;=<>*/%+-] return yytext[0];
"==" return EQUALEQUAL;
"!=" return BANGEQUAL;
"<=" return LESSEQUAL;
">=" return GREATEREQUAL;

"u0" return U0;
"u1" return U1;
"i32" return I32;
"i64" return I64;
"u32" return U32;
"u64" return U64;
"f32" return F32;
"f64" return F64;

"cast" return CAST;
"if" return IF;
"else" return ELSE;
"return" return RETURN;
"while" return WHILE;

[a-zA-Z_][a-zA-Z0-9_]* {
	int bytes;

	bytes = snprintf(yylval.identifier, MAX_IDENTIFIER_SIZE, "%s", yytext);
	if (bytes >= MAX_IDENTIFIER_SIZE) {
		yyerror("identifier too long");
	}
	return IDENTIFIER;
}

[0-9][0-9]* {
	yylval.constant = strtol(yytext, NULL, 10);
	return CONSTANT;
}

. {
	yyerror("Unrecognized input\n");
}
