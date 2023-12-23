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
	yylval.identifier = malloc(yyleng + 1);
	memcpy(yylval.identifier, yytext, yyleng);
	yylval.identifier[yyleng] = '\0';
	return IDENTIFIER;
}

[0-9][0-9]* {
	char buf[yyleng + 1];

	memcpy(buf, yytext, yyleng);
	buf[yyleng] = '\0';
	yylval.constant = strtol(buf, NULL, 10);
	return CONSTANT;
}

. {
	yyerror("Unrecognized input\n");
}
