CFLAGS = -std=c99 -g -Og -Wall -Wextra
CPPFLAGS = -D_POSIX_C_SOURCE=200809L -DYYDEBUG=1
LFLAGS =
YFLAGS = -d -v

test-programs = test-program sort-test

all: compiler $(test-programs)

clean:
	$(RM) compiler *.o y.* compiler.c lexer.c $(test-programs) *.ll

.PHONY: all clean

compiler: compiler.o lexer.o

%.ll: %.X compiler
	./compiler <$< >$@
%: %.ll
	clang -Wall -g $< -o $@

ignorewarnings = -Wno-missing-braces -Wno-unused-function
compiler.o: CFLAGS += $(ignorewarnings)
lexer.o: CFLAGS += $(ignorewarnings)
