CFLAGS = -std=c99 -g -Og -Wall -Wextra
CPPFLAGS = -D_POSIX_C_SOURCE=200809L -DYYDEBUG=1
LFLAGS =
YFLAGS = -d -v

all: compiler

clean:
	$(RM) compiler *.o y.* compiler.c lexer.c

.PHONY: all clean

compiler: compiler.o lexer.o

test-program.ll: test-program.X compiler
	./compiler <$< >$@
test-program: test-program.ll
	clang $< -o $@

ignorewarnings = -Wno-missing-braces -Wno-unused-function
compiler.o: CFLAGS += $(ignorewarnings)
lexer.o: CFLAGS += $(ignorewarnings)
