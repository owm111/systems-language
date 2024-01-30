Unnamed Systems Language
========================

An unnamed, **work-in-progress** systems programming language, with a
single-pass compiler front-end written with Berkley yacc.

My plan is to expand the language and write some formal semantics.

Requirements
------------

- Berkley yacc
- POSIX (?) lex
- GNU (?) make
- C99 compiler
- POSIX 2008-09 libc
- clang (or other LLVM backend)

`nix develop` can be used to obtain a development environment with all
of these tools.

Building
--------

	make
