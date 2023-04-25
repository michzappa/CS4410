SNAKE_EXT=garter
UNAME := $(shell uname)
ifeq ($(UNAME), Linux)
  NASM_FORMAT=elf64
  OS_FLAGS=
else
ifeq ($(UNAME), Darwin)
  NASM_FORMAT=macho64
  OS_FLAGS=
endif
endif

NASM_FLAGS=-f $(NASM_FORMAT) -Wall
CLANG_FLAGS=$(OS_FLAGS) \
	-mstackrealign -m64 -g \
	-fstack-protector-all -fno-omit-frame-pointer \
	-Wstack-protector -Wall -Wextra -Wpedantic -Wconversion \
	-Wshadow -Wno-language-extension-token

PKGS=ounit2,extlib,unix,str
BUILD=ocamlbuild -r -use-ocamlfind -cflag -annot -ocamlyacc 'ocamlyacc -v'

CSRCS=$(addprefix runtime/,main.c gc.c snakeval.c)
CHDRS=$(addprefix runtime/,snakeval.h decl.h)
CC=clang

main: *.ml parser.mly lexer.mll
	$(BUILD) -package $(PKGS) main.native
	mv main.native main

test: *.ml parser.mly lexer.mll main
	$(BUILD) -package $(PKGS) test.native
	mv test.native test

lsp-build: *.ml parser.mly lexer.mll main
	dune build

output/%.run: output/%.o $(CSRCS) $(CHDRS)
	$(CC) $(CLANG_FLAGS) -o $@ $(CSRCS) $<

output/%.o: output/%.s
	nasm $(NASM_FLAGS) -o $@ $<

.PRECIOUS: output/%.s
output/%.s: input/%.$(SNAKE_EXT) main
	./main $< > $@

output/do_pass/%.run: output/do_pass/%.o $(CSRCS) $(CHDRS)
	$(CC) $(CLANG_FLAGS) -o $@ $(CSRCS) $<

output/do_pass/%.o: output/do_pass/%.s
	nasm $(NASM_FLAGS) -o $@ $<

.PRECIOUS: output/do_pass/%.s
output/do_pass/%.s: input/do_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_pass/%.run: output/dont_pass/%.o $(CSRCS) $(CHDRS)
	$(CC) $(CLANG_FLAGS) -o $@ $(CSRCS) $<

output/dont_pass/%.o: output/dont_pass/%.s
	nasm $(NASM_FLAGS) -o $@ $<

.PRECIOUS: output/dont_pass/%.s
output/dont_pass/%.s: input/dont_pass/%.$(SNAKE_EXT) main
	./main $< > $@


output/do_err/%.run: output/do_err/%.o $(CSRCS) $(CHDRS)
	$(CC) $(CLANG_FLAGS) -o $@ $(CSRCS) $<

output/do_err/%.o: output/do_err/%.s
	nasm $(NASM_FLAGS) -o $@ $<

.PRECIOUS: output/do_err/%.s
output/do_err/%.s: input/do_err/%.$(SNAKE_EXT) main
	./main $< > $@


output/dont_err/%.run: output/dont_err/%.o $(CSRCS) $(CHDRS)
	clang $(CLANG_FLAGS) -o $@ $(CSRCS) $<

output/dont_err/%.o: output/dont_err/%.s
	nasm $(NASM_FLAGS) -o $@ $<

.PRECIOUS: output/dont_err/%.s
output/dont_err/%.s: input/dont_err/%.$(SNAKE_EXT) main
	./main $< > $@

# Hello grader person probably. If for some reason you actually needed the
# following target, well too bad, it probably won't work. We deleted gc.h
# since it is not needed. Also all our C code has been moved to the runtime
# folder. Also the gc.c file is not stand alone since it does depend on
# snakeval.c. Good luck :)
gctest.o: gctest.c gc.h
	gcc gctest.c -m64 -c -g -o gctest.o

# gc.o: gc.c gc.h
# 	gcc gc.c -m64 -c -g -o gc.o

# cutest-1.5/CuTest.o: cutest-1.5/CuTest.c cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/CuTest.c -c -g -o cutest-1.5/CuTest.o

# gctest: gctest.o gc.c cutest-1.5/CuTest.o cutest-1.5/CuTest.h
# 	gcc -m32 cutest-1.5/AllTests.c cutest-1.5/CuTest.o gctest.o gc.c -o gctest


clean:
	rm -rf output/*.o output/*.s output/*.dSYM output/*.run *.log *.o
	rm -rf output/*/*.o output/*/*.s output/*/*.dSYM output/*/*.run
	rm -rf _build/
	rm -f main test vgcore.*
