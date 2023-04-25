test: expr.ml sexp.ml test.ml
	ocamlfind ocamlc -o test -package extlib,oUnit,str -linkpkg -g expr.ml sexp.ml test.ml

test2: expr.ml sexp.ml test.ml
	ocamlfind ocamlc -o test -package extlib,oUnit,str -linkpkg -g expr.ml sexp2.ml test.ml

# failed to get ocamldebug working
debug: sexp.ml
	ocamlfind ocamlc -o sexp -package extlib,oUnit,str -linkpkg -g sexp.ml

clean:
	rm -f test *.log *.cmi *.cmo *.cache
