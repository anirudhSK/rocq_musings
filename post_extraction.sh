ocamlfind ocamlc -thread -package z3 -linkpkg -c Z3Example.ml
ocamlc -c EquivalenceChecker.mli
ocamlc -c EquivalenceChecker.ml
ocamlfind ocamlc -thread -package z3 -linkpkg Z3Example.cmo EquivalenceChecker.cmo -o eqchecker
