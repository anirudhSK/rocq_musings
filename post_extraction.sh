# Compile the extracted code
ocamlc -c imp1.mli
ocamlc -c imp1.ml

# Compile your implementation (this might need to reference imp1)
ocamlc -c -I . smt_solver.ml

# Link them together
ocamlc -o my_program smt_solver.cmo imp1.cmo
