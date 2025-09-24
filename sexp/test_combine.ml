(* This file demonstrates S-expression conversion for types in combine.ml *)
(* Run with: dune build && dune exec ./sexp/test_combine.exe *)

open Combine

let () =
  (* print program at the end of combine.ml *)
  let program_to_test = example_program_1 in

  (* Convert the OCaml value to an S-expression *)
  let sexp_representation = sexp_of_caracaraProgram program_to_test in

  (* Print S-expression *)
  Printf.printf "S-expression for 'example_program_1':\n";
  Sexplib.Sexp.to_string_hum sexp_representation |> print_endline