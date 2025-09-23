(* main.ml *)

open Sexplib.Std
open Combine (* <-- This is the only line that changes! *)

let () =
  (* Now 'sexp_of_caracaraProgram' and 'example_program_1' are found *)
  let sexp_output : Sexp.t = sexp_of_caracaraProgram example_program_1 in

  (* Convert the Sexp.t value to a human-readable string *)
  let string_output : string = Sexp.to_string_hum sexp_output in

  (* Print the result *)
  print_endline string_output