open Sexplib

let equivalence_check_programs str1 str2 =
  let sexp_1 = Sexp.of_string str1 in
  let sexp_2 = Sexp.of_string str2 in
  let prog_1 = Interface.coq_CaracaraProgram_of_sexp sexp_1 in
  let prog_2 = Interface.coq_CaracaraProgram_of_sexp sexp_2 in
  let res = SmtQuery.equivalence_checker_cr_dsl prog_1 prog_2 in
  (* Sean TODO: Need to fix this to match new version of equivalence_checker_cr_dsl *)
  match res with
  | Coq_true -> print_endline "Equivalent"
  | Coq_false -> print_endline "Not Equivalent"
  
let load f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str

let () =
  if Array.length Sys.argv != 3 then (
    prerr_endline "usage: ./bin <path/to/s/expr/1> <path/to/s/expr/2>";
    exit 1
  );

  let file_1 = Sys.argv.(1) in
  let f1_str = load file_1 in
  let file_2 = Sys.argv.(2) in
  let f2_str = load file_2 in
  equivalence_check_programs f1_str f2_str
