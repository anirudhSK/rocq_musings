open Sexplib
open CrTypeIF.CrMem

let load f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str

let () =
  if Array.length Sys.argv != 3 then (
    prerr_endline "usage: ./bin <file_a> <file_b>";
    exit 1
  );

  let file_1 = Sys.argv.(1) in
  let f1_str = load file_1 in
  let file_2 = Sys.argv.(2) in
  let f2_str = load file_2 in

  let sexp1 = Sexp.of_string f1_str in
  let sexp2 = Sexp.of_string f2_str in

  let prog1 = coq_IM_Program_of_sexp sexp1 in
  let prog2 = coq_IM_Program_of_sexp sexp2 in

(*
  let eq_query = CrMem.query_expression prog1 prog2 in
  let eqq_s = sexp_of_bool_expr eq_query in
  print_endline(Sexp.to_string_hum eqq_s);
*)
  
  let res = MemSolver.mem_solve prog1 prog2 in
  match res with
  | Z3Sat (_, _, _) -> print_endline("sat")
  | Z3Unsat -> print_endline("unsat")
  | Z3Unknown -> print_endline("unknown")
