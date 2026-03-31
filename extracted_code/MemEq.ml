let () =
  if Array.length Sys.argv <> 3 then (
    prerr_endline "usage: dune exec mem_eq <file_a> <file_b>";
    exit 1
  );

  let prog1 = MemSolver.load_program Sys.argv.(1) in
  let prog2 = MemSolver.load_program Sys.argv.(2) in

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
