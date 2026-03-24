open Sexplib
open CrTypeIF.CrMem

let load f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str

let rec positive_to_sexp n =
  if n <= 1 then Sexp.Atom "Coq_xH"
  else if n mod 2 = 0 then Sexp.List [Sexp.Atom "Coq_xO"; positive_to_sexp (n / 2)]
  else Sexp.List [Sexp.Atom "Coq_xI"; positive_to_sexp (n / 2)]

let rec expand_integers sexp =
  match sexp with
  | Sexp.Atom s -> Sexp.Atom s
  | Sexp.List [Sexp.Atom "Zpos"; Sexp.Atom n] ->
      (try Sexp.List [Sexp.Atom "Zpos"; positive_to_sexp (int_of_string n)]
       with Failure _ -> sexp)
  | Sexp.List [Sexp.Atom "Zneg"; Sexp.Atom n] ->
      (try Sexp.List [Sexp.Atom "Zneg"; positive_to_sexp (int_of_string n)]
       with Failure _ -> sexp)
  | Sexp.List ((Sexp.Atom hd) :: tl) ->
      (* If it's IOArg, TmpArg, IO_CTX_PTR, or any tuple expecting a positive id, intercept it *)
      if Stdlib.List.mem hd ["IOArg"; "TmpArg"; "Coq_pair"; "Coq_cons"] && Stdlib.List.length tl > 0 then
        match Stdlib.List.hd tl with
        | Sexp.Atom n_str ->
            (try 
              let n = int_of_string n_str in
              Sexp.List ([Sexp.Atom hd; positive_to_sexp n] @ (Stdlib.List.map expand_integers (Stdlib.List.tl tl)))
             with Failure _ -> Sexp.List (Stdlib.List.map expand_integers ((Sexp.Atom hd) :: tl)))
        | _ -> Sexp.List (Stdlib.List.map expand_integers ((Sexp.Atom hd) :: tl))
      else
        Sexp.List (Stdlib.List.map expand_integers ((Sexp.Atom hd) :: tl))
  | Sexp.List l ->
      Sexp.List (Stdlib.List.map expand_integers l)

let () =
  if Array.length Sys.argv <> 3 then (
    prerr_endline "usage: dune exec mem_eq <file_a> <file_b>";
    exit 1
  );

  let file_1 = Sys.argv.(1) in
  let f1_str = load file_1 in
  let file_2 = Sys.argv.(2) in
  let f2_str = load file_2 in

  let sexp1 = expand_integers (Sexp.of_string f1_str) in
  let sexp2 = expand_integers (Sexp.of_string f2_str) in

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
