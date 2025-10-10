open Z3
open Z3Solver

let ctx = mk_context []
let example_1 () =
  let x = Arithmetic.Integer.mk_const ctx (Z3.Symbol.mk_string ctx "x") in
  let y = Arithmetic.Integer.mk_const ctx (Z3.Symbol.mk_string ctx "y") in
  let zero = Arithmetic.Integer.mk_numeral_i ctx 0 in (* zero *)
  let eleven = Arithmetic.Integer.mk_numeral_i ctx 11 in (* eleven *)
  let x_gt_0 = Arithmetic.mk_gt ctx x zero in (* x > 0 *)
  let y_gt_0 = Arithmetic.mk_gt ctx y zero in (* y > 0 *)
  let sum = Arithmetic.mk_add ctx [x; y] in   (* sum = x + y *)
  let x_plus_y_eq_11 = Boolean.mk_eq ctx sum eleven in (* sum = 11 *)
  (* Create solver and add constraints *)
  let solver = Solver.mk_solver ctx None in
  Solver.add solver [x_gt_0; y_gt_0; x_plus_y_eq_11];
  (* Print the constraints *)
  Printf.printf "Constraints:\n";
  Printf.printf "x > 0: %s\n" (Expr.to_string x_gt_0);
  Printf.printf "y > 0: %s\n" (Expr.to_string y_gt_0);
  Printf.printf "x + y = 11: %s\n" (Expr.to_string x_plus_y_eq_11);
  match sat_check solver with
  | SmtTypes.SmtSat f -> Printf.printf
      "SAT\nx = %d\ny = %d\n"
      (str_to_coq_str "x" |> f |> coq_Z_to_int)
      (str_to_coq_str "y" |> f |> coq_Z_to_int)
  | SmtTypes.SmtUnsat -> Printf.printf "UNSAT\n"
  | SmtTypes.SmtUnknown -> Printf.printf "UNKNOWN\n"

let () =
  let _ = example_1 () in ()
