open SmtExpr
open Z3

(* Process an SmtBoolExpr from SmtExpr to generate a query for Z3 using the OCaml Z3 API *)
let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let int_sort = Arithmetic.Integer.mk_sort ctx in
  let x = Expr.mk_const_s ctx "x" int_sort in
  let solver = Solver.mk_solver ctx None in
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> Z3.Solver.UNSATISFIABLE
  | Z3.Solver.SATISFIABLE -> Z3.Solver.SATISFIABLE
  | Z3.Solver.UNKNOWN -> Z3.Solver.UNKNOWN

(* Main function to call the function solve above *)
let () =
  let expr = SmtExpr.SmtTrue in
  match solve expr with
  | Z3.Solver.UNSATISFIABLE -> print_endline "UNSATISFIABLE"
  | Z3.Solver.SATISFIABLE -> print_endline "SATISFIABLE"
  | Z3.Solver.UNKNOWN -> print_endline "UNKNOWN"