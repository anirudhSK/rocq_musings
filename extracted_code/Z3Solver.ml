open Z3

(* Recursively convert a coq_SmtBoolExpr to a Z3 expression *)
let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx)
  | SmtExpr.SmtBoolEq (a1, a2) -> Z3.Boolean.mk_true ctx (* TODO: must fix *)

  (* Z3.Boolean.mk_eq ctx (z3_expr_from_coq_smt_bool_expr a1 ctx) (z3_expr_from_coq_smt_bool_expr a2 ctx) *)

(* Process an SmtBoolExpr from SmtExpr to generate a query for Z3 using the OCaml Z3 API *)
let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in 
  (match expr with
  | SmtExpr.SmtTrue -> ()
  | SmtExpr.SmtFalse -> ()
  | SmtExpr.SmtBoolAnd (e1, e2) -> () (* Placeholder for stuff *)
  | SmtExpr.SmtBoolOr (e1, e2) -> () (* Placeholder for stuff *)
  | SmtExpr.SmtBoolNot e -> () (* Placeholder for stuff *)
  | SmtExpr.SmtBoolEq (a1, a2) -> () (* Placeholder for stuff *));
  
  (* Check satisfiability of the constraints added to the solver *)
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.SATISFIABLE -> SmtTypes.SmtSat (fun _ -> (Obj.magic 0 : MyInts.uint8))
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown

(* Main function to call the function solve above *)
let () =
  let expr = SmtExpr.SmtTrue in
  match solve expr with
  | SmtTypes.SmtUnsat -> print_endline "UNSATISFIABLE"
  | SmtTypes.SmtSat _ -> print_endline "SATISFIABLE"
  | SmtTypes.SmtUnknown -> print_endline "UNKNOWN"