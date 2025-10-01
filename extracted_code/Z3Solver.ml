open Z3

(* Recursively convert a coq_SmtBoolExpr to a Z3 expression *)
(* TODO: This function is trusted, so needs to be checked via other means like fuzzing *)
let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx)
  | SmtExpr.SmtBoolEq (a1, a2) -> Z3.Boolean.mk_eq ctx (z3_expr_from_coq_smt_arith_expr a1 ctx) (z3_expr_from_coq_smt_arith_expr a2 ctx)
and z3_expr_from_coq_smt_arith_expr (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtConst n -> Z3.Arithmetic.Integer.mk_numeral_i ctx (Obj.magic n : int) (* TODO: Obj.magic is not type safe. *)
  | SmtExpr.SmtArithVar name -> Z3.Arithmetic.Integer.mk_const ctx (Z3.Symbol.mk_string ctx (Obj.magic name : string))
  | SmtExpr.SmtConditional (cond, e1, e2) ->
      Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr cond ctx) (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitAdd (e1, e2) -> Z3.Arithmetic.mk_add ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitSub (e1, e2) -> Z3.Arithmetic.mk_sub ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitAnd (e1, e2) -> Z3.BitVector.mk_and ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitOr (e1, e2)  -> Z3.BitVector.mk_or ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitXor (e1, e2) -> Z3.BitVector.mk_xor ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitNot e        -> Z3.BitVector.mk_not ctx (z3_expr_from_coq_smt_arith_expr e ctx)
  | SmtExpr.SmtBitMul (e1, e2) -> Z3.Arithmetic.mk_mul ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitDiv (e1, e2) -> Z3.Arithmetic.mk_div ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitMod (e1, e2) -> Z3.Arithmetic.Integer.mk_mod ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)

(* Process an SmtBoolExpr from SmtExpr to generate a query for Z3 using the OCaml Z3 API *)
let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in 
  Solver.add solver [z3_expr_from_coq_smt_bool_expr expr ctx];
  
  (* Check satisfiability of the constraints added to the solver *)
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.SATISFIABLE -> SmtTypes.SmtSat (fun _ -> (Obj.magic 0 : MyInts.uint8)) (* TODO: Need to fix the function here *)
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown
