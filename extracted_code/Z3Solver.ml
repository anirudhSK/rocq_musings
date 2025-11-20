open Char
open Z3

(* LLM's recommended type format for uniquely tracking variables *)
module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx vars)
  | SmtExpr.SmtBoolEq (a1, a2) -> Z3.Boolean.mk_eq ctx (z3_expr_from_coq_smt_arith_expr a1 ctx vars) (z3_expr_from_coq_smt_arith_expr a2 ctx vars)
and z3_expr_from_coq_smt_arith_expr (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtConst n -> Z3.BitVector.mk_numeral ctx (string_of_int (Interface.coq_Z_to_int n)) 8
  | SmtExpr.SmtArithVar name -> (
    let name_str = Interface.coq_str_to_str name in
    match StringMap.find_opt name_str !vars with
    | Some z3_var -> z3_var
    | None ->
        let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 8 in
        vars := StringMap.add name_str z3_var !vars;
        z3_var)
  | SmtExpr.SmtConditional (cond, e1, e2) ->
      Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr cond ctx vars) (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitAdd (e1, e2) -> Z3.BitVector.mk_add ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitSub (e1, e2) -> Z3.BitVector.mk_sub ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitAnd (e1, e2) -> Z3.BitVector.mk_and ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitOr (e1, e2)  -> Z3.BitVector.mk_or ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitXor (e1, e2) -> Z3.BitVector.mk_xor ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitNot e        -> Z3.BitVector.mk_not ctx (z3_expr_from_coq_smt_arith_expr e ctx vars)
  | SmtExpr.SmtBitMul (e1, e2) -> Z3.BitVector.mk_mul ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitDiv (e1, e2) -> Z3.BitVector.mk_udiv ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtBitMod (e1, e2) -> Z3.BitVector.mk_smod ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)

(* Gets all variable assignments and folds them into a valuation (linked list) *)
let to_vmap (m : Z3.Model.model) (acc : Interface.coq_ValueMap) (name : string) (z3_var : Z3.Expr.expr) : Interface.coq_ValueMap =
  match Z3.Model.eval m z3_var true with
  | Some v ->
    if Z3.Expr.is_numeral v then
      let var_str = Z3.BitVector.numeral_to_string v in
      let var_val = int_of_string var_str in
      Printf.printf "| \027[1m%s\027[0m = %d\n" name var_val;
      Interface.VMap (
        Interface.str_to_coq_str name,
        Interface.int_to_coq_uint8 var_val,
        acc)
    else
      raise (Failure ("Expects uint8 but got non-numeral value for " ^ name))
  | None -> raise (Failure ("Z3 failed to return valuation for " ^ name))

let sat_check solver tracked_vars =
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown
  | Z3.Solver.SATISFIABLE -> (
    let model = Solver.get_model solver in
    match model with
    | Some m -> (
      Printf.printf "┌ SAT Valuation\n";
      let var_bindings = StringMap.bindings !tracked_vars in
      let valuations = Stdlib.List.fold_left
        (fun acc (name, z3_var) -> to_vmap m acc name z3_var)
        Interface.VMap_DNE
        var_bindings in
      Printf.printf "└\n";
      SmtTypes.SmtSat (Interface.coq_TraverseMap valuations))
    | None -> raise (Failure "Z3 returned SAT, but no valuation."))

let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  let z3_expr = z3_expr_from_coq_smt_bool_expr expr ctx tracked_vars in
  Solver.add solver [z3_expr];

  sat_check solver tracked_vars
