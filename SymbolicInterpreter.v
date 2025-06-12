From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Some preprocessing operations before we begin the transformation to SMT.
   For now, leave these as function signatures. 
   The idea is that if these return true, then we worry about correctness of the transformation to SMT,
   else, we just error out right here. *)
Parameter check_uninitilized : Transformer -> bool.
Parameter check_unique : Transformer -> bool.

(* Convert FunctionArgument to SmtExpr *)
Definition fn_arg_to_smt_expr (arg : FunctionArgument) : SmtExpr :=
    match arg with
    | HeaderArg (HeaderCtr h) => SmtVar ("hdr_" ++ h)
    | CtrlPlaneArg (CtrlPlaneConfigNameCtr c) => SmtVar ("ctrl_" ++ c)
    | ConstantArg n => SmtConst n
    | StatefulArg (StateVarCtr s) => SmtVar ("state_" ++ s)
    end.

(* Define the symbolic interpreter for header operations *)
Definition symbolic_interpreter (h : HdrOp) : SmtExpr :=
    match h with
    | StatefulOp f arg1 arg2 target =>
       match f with 
         | AddOp => SmtBitAdd (fn_arg_to_smt_expr arg1) (fn_arg_to_smt_expr arg2)
       end
    | StatelessOp f arg1 arg2 target =>
       match f with
         | AddOp => SmtBitAdd (fn_arg_to_smt_expr arg1) (fn_arg_to_smt_expr arg2)
       end
    end.

(* Convert CR Valuation to SMT Valuation *)
Definition cr_val_to_smt_val (v: Valuation) : SmtValuation :=
    (* This returns a lambda function from string to uint8 *)
    fun x =>
      if string_prefix "hdr_" x then
        header_map v (HeaderCtr (string_drop 4 x))
      else if string_prefix "ctrl_" x then
        ctrl_plane_map v (CtrlPlaneConfigNameCtr (string_drop 5 x))
      else if string_prefix "state_" x then
        state_var_map v (StateVarCtr (string_drop 6 x))
      else zero. (* Default value if not found *)
      (* TODO: Need to figure out what to do here, this is weird.
         Why does this even work?
         I guess because cr_val_to_sml is only ever applied to the smt_transformed formula,
        not arbitrary ones? *)

(* Lemma relating evaluation of CR program and
                  evaluation of SMT expression
                  produced by symbolic_interpreter *)
Lemma cr_eval_to_smt_eval :
  forall (hop : HdrOp) (v : Valuation), eval_hdr_op_expr hop v = eval_smt_expr (symbolic_interpreter hop) (cr_val_to_smt_val v).
Proof.
  destruct hop, f, arg1, arg2; (* destruct on header op, binary function, and 2 arguments *)
  simpl;
  try destruct h; (* if the two arguments are headers, destruct on these *)
  try destruct h0;
  try destruct c; (* similar with ctrl plane args *)
  try destruct c0;
  try destruct s; (* and state variables *)
  try destruct s0;
  simpl;
  reflexivity.
Qed.