From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Convert FunctionArgument to SmtExpr *)
Definition lookup_smt (arg : FunctionArgument) (ps : ProgramState SmtExpr) : SmtExpr :=
  match arg with
  | CtrlPlaneArg c => ctrl_plane_map SmtExpr ps c
  | HeaderArg h    => header_map SmtExpr ps h
  | ConstantArg n  => SmtConst n
  | StatefulArg s  => state_var_map SmtExpr ps s
  end.

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) (ps : ProgramState SmtExpr) : SmtExpr :=
    match h with
    | StatefulOp f arg1 arg2 _ =>
       match f with 
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    | StatelessOp f arg1 arg2 _ =>
       match f with
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    end.

Definition eval_hdr_op_smt_assign (ho : HdrOp) (ps: ProgramState SmtExpr) : ProgramState SmtExpr :=
    match ho with
    | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_state ps target op_output
    | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_smt ho ps in update_hdr ps target op_output
    end.  

(* Convert ProgramState to SMT Valuation *)
Definition prog_state_to_smt_val (ps: ProgramState uint8) : SmtValuation :=
    (* This returns a lambda function from string to uint8 *)
    fun x =>
      if string_prefix "hdr_" x then
        header_map uint8 ps (HeaderCtr (string_drop 4 x))
      else if string_prefix "ctrl_" x then
        ctrl_plane_map uint8 ps (CtrlPlaneConfigNameCtr (string_drop 5 x))
      else if string_prefix "state_" x then
        state_var_map uint8 ps (StateVarCtr (string_drop 6 x))
      else zero. (* Default value if not found *)
      (* TODO: Need to figure out what to do here, this is weird.
         Why does this even work?
         I guess because cr_val_to_sml is only ever applied to the smt_transformed formula,
        not arbitrary ones? *)

Instance Semantics_SmtExpr : Semantics SmtExpr := {
  (* Function to lookup arg in program state *)
  lookup_function_argument := lookup_smt;

  (* Function to evaluate header operation expression *)
  eval_hdr_op_expr := eval_hdr_op_expr_smt;

  (* Function to update header or state variable in program state *)
  eval_hdr_op_assign := eval_hdr_op_smt_assign;
}.