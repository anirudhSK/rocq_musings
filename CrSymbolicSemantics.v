From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Convert FunctionArgument to SmtExpr *)
Definition function_argument_to_smt (arg : FunctionArgument) : SmtExpr :=
    match arg with
    | HeaderArg (HeaderCtr h) => SmtVar ("hdr_" ++ h)
    | CtrlPlaneArg (CtrlPlaneConfigNameCtr c) => SmtVar ("ctrl_" ++ c)
    | ConstantArg n => SmtConst n
    | StatefulArg (StateVarCtr s) => SmtVar ("state_" ++ s)
    end.

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) : SmtExpr :=
    match h with
    | StatefulOp f arg1 arg2 _ =>
       match f with 
         | AddOp => SmtBitAdd (function_argument_to_smt arg1) (function_argument_to_smt arg2)
       end
    | StatelessOp f arg1 arg2 _ =>
       match f with
         | AddOp => SmtBitAdd (function_argument_to_smt arg1) (function_argument_to_smt arg2)
       end
    end.

Definition eval_hdr_op_smt (h : HdrOp) : SmtExpr :=
    match h with
    | StatefulOp f arg1 arg2 target => SmtBitEq (function_argument_to_smt (StatefulArg target)) (eval_hdr_op_expr_smt h)
    | StatelessOp f arg1 arg2 target => SmtBitEq (function_argument_to_smt (HeaderArg target)) (eval_hdr_op_expr_smt h)
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