From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
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

(* Define equivalence checker function *)
Definition hdr_ops_to_smt_query (h1 : HdrOp) (h2 : HdrOp) : SmtExpr :=
  let smt_expr1 := symbolic_interpreter h1 in
  let smt_expr2 := symbolic_interpreter h2 in
  SmtBitEq smt_expr1 smt_expr2.

Definition equivalence_checker (h1 : HdrOp) (h2 : HdrOp) : bool :=
  if (SmtResult_eqb (smt_query_engine (hdr_ops_to_smt_query h1 h2)) (sat)) then true else false.
(* Fill this in. *)