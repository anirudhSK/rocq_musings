From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrSemantics.
From MyProject Require Import SmtExpr.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Convert FunctionArgument to SmtArithExpr *)
Definition lookup_smt (arg : FunctionArgument) (ps : ProgramState SmtArithExpr) : SmtArithExpr :=
  match arg with
  | CtrlPlaneArg c => ctrl_plane_map SmtArithExpr ps c
  | HeaderArg h    => header_map SmtArithExpr ps h
  | ConstantArg n  => SmtConst n
  | StatefulArg s  => state_var_map SmtArithExpr ps s
  end.

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) (ps : ProgramState SmtArithExpr) : SmtArithExpr :=
    match h with
    | StatefulOp f arg1 arg2 _ =>
       match f with 
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | SubOp => SmtBitSub (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | AndOp => SmtBitAnd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | OrOp => SmtBitOr (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | XorOp => SmtBitXor (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | MulOp => SmtBitMul (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | DivOp => SmtBitDiv (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | ModOp => SmtBitMod (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    | StatelessOp f arg1 arg2 _ =>
       match f with
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | SubOp => SmtBitSub (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | AndOp => SmtBitAnd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | OrOp => SmtBitOr (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | XorOp => SmtBitXor (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | MulOp => SmtBitMul (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | DivOp => SmtBitDiv (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | ModOp => SmtBitMod (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    end.

Definition eval_hdr_op_assign_smt (ho : HdrOp) (ps: ProgramState SmtArithExpr) : ProgramState SmtArithExpr :=
    match ho with
    | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_state ps target op_output
    | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_smt ho ps in update_hdr ps target op_output
    end.  

Instance Semantics_SmtArithExpr : Semantics SmtArithExpr := {
  (* Function to lookup arg in program state *)
  lookup_function_argument := lookup_smt;

  (* Function to evaluate header operation expression *)
  eval_hdr_op_expr := eval_hdr_op_expr_smt;

  (* Function to update header or state variable in program state *)
  eval_hdr_op_assign := eval_hdr_op_assign_smt;
}.