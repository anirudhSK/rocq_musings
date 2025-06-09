From MyProject Require Import CrTransformer.
From MyProject Require Import SmtExpr.
Require Import ZArith.

(* Define the symbolic interpreter for header operations *)
Definition symbolic_interpreter (h : HdrOp) : SmtExpr :=
    match h with
    | StatefulOp f arg1 arg2 target =>
       match f with 
         | AddOp => SmtConst zero (*TODO: placeholder *)
       end
    | StatelessOp f arg1 arg2 target =>
       match f with
         | AddOp => SmtConst zero (*TODO: placeholder *)
       end
    end.

(* TODO: Need to handle arg1 and arg2 being various symbolic types: HeaderArg, CtrlPlaneArg,
   and we need to introduce unique string names for each of these things so that the smt formula does the right thing *)

(* TODO: Need to compile down the AddOp and MulOp down into
   the basic ops (and, or, not) we support in SmtExpr *)