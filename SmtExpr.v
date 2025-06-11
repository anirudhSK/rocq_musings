(* Write out semantics for bitvectors in SMT,
   show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import CrIdentifiers.
From Coq.Strings Require Import String.

Definition SmtValuation := string -> uint8.

(* Basic starting point of Smt expressions, just have 8 bit ands, ors, and nots.
   Can express everything a sat solver cares about by just setting 7 bits to zero.
   so seems complete in some sense.*)
Inductive SmtExpr :=
    | SmtConst (value : uint8)
    | SmtVar (name : string)
    | SmtBitAdd (e1 e2 : SmtExpr)
    | SmtBitAnd (e1 e2 : SmtExpr)
    | SmtBitOr (e1 e2 : SmtExpr)
    | SmtBitEq (e1 e2 : SmtExpr)
    | SmtBitNot (e : SmtExpr).

(* Provide semantics for the SmtExpr above using the uint8 functions from Integer.v *)
Fixpoint eval_smt_expr (e : SmtExpr) (v : SmtValuation) : uint8 :=
    match e with
    | SmtConst value => value
    | SmtVar name => v name
    (* Note: we assume that the valuation v is well-formed,
       i.e., it contains all the variables that appear in the expression *)
    | SmtBitAdd e1 e2 => add (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitAnd e1 e2 => and (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitOr e1 e2 => or (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitEq e1 e2 => if (eq  (eval_smt_expr e1 v) (eval_smt_expr e2 v)) then one else zero (* Is this one = 1 or 255? Does it matter? *)
    | SmtBitNot e => not (eval_smt_expr e v)
    end.