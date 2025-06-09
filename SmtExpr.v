(* Write out semantics for bitvectors in SMT,
   show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import CrIdentifiers.
From Coq.Strings Require Import String.

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

Inductive SmtResult :=
    | sat
    | unsat.

Definition SmtResult_eqb (a b : SmtResult) : bool :=
  match a, b with
  | sat, sat => true
  | unsat, unsat => true
  | _, _ => false
  end.

(* Model for Z3 (or any other SMT solver) *)
Parameter smt_query_engine : SmtExpr -> SmtResult.

(* Provide semantics for the SmtExpr above using the uint8 functions from Integer.v *)
Fixpoint eval_smt_expr (e : SmtExpr) (v : fmap string uint8) : uint8 :=
    match e with
    | SmtConst value => value
    | SmtVar name => match lookup v name with
                     | Some value => value
                     | None => zero (* Default to zero if variable not found *)
                     end
    | SmtBitAdd e1 e2 => add (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitAnd e1 e2 => and (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitOr e1 e2 => or (eval_smt_expr e1 v) (eval_smt_expr e2 v)
    | SmtBitEq e1 e2 => if (eq  (eval_smt_expr e1 v) (eval_smt_expr e2 v)) then one else zero (* Is this one = 1 or 255? Does it matter? *)
    | SmtBitNot e => not (eval_smt_expr e v)
    end.

(* Start with these two axioms and add more if needed. *)
Axiom sound_smt_engine : forall e,
    smt_query_engine e = sat -> exists v, eval_smt_expr e v <> zero.

Axiom complete_smt_engine : forall e,
    (exists v, eval_smt_expr e v <> zero) -> smt_query_engine e = sat.