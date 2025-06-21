From MyProject Require Import SmtExpr.
Require Import Classical.

(* An SmtQuery takes an SmtBoolExpr and returns:
   None: meaning it is false for all possible valuations (or)
   Some(SmtValuation): a valuation for which it is true *)
Parameter smt_query : SmtBoolExpr -> option (SmtValuation).

(* Axiom that smt_query is sound. *)
Axiom smt_query_sound : forall e,
  smt_query e <> None ->
  exists v, eval_smt_bool e v = true.

(* Axiom that smt_query is complete. *)
Axiom smt_query_complete : forall e,
  smt_query e = None ->
  forall v', eval_smt_bool e v' = false.