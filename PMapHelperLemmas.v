From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.

Transparent lookup_ctrl.
Lemma commute_lookup_eval_ctrl:
  forall c f s,
  lookup_ctrl (eval_sym_state s f) c =
  eval_smt_arith (lookup_ctrl s c) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.
Global Opaque lookup_ctrl.