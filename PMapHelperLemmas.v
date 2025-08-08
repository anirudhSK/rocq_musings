From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import Maps.

Transparent lookup_ctrl.
Lemma commute_lookup_eval_ctrl:
  forall c f s,
  lookup_ctrl (eval_sym_state s f) c =
  eval_smt_arith (lookup_ctrl s c) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.

(* Same as the above lemma for hdr and state *)
Transparent lookup_hdr.
Transparent lookup_hdr_map.
Lemma commute_lookup_eval_hdr:
  forall h f s,
  lookup_hdr (eval_sym_state s f) h =
  eval_smt_arith (lookup_hdr s h) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.

Transparent lookup_state.
Transparent lookup_state_map.
Lemma commute_lookup_eval_state:
  forall sv f s,
  lookup_state (eval_sym_state s f) sv =
  eval_smt_arith (lookup_state s sv) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.

Global Opaque lookup_hdr.
Global Opaque lookup_state.
Global Opaque lookup_hdr_map.
Global Opaque lookup_state_map.
Global Opaque lookup_ctrl.