(* Various helper lemmas showing ctrl plane maps don't change *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrSymbolicSemanticsTransformer.
Require Import Coq.Lists.List.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_smt:
  forall ho c1,
  ctrl_plane_map (eval_hdr_op_assign_smt ho c1) =
  ctrl_plane_map c1.
Proof.
  intros ho c1.
  destruct ho; simpl; try reflexivity.
Qed.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_list_smt:
  forall hol c1,
  ctrl_plane_map (eval_hdr_op_list_smt hol c1) =
  ctrl_plane_map c1.
Proof.
  intros.
  induction hol.
  - reflexivity.
  - simpl. rewrite <- IHhol.
    apply ctrl_plane_invariant_hdr_op_smt.
Qed.


Lemma ctrl_plane_invariant_seq_rule_smt:
  forall s c,
    ctrl_plane_map (eval_seq_rule_smt s c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_seq_rule_smt.
  destruct s.
  destruct (eval_match_smt match_pattern c);
  rewrite ctrl_plane_invariant_update_states;
  rewrite ctrl_plane_invariant_update_hdrs;
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule_smt:
  forall p c,
    ctrl_plane_map (eval_par_rule_smt p c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_par_rule_smt.
  destruct p.
  destruct (eval_match_smt match_pattern c);
  rewrite ctrl_plane_invariant_update_states;
  rewrite ctrl_plane_invariant_update_hdrs;
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_ma_rule_smt:
  forall m c,
    ctrl_plane_map (eval_match_action_rule_smt m c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_match_action_rule_smt.
  destruct m.
  - apply ctrl_plane_invariant_seq_rule_smt.
  - apply ctrl_plane_invariant_par_rule_smt.
Qed.

Lemma ctrl_plane_invariant_transformer_intermediate_smt:
  forall a t c,
    ctrl_plane_map (eval_transformer_smt (a :: t) c) =
    ctrl_plane_map (eval_transformer_smt t c).
Proof.
  intros.
  unfold eval_transformer_smt.
  remember (a :: t) as full_list.
  repeat rewrite ctrl_plane_invariant_update_states.
  repeat rewrite ctrl_plane_invariant_update_hdrs.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer_smt:
  forall c t,
    ctrl_plane_map (eval_transformer_smt t c) = ctrl_plane_map c.
Proof.
  intros.
  induction t.
  - reflexivity.
  - rewrite <- IHt. apply ctrl_plane_invariant_transformer_intermediate_smt.
Qed.