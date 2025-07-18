(* Various helper lemmas showing ctrl plane maps don't change *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrSymbolicSemanticsTransformer.
Require Import Coq.Lists.List.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op:
  forall (ho: HdrOp)
         (c1: ProgramState uint8),
  ctrl_plane_map (eval_hdr_op_assign_uint8 ho c1) =
  ctrl_plane_map c1.
Proof.
  intros ho c1.
  destruct ho; simpl; try reflexivity.
Qed.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_list:
  forall hol c1,
  ctrl_plane_map (eval_hdr_op_list_uint8 hol c1) =
  ctrl_plane_map c1.
Proof.
  intros.
  induction hol.
  - reflexivity.
  - simpl. rewrite <- IHhol.
    apply ctrl_plane_invariant_hdr_op.
Qed.


Lemma ctrl_plane_invariant_seq_rule:
  forall s c,
    ctrl_plane_map (eval_seq_rule_uint8 s c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_seq_rule_uint8.
  destruct s.
  destruct (eval_match_uint8 match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule:
  forall p c,
    ctrl_plane_map (eval_par_rule_uint8 p c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_par_rule_uint8.
  destruct p.
  destruct (eval_match_uint8 match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_ma_rule:
  forall m c,
    ctrl_plane_map (eval_match_action_rule_uint8 m c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_match_action_rule_uint8.
  destruct m.
  - apply ctrl_plane_invariant_seq_rule.
  - apply ctrl_plane_invariant_par_rule.
Qed.

Lemma ctrl_plane_invariant_transformer_intermediate:
  forall a t c,
    ctrl_plane_map (eval_transformer_uint8 (a :: t) c) =
    ctrl_plane_map (eval_transformer_uint8 t c).
Proof.
  intros.
  unfold eval_transformer_uint8.
  remember (a :: t) as full_list.
  remember (find_first_match (combine (get_match_results full_list c) full_list)) as outer_match.
  remember (find_first_match (combine (get_match_results t c) t)) as inner_match.
  destruct (outer_match) eqn:des; destruct inner_match eqn:des2; try rewrite ctrl_plane_invariant_ma_rule; try reflexivity.
  rewrite ctrl_plane_invariant_ma_rule. reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer:
  forall c t,
    ctrl_plane_map (eval_transformer_uint8 t c) = ctrl_plane_map c.
Proof.
  intros.
  induction t.
  - reflexivity.
  - rewrite <- IHt. apply ctrl_plane_invariant_transformer_intermediate.
Qed.