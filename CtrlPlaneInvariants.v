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
         (c1: ConcreteState),
  ctrl_map (eval_hdr_op_assign_concrete ho c1) =
  ctrl_map c1.
Proof.
  intros ho c1.
  destruct ho; simpl; try reflexivity.
Qed.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_list:
  forall hol c1,
  ctrl_map (eval_hdr_op_list_concrete hol c1) =
  ctrl_map c1.
Proof.
  intros.
  induction hol.
  - reflexivity.
  - simpl. rewrite <- IHhol.
    apply ctrl_plane_invariant_hdr_op.
Qed.


Lemma ctrl_plane_invariant_seq_rule:
  forall s c,
    ctrl_map (eval_seq_rule_concrete s c) =
    ctrl_map c.
Proof.
  intros.
  unfold eval_seq_rule_concrete.
  destruct s.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule:
  forall p c,
    ctrl_map (eval_par_rule_concrete p c) =
    ctrl_map c.
Proof.
  intros.
  unfold eval_par_rule_concrete.
  destruct p.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_ma_rule:
  forall m c,
    ctrl_map (eval_match_action_rule_concrete m c) =
    ctrl_map c.
Proof.
  intros.
  unfold eval_match_action_rule_concrete.
  destruct m.
  - apply ctrl_plane_invariant_seq_rule.
  - apply ctrl_plane_invariant_par_rule.
Qed.

Lemma ctrl_plane_invariant_transformer_intermediate:
  forall a t c,
    ctrl_map (eval_transformer_concrete (a :: t) c) =
    ctrl_map (eval_transformer_concrete t c).
Proof.
  intros.
  unfold eval_transformer_concrete.
  remember (a :: t) as full_list.
  remember (find_first_match (combine (get_match_results full_list c) full_list)) as outer_match.
  remember (find_first_match (combine (get_match_results t c) t)) as inner_match.
  destruct (outer_match) eqn:des; destruct inner_match eqn:des2; try rewrite ctrl_plane_invariant_ma_rule; try reflexivity.
  rewrite ctrl_plane_invariant_ma_rule. reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer:
  forall c t,
    ctrl_map (eval_transformer_concrete t c) = ctrl_map c.
Proof.
  intros.
  induction t.
  - reflexivity.
  - rewrite <- IHt. apply ctrl_plane_invariant_transformer_intermediate.
Qed.