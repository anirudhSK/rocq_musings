(* Various helper lemmas showing ctrl plane maps don't change *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrProgramState.
From MyProject Require Import ListUtils.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Bool.Bool.

(* Each lemma comes in two versions, because the concrete transformer has two
   evaluators (see the note on [eval_hdr_op_assign_concrete]): a [_mem] one
   over the memory-threading evaluator the network semantics runs, and one over
   the memory-free evaluator the transformer-level checker runs.  They are
   separate recursions, so neither proof follows from the other; both are
   short.  Memory changes nothing here in either case -- a load writes a header
   and a store writes only memory, so neither can touch the ctrl map. *)

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_mem:
  forall (ho: HdrOp) (mc : ConcreteMemCtx) (c1: ConcreteTransformerState),
  t_ctrl_map (snd (eval_hdr_op_assign_concrete_mem ho mc c1)) =
  t_ctrl_map c1.
Proof.
  intros ho mc c1.
  destruct ho; simpl; try reflexivity.
Qed.

Lemma ctrl_plane_invariant_hdr_op:
  forall (ho: HdrOp)
         (c1: ConcreteTransformerState),
  t_ctrl_map (eval_hdr_op_assign_concrete ho c1) =
  t_ctrl_map c1.
Proof.
  intros ho c1. destruct ho; simpl; try reflexivity.
Qed.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_list_mem:
  forall hol mc c1,
  t_ctrl_map (snd (eval_hdr_op_list_concrete_mem hol mc c1)) =
  t_ctrl_map c1.
Proof.
  intros hol. induction hol; intros mc c1.
  - reflexivity.
  - rewrite eval_hdr_op_list_concrete_mem_cons, IHhol.
    apply ctrl_plane_invariant_hdr_op_mem.
Qed.

Lemma ctrl_plane_invariant_hdr_op_list:
  forall hol c1,
  t_ctrl_map (eval_hdr_op_list_concrete hol c1) =
  t_ctrl_map c1.
Proof.
  intros hol c1. revert c1.
  induction hol; intros c1.
  - reflexivity.
  - simpl. rewrite IHhol.
    apply ctrl_plane_invariant_hdr_op.
Qed.

Lemma ctrl_plane_invariant_seq_rule_mem:
  forall s mc c,
    t_ctrl_map (snd (eval_seq_rule_concrete_mem s mc c)) =
    t_ctrl_map c.
Proof.
  intros.
  unfold eval_seq_rule_concrete_mem.
  destruct s.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list_mem.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_seq_rule:
  forall s c,
    t_ctrl_map (eval_seq_rule_concrete s c) =
    t_ctrl_map c.
Proof.
  intros. unfold eval_seq_rule_concrete. destruct s.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule_mem:
  forall p mc c,
    t_ctrl_map (snd (eval_par_rule_concrete_mem p mc c)) =
    t_ctrl_map c.
Proof.
  intros.
  unfold eval_par_rule_concrete_mem.
  destruct p.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list_mem.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule:
  forall p c,
    t_ctrl_map (eval_par_rule_concrete p c) =
    t_ctrl_map c.
Proof.
  intros. unfold eval_par_rule_concrete. destruct p.
  destruct (eval_match_concrete match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_ma_rule_mem:
  forall m mc c,
    t_ctrl_map (snd (eval_match_action_rule_concrete_mem m mc c)) =
    t_ctrl_map c.
Proof.
  intros.
  unfold eval_match_action_rule_concrete_mem.
  destruct m.
  - apply ctrl_plane_invariant_seq_rule_mem.
  - apply ctrl_plane_invariant_par_rule_mem.
Qed.

Lemma ctrl_plane_invariant_ma_rule:
  forall m c,
    t_ctrl_map (eval_match_action_rule_concrete m c) =
    t_ctrl_map c.
Proof.
  intros. unfold eval_match_action_rule_concrete. destruct m.
  - apply ctrl_plane_invariant_seq_rule.
  - apply ctrl_plane_invariant_par_rule.
Qed.

Lemma ctrl_plane_invariant_transformer_mem:
  forall t mc c,
    t_ctrl_map (snd (eval_transformer_concrete_mem t mc c)) = t_ctrl_map c.
Proof.
  intros.
  unfold eval_transformer_concrete_mem.
  destruct (find_first_match (combine (get_match_results t c) t)).
  - apply ctrl_plane_invariant_ma_rule_mem.
  - reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer:
  forall c t,
    t_ctrl_map (eval_transformer_concrete t c) = t_ctrl_map c.
Proof.
  intros. unfold eval_transformer_concrete.
  destruct (find_first_match (combine (get_match_results t c) t)).
  - apply ctrl_plane_invariant_ma_rule.
  - reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer_intermediate:
  forall a t c,
    t_ctrl_map (eval_transformer_concrete (a :: t) c) =
    t_ctrl_map (eval_transformer_concrete t c).
Proof.
  intros. rewrite !ctrl_plane_invariant_transformer. reflexivity.
Qed.
