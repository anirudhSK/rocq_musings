From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import ListUtils.
From MyProject Require Import Maps.
From Stdlib Require Import Lists.List.
From Stdlib Require Import PArith.BinPos.
Import ListNotations.

(* The convenient equivalence: c1 and c2 agree on every program-variable
   lookup. *)
Definition cs_lookup_eq (c1 c2 : ConcreteTransformerState) : Prop :=
  (forall h : Header, lookup_varlike c1 h = lookup_varlike c2 h) /\
  (forall s : State,  lookup_varlike c1 s = lookup_varlike c2 s) /\
  (forall c : Ctrl,   lookup_varlike c1 c = lookup_varlike c2 c).

Transparent lookup_varlike_map.
Transparent map_from_ps.
Transparent update_varlike.
Transparent lookup_varlike.

(* A ctrl lookup reads only the ctrl map, so two states with equal ctrl maps
   agree on every ctrl lookup. *)
Lemma lookup_varlike_ctrl_t_ctrl_map :
  forall (c1 c2 : ConcreteTransformerState) (v : Ctrl),
    t_ctrl_map c1 = t_ctrl_map c2 ->
    lookup_varlike c1 v = lookup_varlike c2 v.
Proof.
  intros c1 c2 v H.
  unfold lookup_varlike. cbn [map_from_ps CrVarLike_Ctrl].
  rewrite H. reflexivity.
Qed.

(* update_varlike preserves cs_lookup_eq, regardless of the variable type.

   The cross-type cases (e.g. updating a Header doesn't affect State / Ctrl
   lookups) are definitional, so [apply ...] discharges them directly. *)
Lemma cs_lookup_eq_update_header :
  forall c1 c2 (h : Header) (x : CrVal),
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (update_varlike c1 h x) (update_varlike c2 h x).
Proof.
  intros c1 c2 h x [Hh [Hs Hc]].
  split; [| split].
  - intros h'. rewrite ! lookup_update_header_header.
    destruct h, h'. destruct (Coqlib.peq _ _); auto.
  - apply Hs.
  - apply Hc.
Qed.

Lemma cs_lookup_eq_update_state :
  forall c1 c2 (s : State) (x : CrVal),
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (update_varlike c1 s x) (update_varlike c2 s x).
Proof.
  intros c1 c2 s x [Hh [Hs' Hc]].
  split; [| split].
  - apply Hh.
  - intros s'. rewrite ! lookup_update_state_state.
    destruct s, s'. destruct (Coqlib.peq _ _); auto.
  - apply Hc.
Qed.

Lemma cs_lookup_eq_update_ctrl :
  forall c1 c2 (c : Ctrl) (x : CrVal),
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (update_varlike c1 c x) (update_varlike c2 c x).
Proof.
  intros c1 c2 c x [Hh [Hs Hc']].
  split; [| split].
  - apply Hh.
  - apply Hs.
  - intros c'. rewrite ! lookup_update_ctrl_ctrl.
    destruct c, c'. destruct (Coqlib.peq _ _); auto.
Qed.

(* lookup_concrete (used to evaluate function arguments) commutes with
   cs_lookup_eq. *)
Lemma lookup_concrete_eq :
  forall c1 c2 ty arg,
  cs_lookup_eq c1 c2 ->
  lookup_concrete ty arg c1 = lookup_concrete ty arg c2.
Proof.
  intros c1 c2 ty arg [Hh [Hs Hc]]. destruct arg; simpl;
    [apply Hc | apply Hh | reflexivity | apply Hs].
Qed.

Lemma eval_hdr_op_expr_concrete_eq :
  forall c1 c2 op,
  cs_lookup_eq c1 c2 ->
  eval_hdr_op_expr_concrete op c1 = eval_hdr_op_expr_concrete op c2.
Proof.
  intros c1 c2 op Hcs.
  (* The memory ops have no [lookup_concrete] to rewrite: they are not
     expressions of the state, and this yields ErrorVal for them. *)
  destruct op; cbn [eval_hdr_op_expr_concrete];
    try rewrite !(lookup_concrete_eq _ _ _ _ Hcs); reflexivity.
Qed.

Lemma eval_match_concrete_eq :
  forall c1 c2 mp,
  cs_lookup_eq c1 c2 ->
  eval_match_concrete mp c1 = eval_match_concrete mp c2.
Proof.
  intros c1 c2 mp [Hh [Hs Hc]].
  unfold eval_match_concrete.
  induction mp as [|[[hh cmp] mv] rest IH]; simpl; auto.
  rewrite IH. f_equal. f_equal.
  - apply Hh.
  - destruct mv; [reflexivity | apply Hh].
Qed.

(* With memory in play the statement gains a second half: two states that agree
   pointwise, run against the *same* memory, not only stay in agreement but
   also leave the memory in the same state.  That second half is what makes the
   induction go through, since the memory is threaded from one op to the next.
   It holds because everything a memory op reads out of the state -- the offset
   and, for a store, the value -- goes through [lookup_concrete].

   The memory-free counterparts follow below rather than as corollaries: the two
   evaluators are separate recursions (see the note on
   [CrConcreteSemanticsTransformer.eval_hdr_op_assign_concrete]). *)
Definition mem_and_state_eq
  (r1 r2 : ConcreteMemCtx * ConcreteTransformerState) : Prop :=
  fst r1 = fst r2 /\ cs_lookup_eq (snd r1) (snd r2).

Lemma eval_hdr_op_assign_concrete_mem_preserves_eq :
  forall c1 c2 mc op,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_hdr_op_assign_concrete_mem op mc c1)
                   (eval_hdr_op_assign_concrete_mem op mc c2).
Proof.
  intros c1 c2 mc op Hcs.
  pose proof (eval_hdr_op_expr_concrete_eq c1 c2 op Hcs) as Hexp.
  unfold mem_and_state_eq.
  destruct op as [f ty arg1 arg2 target | f ty arg1 arg2 target
                 | from to arg target | from to arg target
                 | ty r off target | ty r off val];
    cbn [eval_hdr_op_assign_concrete_mem fst snd].
  - rewrite Hexp. split; [reflexivity | apply cs_lookup_eq_update_state; assumption].
  - rewrite Hexp. split; [reflexivity | apply cs_lookup_eq_update_header; assumption].
  - rewrite Hexp. split; [reflexivity | apply cs_lookup_eq_update_state; assumption].
  - rewrite Hexp. split; [reflexivity | apply cs_lookup_eq_update_header; assumption].
  - rewrite !(lookup_concrete_eq _ _ _ _ Hcs).
    split; [reflexivity | apply cs_lookup_eq_update_header; assumption].
  - rewrite !(lookup_concrete_eq _ _ _ _ Hcs). split; [reflexivity | assumption].
Qed.

Lemma eval_hdr_op_list_concrete_mem_preserves_eq :
  forall c1 c2 mc hol,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_hdr_op_list_concrete_mem hol mc c1)
                   (eval_hdr_op_list_concrete_mem hol mc c2).
Proof.
  intros c1 c2 mc hol. revert c1 c2 mc.
  induction hol as [|op rest IH]; intros c1 c2 mc Hcs.
  - split; [reflexivity | assumption].
  - rewrite !eval_hdr_op_list_concrete_mem_cons.
    destruct (eval_hdr_op_assign_concrete_mem_preserves_eq c1 c2 mc op Hcs) as [Hm Hs].
    rewrite Hm. apply IH. assumption.
Qed.

Lemma eval_seq_rule_concrete_mem_preserves_eq :
  forall c1 c2 mc sr,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_seq_rule_concrete_mem sr mc c1)
                   (eval_seq_rule_concrete_mem sr mc c2).
Proof.
  intros c1 c2 mc [mp action] Hcs. simpl.
  rewrite (eval_match_concrete_eq _ _ mp Hcs).
  destruct (eval_match_concrete mp c2).
  - apply eval_hdr_op_list_concrete_mem_preserves_eq. assumption.
  - split; [reflexivity | assumption].
Qed.

Lemma eval_par_rule_concrete_mem_preserves_eq :
  forall c1 c2 mc pr,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_par_rule_concrete_mem pr mc c1)
                   (eval_par_rule_concrete_mem pr mc c2).
Proof.
  intros c1 c2 mc [mp action] Hcs. simpl.
  rewrite (eval_match_concrete_eq _ _ mp Hcs).
  destruct (eval_match_concrete mp c2).
  - apply eval_hdr_op_list_concrete_mem_preserves_eq. assumption.
  - split; [reflexivity | assumption].
Qed.

Lemma eval_match_action_rule_concrete_mem_preserves_eq :
  forall c1 c2 mc rule,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_match_action_rule_concrete_mem rule mc c1)
                   (eval_match_action_rule_concrete_mem rule mc c2).
Proof.
  intros c1 c2 mc [sr | pr] Hcs.
  - apply eval_seq_rule_concrete_mem_preserves_eq. assumption.
  - apply eval_par_rule_concrete_mem_preserves_eq. assumption.
Qed.

Lemma eval_hdr_op_assign_concrete_preserves_eq :
  forall c1 c2 op,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_hdr_op_assign_concrete op c1) (eval_hdr_op_assign_concrete op c2).
Proof.
  intros c1 c2 op Hcs.
  pose proof (eval_hdr_op_expr_concrete_eq c1 c2 op Hcs) as Hexp.
  unfold eval_hdr_op_assign_concrete.
  destruct op as [f ty arg1 arg2 target | f ty arg1 arg2 target
                 | from to arg target | from to arg target
                 | ty r off target | ty r off val];
    try rewrite Hexp.
  - apply cs_lookup_eq_update_state. assumption.
  - apply cs_lookup_eq_update_header. assumption.
  - apply cs_lookup_eq_update_state. assumption.
  - apply cs_lookup_eq_update_header. assumption.
  - apply cs_lookup_eq_update_header. assumption.
  - assumption.
Qed.

Lemma eval_hdr_op_list_concrete_preserves_eq :
  forall c1 c2 hol,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_hdr_op_list_concrete hol c1) (eval_hdr_op_list_concrete hol c2).
Proof.
  intros c1 c2 hol. revert c1 c2.
  induction hol as [|op rest IH]; intros.
  - simpl. assumption.
  - simpl. apply IH. apply eval_hdr_op_assign_concrete_preserves_eq. assumption.
Qed.

Lemma eval_seq_rule_concrete_preserves_eq :
  forall c1 c2 sr,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_seq_rule_concrete sr c1) (eval_seq_rule_concrete sr c2).
Proof.
  intros c1 c2 [mp action] Hcs. simpl.
  rewrite (eval_match_concrete_eq _ _ mp Hcs).
  destruct (eval_match_concrete mp c2); auto.
  apply eval_hdr_op_list_concrete_preserves_eq. assumption.
Qed.

Lemma eval_par_rule_concrete_preserves_eq :
  forall c1 c2 pr,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_par_rule_concrete pr c1) (eval_par_rule_concrete pr c2).
Proof.
  intros c1 c2 [mp action] Hcs. simpl.
  rewrite (eval_match_concrete_eq _ _ mp Hcs).
  destruct (eval_match_concrete mp c2); auto.
  apply eval_hdr_op_list_concrete_preserves_eq. assumption.
Qed.

Lemma eval_match_action_rule_concrete_preserves_eq :
  forall c1 c2 rule,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_match_action_rule_concrete rule c1) (eval_match_action_rule_concrete rule c2).
Proof.
  intros c1 c2 [sr | pr] Hcs.
  - apply eval_seq_rule_concrete_preserves_eq. assumption.
  - apply eval_par_rule_concrete_preserves_eq. assumption.
Qed.

Lemma get_match_results_eq :
  forall c1 c2 t,
  cs_lookup_eq c1 c2 ->
  get_match_results t c1 = get_match_results t c2.
Proof.
  intros c1 c2 t Hcs.
  unfold get_match_results.
  apply map_ext. intros [[mp _] | [mp _]]; apply eval_match_concrete_eq; assumption.
Qed.

Lemma eval_transformer_concrete_mem_preserves_eq :
  forall c1 c2 mc t,
  cs_lookup_eq c1 c2 ->
  mem_and_state_eq (eval_transformer_concrete_mem t mc c1)
                   (eval_transformer_concrete_mem t mc c2).
Proof.
  intros c1 c2 mc t Hcs.
  unfold eval_transformer_concrete_mem.
  rewrite (get_match_results_eq _ _ t Hcs).
  destruct (find_first_match (combine (get_match_results t c2) t)) as [rule|].
  - apply eval_match_action_rule_concrete_mem_preserves_eq. assumption.
  - split; [reflexivity | assumption].
Qed.

Lemma eval_transformer_concrete_preserves_eq :
  forall c1 c2 t,
  cs_lookup_eq c1 c2 ->
  cs_lookup_eq (eval_transformer_concrete t c1) (eval_transformer_concrete t c2).
Proof.
  intros c1 c2 t Hcs.
  unfold eval_transformer_concrete.
  rewrite (get_match_results_eq _ _ t Hcs).
  destruct (find_first_match (combine (get_match_results t c2) t)) as [rule|]; auto.
  apply eval_match_action_rule_concrete_preserves_eq. assumption.
Qed.

(* Convenient repackaged form: agreement at all 3 varlike types is preserved
   pointwise by the transformer. *)
Lemma transformer_preserves_lookup_equality_lemma :
  forall t c1 c2,
  (forall (h : Header) (s : State) (c : Ctrl),
    lookup_varlike c1 h = lookup_varlike c2 h /\
    lookup_varlike c1 s = lookup_varlike c2 s /\
    lookup_varlike c1 c = lookup_varlike c2 c)
  ->
  (forall (h : Header) (s : State) (c : Ctrl),
    lookup_varlike (eval_transformer_concrete t c1) h = lookup_varlike (eval_transformer_concrete t c2) h /\
    lookup_varlike (eval_transformer_concrete t c1) s = lookup_varlike (eval_transformer_concrete t c2) s /\
    lookup_varlike (eval_transformer_concrete t c1) c = lookup_varlike (eval_transformer_concrete t c2) c).
Proof.
  intros t c1 c2 H.
  assert (Hcs : cs_lookup_eq c1 c2).
  { split; [| split].
    - intros v. apply (H v (StateCtr xH) (CtrlCtr xH)).
    - intros v. apply (H (HeaderCtr xH) v (CtrlCtr xH)).
    - intros v. apply (H (HeaderCtr xH) (StateCtr xH) v). }
  pose proof (eval_transformer_concrete_preserves_eq _ _ t Hcs) as [Hh' [Hs' Hc']].
  intros h s c. split; [| split].
  - apply Hh'.
  - apply Hs'.
  - apply Hc'.
Qed.

Global Opaque lookup_varlike_map.
Global Opaque map_from_ps.
