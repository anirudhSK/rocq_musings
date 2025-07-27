(* Miscellaneous helper lemmas for ConcreteToSymbolicLemmas.v *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtExpr.
Require Import ZArith.
Require Import Coq.Lists.List.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From Coq Require Import FunctionalExtensionality.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import CrProgramState.

Lemma nothing_changed_state:
  forall s f target,
    eval_sym_state s f = 
    update_state (eval_sym_state s f) target (eval_smt_arith (lookup_state s target) f).
Proof.
  intros s f target.
  unfold eval_sym_state.
  specialize (commute_mapper_update_state (T1 := SmtArithExpr) (T2 := uint8)).
  intros.
  specialize (H s target (lookup_state s target) (fun e : SmtArithExpr => eval_smt_arith e f)).
  rewrite <- H.
  rewrite update_lookup_inverses_state.
  reflexivity.
Qed.

Lemma nothing_changed_hdr:
  forall s f target,
    eval_sym_state s f = 
    update_hdr (eval_sym_state s f) target
     (eval_smt_arith (lookup_hdr s target) f).
Proof.
  intros s f target.
  unfold eval_sym_state.
  specialize (commute_mapper_update_hdr (T1 := SmtArithExpr) (T2 := uint8)).
  intros.
  specialize (H s target (lookup_hdr s target) (fun e : SmtArithExpr => eval_smt_arith e f)).
  rewrite <- H.
  rewrite update_lookup_inverses_hdr.
  reflexivity.
Qed.

Lemma commute_lookup_eval_state:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation)
        sv,
    lookup_state (eval_sym_state s f) sv =
    eval_smt_arith (lookup_state s sv) f.
Proof.
  intros s f sv.
  destruct sv.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_state.
  reflexivity.
Qed.

Lemma commute_lookup_eval_hdr:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation)
        hv,
    lookup_hdr (eval_sym_state s f) hv =
    eval_smt_arith (lookup_hdr s hv) f.
Proof.
  intros s f hv.
  destruct hv.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_hdr.
  reflexivity.
Qed.

Lemma commute_lookup_eval:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation)
        arg,
    lookup_uint8 arg (eval_sym_state s f) =
    eval_smt_arith (lookup_smt arg s) f.
Proof.
  intros s f arg.
  destruct arg; simpl; try reflexivity.
  apply PMapHelperLemmas.commute_lookup_eval_ctrl.
Qed.

Lemma find_first_match_lemma:
  forall {T : Set} (list_of_pair :  list (bool*T)),
    None = find_first_match list_of_pair ->
    forall x,
    In x list_of_pair -> fst x = false.
Proof.
  intros.
  induction list_of_pair as [| [b t] rest].
  - simpl in H0. contradiction.
  - simpl in H0. destruct H0 eqn:des.
    + subst. simpl in H. destruct b.
      * discriminate H.
      * reflexivity.
    + subst. simpl in H. destruct b.
      * discriminate H.
      * apply IHrest; assumption.
Qed.

Lemma find_first_match_lemma2:
  forall {T : Set} (list_of_pair :  list (bool*T)) element,
    Some element = find_first_match list_of_pair ->
    In (true, element) list_of_pair.
Proof.
  intros.
  induction list_of_pair as [| [b t] rest].
  - simpl in H. discriminate H.
  - simpl in H.
    simpl.
    destruct b.
    -- inversion H. left. reflexivity.
    -- right. apply IHrest.
       assumption.
Qed.

Lemma header_map_ps : (*TODO: Should probably be called lookup_hdr_ps *)
  forall s f h,
    lookup_hdr (eval_sym_state s f) h =
    eval_smt_arith (lookup_hdr s h) f.
Proof.
  intros.
  unfold eval_sym_state.
  simpl.
  reflexivity.
Qed.

(* Create a lemma similar to header_map_ps but with state_var_map instead *)
Lemma state_var_map_ps : (* Same TODO as header_map_ps, bad naming *)
  forall s f sv,
    lookup_state (eval_sym_state s f) sv =
    eval_smt_arith (lookup_state s sv) f.
Proof.
  intros.
  unfold eval_sym_state.
  simpl.
  reflexivity.
Qed.