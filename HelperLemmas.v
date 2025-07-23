(* Miscellaneous helper lemmas for ConcreteToSymbolicLemmas.v *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtExpr.
Require Import ZArith.
Require Import Coq.Lists.List.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From Coq Require Import FunctionalExtensionality.

Lemma program_state_equality:
      forall (ps1 ps2: ProgramState uint8),
        ctrl_plane_map ps1 = ctrl_plane_map ps2 ->
        header_map ps1 = header_map ps2 ->
        state_var_map  ps1 = state_var_map ps2 ->
        ps1 = ps2.
Proof.
  intros ps1 ps2 Hctrl Hhdr Hstate.
  destruct ps1 as [ctrl1 hdr1 state1].
  destruct ps2 as [ctrl2 hdr2 state2].
  simpl in *.
  f_equal; try assumption.
Qed.

Lemma program_state_equality_sym:
      forall (ps1 ps2: ProgramState SmtArithExpr),
        ctrl_plane_map ps1 = ctrl_plane_map ps2 ->
        header_map ps1 = header_map ps2 ->
        state_var_map  ps1 = state_var_map ps2 ->
        ps1 = ps2.
Proof.
  intros ps1 ps2 Hctrl Hhdr Hstate.
  destruct ps1 as [ctrl1 hdr1 state1].
  destruct ps2 as [ctrl2 hdr2 state2].
  simpl in *.
  f_equal; try assumption.
Qed.

Lemma nothing_changed_state:
  forall s f target,
    eval_sym_state s f = 
    update_state (eval_sym_state s f) target
     (eval_smt_arith (lookup_state s target) f).
Proof.
  intros s f target.
  destruct target.
  unfold eval_sym_state.
  apply program_state_equality; simpl; try reflexivity.
  apply functional_extensionality.
  intros x.
  destruct x.
  destruct (uid =? uid0)%positive eqn:des.
  - apply Pos.eqb_eq in des.
    rewrite des.
    reflexivity.
  - reflexivity.
Qed.

Lemma nothing_changed_hdr:
  forall s f target,
    eval_sym_state s f = 
    update_hdr (eval_sym_state s f) target
     (eval_smt_arith (lookup_hdr s target) f).
Proof.
  intros s f target.
  destruct target.
  unfold eval_sym_state.
  apply program_state_equality; simpl; try reflexivity.
  apply functional_extensionality.
  intros x.
  destruct x.
  destruct (uid =? uid0)%positive eqn:des.
  - apply Pos.eqb_eq in des.
    rewrite des.
    reflexivity.
  - reflexivity.
Qed.

Lemma commute_lookup_eval:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation)
        arg,
    lookup_uint8 arg (eval_sym_state s f) =
    eval_smt_arith (lookup_smt arg s) f.
Proof.
  intros s f arg.
  destruct arg; simpl; reflexivity.
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

Lemma header_map_ps :
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
Lemma state_var_map_ps :
  forall s f sv,
    lookup_state (eval_sym_state s f) sv =
    eval_smt_arith (lookup_state s sv) f.
Proof.
  intros.
  unfold eval_sym_state.
  simpl.
  reflexivity.
Qed.