From MyProject Require Import SmtExpr.
Require Import Classical.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* Import or define SeqRule and related types *)
From MyProject Require Import CrTransformer. (* Or replace with the correct module *)
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import ConcreteToSymbolicLemmas.

Inductive SmtResult : Type :=
  | SmtSat (f : SmtValuation)  (* Satisfiable with valuation f *)
  | SmtUnsat                   (* Unsatisfiable *)
  | SmtUnknown.                (* Unknown status *)

(* An SmtQuery takes an SmtBoolExpr and returns:
   None: meaning it is false for all possible valuations (or)
   Some(SmtValuation): a valuation for which it is true *)
Parameter smt_query : SmtBoolExpr -> SmtResult.

(* Axiom that smt_query is sound. *)
Axiom smt_query_sound_some : forall e v,
  smt_query e = SmtSat v ->
  eval_smt_bool e v = true.

(* Axiom that smt_query is complete. *)
Axiom smt_query_sound_none : forall e,
  smt_query e = SmtUnsat ->
  forall v', eval_smt_bool e v' = false.

(* check if s1 and s2 are equivalent *)
(* Need to look at all variables within s1 and s2,
   which means we need to iterate through header_list and state_var_list *)
(* function that given 2 states and a list of headers and state vars, asserts that each header/state var is the same across the two states *)
Definition check_headers_and_state_vars (s1 s2 : ProgramState SmtArithExpr)
  (header_list : list Header) (state_var_list : list StateVar)
  : SmtBoolExpr :=
  SmtBoolNot(
  SmtBoolAnd (List.fold_right (fun h acc => SmtBoolAnd acc (SmtBoolEq (lookup_hdr s1 h) (lookup_hdr s2 h))) 
                                    SmtTrue header_list)
             (List.fold_right (fun sv acc => SmtBoolAnd acc (SmtBoolEq (lookup_state s1 sv) (lookup_state s2 sv))) 
                                    SmtTrue state_var_list)).

Lemma eval_smt_bool_smt_bool_not_false :
  forall e1 e2 f,
  eval_smt_bool (SmtBoolNot (SmtBoolAnd e1 e2)) f = false ->
  eval_smt_bool e1 f = true /\ eval_smt_bool e2 f = true.
Proof.
  intros e1 e2 f H.
  simpl in H.
  destruct (eval_smt_bool e1 f && eval_smt_bool e2 f) eqn:Ex.
  -- apply andb_true_iff.
     assumption.
  -- exfalso. simpl in H. congruence.
Qed.

Lemma eval_smt_bool_smt_bool_not_true :
  forall e1 e2 f,
  eval_smt_bool (SmtBoolNot (SmtBoolAnd e1 e2)) f = true ->
  eval_smt_bool e1 f = false \/ eval_smt_bool e2 f = false.
Proof.
  intros e1 e2 f H.
  simpl in H.
  destruct (eval_smt_bool e1 f && eval_smt_bool e2 f) eqn:Ex.
  -- exfalso. simpl in H.
     congruence.
  -- apply andb_false_iff in Ex.
     assumption.
Qed.

Lemma SmtBoolConjunction_true_header:
  forall s1 s2 header_list f,
  eval_smt_bool (fold_right 
    (fun (h : Header) (acc : SmtBoolExpr) =>
          SmtBoolAnd acc
          (SmtBoolEq (lookup_hdr s1 h)
          (lookup_hdr s2 h))) SmtTrue header_list) f =
    true ->
  forallb (fun h => (eval_smt_bool
          (SmtBoolEq
          (lookup_hdr s1 h)
          (lookup_hdr s2 h)) f)) header_list = true.
Proof.
  intros s1 s2 header_list f H.
  induction header_list as [|h t IH].
  - simpl in H. reflexivity.
  - simpl in H.
    simpl. apply andb_true_iff. split.
    apply andb_true_iff in H. apply H.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    apply IH in H1.
    assumption.
Qed.

(* Same lemma as above, but for state var instead of header *)
Lemma SmtBoolConjunction_true_state_var:
  forall s1 s2 state_var_list f,
  eval_smt_bool (fold_right 
    (fun (sv : StateVar) (acc : SmtBoolExpr) =>
          SmtBoolAnd acc
          (SmtBoolEq (lookup_state s1 sv)
          (lookup_state s2 sv))) SmtTrue state_var_list) f =
    true ->
  forallb (fun sv => (eval_smt_bool
          (SmtBoolEq
          (lookup_state s1 sv)
          (lookup_state s2 sv)) f)) state_var_list = true.
Proof.
  intros s1 s2 state_var_list f H.
  induction state_var_list as [|sv t IH].
  - simpl in H. reflexivity.
  - simpl in H.
    simpl. apply andb_true_iff. split.
    apply andb_true_iff in H. apply H.
    apply andb_true_iff in H.
    destruct H as [H1 H2].
    apply IH in H1.
    assumption.
Qed.

Lemma SmtBoolConjunction_false_header:
  forall s1 s2 header_list f,
  eval_smt_bool (fold_right 
    (fun (h : Header) (acc : SmtBoolExpr) =>
          SmtBoolAnd acc
          (SmtBoolEq (lookup_hdr s1 h)
          (lookup_hdr s2 h))) SmtTrue header_list) f =
    false ->
  existsb (fun h => (eval_smt_bool
          (SmtBoolNot (SmtBoolEq
          (lookup_hdr s1 h)
          (lookup_hdr s2 h))) f)) header_list = true.
          (* there is a header (true), such that:
             If you assert the inequality of the headers (equality and then not),
             that resulting statement is true*)
Proof.
  intros s1 s2 header_list f H.
  induction header_list as [|h t IH].
  - simpl in H. exfalso. congruence.
  - simpl in *.
    apply andb_false_iff in H.
    apply orb_true_iff.
    destruct H.
    + right. apply IH in H.
      assumption.
    + apply f_equal with (f := negb) in H.
      simpl in H. left. assumption.
Qed.
  
(* Same lemma as above, but for state var instead of header *)
Lemma SmtBoolConjunction_false_state_var:
  forall s1 s2 state_var_list f,
  eval_smt_bool (fold_right 
    (fun (sv : StateVar) (acc : SmtBoolExpr) =>
          SmtBoolAnd acc
          (SmtBoolEq (lookup_state s1 sv)
          (lookup_state s2 sv))) SmtTrue state_var_list) f =
    false ->
  existsb (fun sv => (eval_smt_bool
          (SmtBoolNot (SmtBoolEq
          (lookup_state s1 sv)
          (lookup_state s2 sv))) f)) state_var_list = true.
          (* there is a state var (true), such that:
             If you assert the inequality of the state vars (equality and then not),
             that resulting statement is true*) 
Proof.
  intros s1 s2 state_var_list f H.
  induction state_var_list as [|sv t IH].
  - simpl in H. exfalso. congruence.
  - simpl in *.
    apply andb_false_iff in H.
    apply orb_true_iff.
    destruct H.
    + right. apply IH in H.
      assumption.
    + apply f_equal with (f := negb) in H.
      simpl in H. left. assumption.
Qed.

Lemma forallb_in_hdr_list :
  forall (f : Header -> bool) (l : list Header),
  forallb f l = true ->
  forall x, In x l -> f x = true.
Proof.
  intros f l H.
  induction l as [|x t IH].
  - intros x H_in. exfalso. simpl in H_in. contradiction.
  - simpl in H.
    apply andb_true_iff in H as [H1 H2].
    specialize (IH H2).
    simpl.
    intros x0.
    intros H_in.
    destruct H_in as [H_eq | H_in_t].
    + subst x0. assumption.
    + apply IH. assumption.
Qed.

(* Same lemma as above but for state var list *)
Lemma forallb_in_state_var_list :
  forall (f : StateVar -> bool) (l : list StateVar),
  forallb f l = true ->
  forall x, In x l -> f x = true.
Proof.
  intros f l H.
  induction l as [|x t IH].
  - intros x H_in. exfalso. simpl in H_in. contradiction.
  - simpl in H.
    apply andb_true_iff in H as [H1 H2].
    specialize (IH H2).
    simpl.
    intros x0.
    intros H_in.
    destruct H_in as [H_eq | H_in_t].
    + subst x0. assumption.
    + apply IH. assumption.
Qed.

Lemma check_headers_and_state_vars_false:
  forall s1 s2 header_list state_var_list f,
  eval_smt_bool(check_headers_and_state_vars s1 s2 header_list state_var_list) f = false ->
  (forall h, In h header_list -> eval_smt_bool (SmtBoolEq (lookup_hdr s1 h) (lookup_hdr s2 h)) f = true) /\
  (forall sv, In sv state_var_list -> eval_smt_bool (SmtBoolEq (lookup_state s1 sv) (lookup_state s2 sv)) f = true).
Proof.
  intros s1 s2 header_list state_var_list f H.
  unfold check_headers_and_state_vars in H.
  apply eval_smt_bool_smt_bool_not_false in H as [H1 H2].
  apply SmtBoolConjunction_true_header in H1.
  apply SmtBoolConjunction_true_state_var in H2.
  split.
  - apply forallb_in_hdr_list.
    assumption.
  - apply forallb_in_state_var_list.
    assumption.
Qed.

Lemma check_headers_and_state_vars_true:
  forall s1 s2 header_list state_var_list f,
  eval_smt_bool(check_headers_and_state_vars s1 s2 header_list state_var_list) f = true ->
  (exists h : Header, In h header_list /\
                      eval_smt_bool (SmtBoolEq (lookup_hdr s1 h) (lookup_hdr s2 h)) f = false) \/
  (exists sv : StateVar, In sv state_var_list /\
                      eval_smt_bool (SmtBoolEq (lookup_state s1 sv) (lookup_state s2 sv)) f = false).
Proof.
  intros s1 s2 header_list state_var_list f H.
  unfold check_headers_and_state_vars in H.
  apply eval_smt_bool_smt_bool_not_true in H.
  destruct H as [H1 | H2].
  - apply SmtBoolConjunction_false_header in H1. left.
    apply existsb_exists in H1.
    simpl in H1.
    destruct H1 as [h H1'].
    destruct H1' as [H_in H_eq].
    apply Bool.negb_true_iff in H_eq.
    simpl.
    exists h.
    split; assumption.
  - apply SmtBoolConjunction_false_state_var in H2. right.
    apply existsb_exists in H2.
    simpl in H2.
    destruct H2 as [sv H2'].
    destruct H2' as [H_in H_eq].
    apply Bool.negb_true_iff in H_eq.
    simpl.
    exists sv.
    split; assumption.
Qed.

Definition equivalence_checker
  (s : ProgramState SmtArithExpr)
  (t1 : Transformer) (t2 : Transformer)
  (header_list : list Header) (state_var_list : list StateVar)
   :  SmtResult :=
  (* assume a starting symbolic state s*)
  (* convert t1 and t2 to an equivalent final SmtArithExpr, assuming a start state of s *)
  let s1 := eval_transformer_smt t1 s in
  let s2 := eval_transformer_smt t2 s in
  (* check if the headers and state vars are equivalent *)
  smt_query (check_headers_and_state_vars s1 s2 header_list state_var_list).

Lemma uint8_eq_from_unsigned : forall (v1 v2 : uint8),
  unsigned v1 = unsigned v2 -> v1 = v2.
Proof.
  intros v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  apply mkint_eq; auto.
Qed.

(* TODO: Not sure if this lemma uses law of excluded middle or not?
   What about the intro Heq step? *)
Lemma uint8_neq_from_unsigned : forall (v1 v2 : uint8),
  unsigned v1 <> unsigned v2 -> v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  simpl in H.
  intro Heq.
  injection Heq as H_val_eq.
  apply H.
  assumption.
Qed.

Lemma uint8_if_else : forall (v1 v2 : uint8),
  ((if eq v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct (eq v1 v2) eqn:Ex.
  -- unfold eq in Ex.
     unfold Rocqlib.zeq in Ex.
     destruct (Z.eq_dec (unsigned v1) (unsigned v2)) as [Heq|Hneq].
     ++ apply uint8_eq_from_unsigned. assumption.
     ++ exfalso. congruence.
  -- exfalso. congruence.
Qed.

Lemma uint8_if_else2 : forall (v1 v2 : uint8),
  ((if eq v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct (eq v1 v2) eqn:Ex.
  -- unfold eq in Ex.
     unfold Rocqlib.zeq in Ex.
     destruct (Z.eq_dec (unsigned v1) (unsigned v2)) as [Heq|Hneq].
     ++ exfalso. congruence.
     ++ apply uint8_neq_from_unsigned. assumption.
  -- unfold eq in Ex.
     destruct (Rocqlib.zeq (unsigned v1) (unsigned v2)) eqn:Ex2.
     ++ exfalso. congruence.
     ++ apply uint8_neq_from_unsigned. assumption.
Qed.
        
Lemma smt_bool_eq_true : forall e1 e2 f,
  eval_smt_bool (SmtBoolEq e1 e2) f = true -> 
  eval_smt_arith e1 f = eval_smt_arith e2 f.
Proof.
  intros e1 e2 f H.
  destruct (eval_smt_bool (SmtBoolEq e1 e2) f) eqn:Ex1.
  -- destruct e1, e2; apply uint8_if_else in Ex1;
     try unfold eval_smt_arith; try assumption.
  -- exfalso. congruence.
Qed.

Lemma eval_smt_bool_lemma_hdr :
  forall t1 t2 s h f,
  eval_smt_bool
(SmtBoolEq (lookup_hdr (eval_transformer_smt t1 s) h)
(lookup_hdr (eval_transformer_smt t2 s) h)) f = true ->
lookup_hdr (eval_transformer_uint8 t1 (eval_sym_state s f)) h =
lookup_hdr (eval_transformer_uint8 t2 (eval_sym_state s f)) h.
Proof.
  intros t1 t2 s h f.
  intro H.
  apply smt_bool_eq_true in H.
  rewrite commute_sym_vs_conc_transfomer.
  rewrite commute_sym_vs_conc_transfomer.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_hdr.
  rewrite commute_mapper_lookup_hdr.
  apply H.
Qed.

Lemma eval_smt_bool_lemma_state :
  forall t1 t2 s sv f,
  eval_smt_bool
(SmtBoolEq (lookup_state (eval_transformer_smt t1 s) sv)
(lookup_state (eval_transformer_smt t2 s) sv)) f = true ->
lookup_state (eval_transformer_uint8 t1 (eval_sym_state s f)) sv =
lookup_state (eval_transformer_uint8 t2 (eval_sym_state s f)) sv.
Proof.
  intros t1 t2 s sv f.
  intro H.
  apply smt_bool_eq_true in H.
  rewrite commute_sym_vs_conc_transfomer.
  rewrite commute_sym_vs_conc_transfomer.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_state.
  rewrite commute_mapper_lookup_state.
  apply H.
Qed.

(* Soundness lemma about equivalence_checker conditional on the axioms above *)
Lemma equivalence_checker_sound :
  forall s t1 t2 header_list state_var_list f,
  equivalence_checker s t1 t2 header_list state_var_list = SmtUnsat ->
  let c  := eval_sym_state s f in
  let c1 := eval_transformer_uint8 t1 c in
  let c2 := eval_transformer_uint8 t2 c in
  (forall v, In v header_list ->
  (lookup_hdr c1 v) = (lookup_hdr c2 v)) /\
  (forall v, In v state_var_list ->
  (lookup_state c1 v) = (lookup_state c2 v)).
Proof.
  intros s t1 t2 header_list state_var_list f.
  intro H.
  simpl.
  unfold equivalence_checker in H.
  split; intro h; intro H_in.
  -- specialize (smt_query_sound_none _ H f) as H_complete.
     apply check_headers_and_state_vars_false in H_complete.
     destruct H_complete as [H_header H_state_var].
     clear H_state_var. (* declutter *)
     specialize (H_header h H_in).
     apply eval_smt_bool_lemma_hdr. assumption.
  -- specialize (smt_query_sound_none _ H f) as H_complete.
     apply check_headers_and_state_vars_false in H_complete.
     destruct H_complete as [H_header H_state_var].
     clear H_header. (* declutter *)
     specialize (H_state_var h H_in).
     apply eval_smt_bool_lemma_state. assumption.
Qed.

Print Assumptions equivalence_checker_sound.

Lemma smt_bool_eq_false : forall e1 e2 f,
  eval_smt_bool (SmtBoolEq e1 e2) f = false -> 
  eval_smt_arith e1 f <> eval_smt_arith e2 f.
Proof.
  intros e1 e2 f H.
  destruct (eval_smt_bool (SmtBoolEq e1 e2) f) eqn:Ex1.
  -- exfalso. congruence.
  -- destruct e1, e2; apply uint8_if_else2 in Ex1;
     try unfold eval_smt_arith; try assumption.
Qed.

Lemma eval_smt_bool_lemma_hdr_false :
  forall t1 t2 s h f,
  eval_smt_bool
(SmtBoolEq (lookup_hdr (eval_transformer_smt t1 s) h)
(lookup_hdr (eval_transformer_smt t2 s) h)) f = false ->
lookup_hdr (eval_transformer_uint8 t1 (eval_sym_state s f)) h <>
lookup_hdr (eval_transformer_uint8 t2 (eval_sym_state s f)) h.
Proof.
  intros t1 t2 s h f.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite commute_sym_vs_conc_transfomer.
  rewrite commute_sym_vs_conc_transfomer.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_hdr.
  rewrite commute_mapper_lookup_hdr.
  apply H.
Qed.

Lemma eval_smt_bool_lemma_state_false :
  forall t1 t2 s sv f,
  eval_smt_bool
(SmtBoolEq (lookup_state (eval_transformer_smt t1 s) sv)
(lookup_state (eval_transformer_smt t2 s) sv)) f = false ->
lookup_state (eval_transformer_uint8 t1 (eval_sym_state s f)) sv <>
lookup_state (eval_transformer_uint8 t2 (eval_sym_state s f)) sv.
Proof.
  intros t1 t2 s sv f.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite commute_sym_vs_conc_transfomer.
  rewrite commute_sym_vs_conc_transfomer.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_state.
  rewrite commute_mapper_lookup_state.
  apply H.
Qed.

(* Completeness lemma about equivalence_checker conditional on the axioms above *)
Lemma equivalence_checker_complete :
  forall s t1 t2 header_list state_var_list f',
  equivalence_checker s t1 t2 header_list state_var_list = SmtSat f' ->
  let c' := eval_sym_state s f' in
  let c1 := eval_transformer_uint8 t1 c' in
  let c2 := eval_transformer_uint8 t2 c' in
  (exists v, In v header_list /\
  (lookup_hdr c1 v) <> (lookup_hdr c2 v)) \/
  (exists v, In v state_var_list /\
  (lookup_state c1 v) <> (lookup_state c2 v)).
Proof.
  intros s t1 t2 header_list state_var_list f'.
  intro H.
  simpl.
  unfold equivalence_checker in H.
  destruct (smt_query (check_headers_and_state_vars (eval_transformer_smt t1 s) (eval_transformer_smt t2 s) header_list state_var_list)) eqn:H_query.
  - injection H as Heq.
    subst f'.
    apply smt_query_sound_some in H_query.
    apply check_headers_and_state_vars_true in H_query.
    destruct H_query as [H_header | H_state_var].
    -- destruct H_header as [h Hw].
       destruct Hw.
       pose proof (eval_smt_bool_lemma_hdr_false t1 t2 s h f H0) as H_neq.
       left.
       exists h.
       split; assumption.
    -- destruct H_state_var as [sv Hw].
       destruct Hw.
       pose proof (eval_smt_bool_lemma_state_false t1 t2 s sv f H0) as H_neq.
       right.
       exists sv.
       split; assumption.
  - discriminate H.
  - discriminate H.
Qed.

Print Assumptions equivalence_checker_complete.
