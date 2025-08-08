From MyProject Require Import SmtExpr.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import MyInts.
Require Import Bool.
Require Import List.

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
    (fun (sv :State) (acc : SmtBoolExpr) =>
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
    (fun (sv :State) (acc : SmtBoolExpr) =>
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

Lemma smt_bool_eq_true : forall e1 e2 f,
  eval_smt_bool (SmtBoolEq e1 e2) f = true -> 
  eval_smt_arith e1 f = eval_smt_arith e2 f.
Proof.
  intros e1 e2 f H.
  destruct (eval_smt_bool (SmtBoolEq e1 e2) f) eqn:Ex1.
  -- destruct e1, e2; apply uint8_concrete_if_else in Ex1;
     try unfold eval_smt_arith; try assumption.
  -- exfalso. congruence.
Qed.

Lemma smt_bool_eq_false : forall e1 e2 f,
  eval_smt_bool (SmtBoolEq e1 e2) f = false -> 
  eval_smt_arith e1 f <> eval_smt_arith e2 f.
Proof.
  intros e1 e2 f H.
  destruct (eval_smt_bool (SmtBoolEq e1 e2) f) eqn:Ex1.
  -- exfalso. congruence.
  -- destruct e1, e2; apply uint8_concrete_if_else2 in Ex1;
     try unfold eval_smt_arith; try assumption.
Qed.