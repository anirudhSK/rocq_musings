From MyProject Require Import SmtExpr.
Require Import Classical.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

(* Import or define SeqRule and related types *)
From MyProject Require Import CrTransformer. (* Or replace with the correct module *)
From MyProject Require Import CrSymbolicSemantics.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import ConcreteToSymbolicLemmas.

(* An SmtQuery takes an SmtBoolExpr and returns:
   None: meaning it is false for all possible valuations (or)
   Some(SmtValuation): a valuation for which it is true *)
Parameter smt_query : SmtBoolExpr -> option (SmtValuation).

(* Axiom that smt_query is sound. *)
Axiom smt_query_sound : forall e v,
  smt_query e = Some v ->
  eval_smt_bool e v = true.

(* Axiom that smt_query is complete. *)
Axiom smt_query_complete : forall e,
  smt_query e = None ->
  forall v', eval_smt_bool e v' = false.

(* check if s1 and s2 are equivalent *)
(* Need to look at all variables within s1 and s2,
   which means we need to iterate through header_list and state_var_list *)
(* function that given 2 states and a list of headers and state vars, asserts that each header/state var is the same across the two states *)
Definition check_headers_and_state_vars (s1 s2 : ProgramState SmtArithExpr)
  (header_list : list Header) (state_var_list : list StateVar)
  : SmtBoolExpr :=
  SmtBoolNot(
  SmtBoolAnd (List.fold_right (fun h acc => SmtBoolAnd acc (SmtBoolEq (header_map SmtArithExpr s1 h) (header_map SmtArithExpr s2 h))) 
                                    SmtTrue header_list)
             (List.fold_right (fun sv acc => SmtBoolAnd acc (SmtBoolEq (state_var_map SmtArithExpr s1 sv) (state_var_map SmtArithExpr s2 sv))) 
                                    SmtTrue state_var_list)).

Lemma eval_smt_bool_smt_bool_not :
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

Lemma SmtBoolConjunction_true_header:
  forall s1 s2 header_list f,
  eval_smt_bool (fold_right 
    (fun (h : Header) (acc : SmtBoolExpr) =>
          SmtBoolAnd acc
          (SmtBoolEq (header_map SmtArithExpr s1 h)
          (header_map SmtArithExpr s2 h))) SmtTrue header_list) f =
    true ->
  forallb (fun h => (eval_smt_bool
          (SmtBoolEq
          (header_map SmtArithExpr s1 h)
          (header_map SmtArithExpr s2 h)) f)) header_list = true.
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
          (SmtBoolEq (state_var_map SmtArithExpr s1 sv)
          (state_var_map SmtArithExpr s2 sv))) SmtTrue state_var_list) f =
    true ->
  forallb (fun sv => (eval_smt_bool
          (SmtBoolEq
          (state_var_map SmtArithExpr s1 sv)
          (state_var_map SmtArithExpr s2 sv)) f)) state_var_list = true.
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
  (forall h, In h header_list -> eval_smt_bool (SmtBoolEq (header_map SmtArithExpr s1 h) (header_map SmtArithExpr s2 h)) f = true) /\
  (forall sv, In sv state_var_list -> eval_smt_bool (SmtBoolEq (state_var_map SmtArithExpr s1 sv) (state_var_map SmtArithExpr s2 sv)) f = true).
Proof.
  intros s1 s2 header_list state_var_list f H.
  unfold check_headers_and_state_vars in H.
  apply eval_smt_bool_smt_bool_not in H as [H1 H2].
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
                      eval_smt_bool (SmtBoolEq (header_map SmtArithExpr s1 h) (header_map SmtArithExpr s2 h)) f = false) \/
  (exists sv : StateVar, In sv state_var_list /\
                      eval_smt_bool (SmtBoolEq (state_var_map SmtArithExpr s1 sv) (state_var_map SmtArithExpr s2 sv)) f = false).
Proof.
Admitted.

Definition equivalence_checker
  (s : ProgramState SmtArithExpr)
  (sr1 : SeqRule) (sr2 : SeqRule)
  (header_list : list Header) (state_var_list : list StateVar)
   :  option (SmtValuation) :=
  (* assume a starting symbolic state s*)
  (* convert sr1 and sr2 to an equivalent SmtArithExpr, assuming s *)
  let s1 := eval_seq_rule_smt sr1 s in
  let s2 := eval_seq_rule_smt sr2 s in
  (* check if the headers and state vars are equivalent *)
  smt_query (check_headers_and_state_vars s1 s2 header_list state_var_list).

Lemma uint8_eq_from_unsigned : forall (v1 v2 : uint8),
  unsigned v1 = unsigned v2 -> v1 = v2.
Proof.
  intros v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  simpl in H.
  subst val2.
  f_equal.
  (* The proof obligations about range equality should be automatic *)
  apply proof_irrelevance.
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
  forall sr1 sr2 s h f,
  eval_smt_bool
(SmtBoolEq (header_map SmtArithExpr (eval_seq_rule_smt sr1 s) h)
(header_map SmtArithExpr (eval_seq_rule_smt sr2 s) h)) f = true ->
header_map uint8 (eval_seq_rule_uint8 sr1 (eval_sym_state s f)) h =
header_map uint8 (eval_seq_rule_uint8 sr2 (eval_sym_state s f)) h.
Proof.
  intros sr1 sr2 s h f.
  intro H.
  apply smt_bool_eq_true in H.
  rewrite symbolic_vs_concrete_seq_rule.
  rewrite symbolic_vs_concrete_seq_rule.
  apply H.
Qed.

Lemma eval_smt_bool_lemma_state :
  forall sr1 sr2 s sv f,
  eval_smt_bool
(SmtBoolEq (state_var_map SmtArithExpr (eval_seq_rule_smt sr1 s) sv)
(state_var_map SmtArithExpr (eval_seq_rule_smt sr2 s) sv)) f = true ->
state_var_map uint8 (eval_seq_rule_uint8 sr1 (eval_sym_state s f)) sv =
state_var_map uint8 (eval_seq_rule_uint8 sr2 (eval_sym_state s f)) sv.
Proof.
  intros sr1 sr2 s sv f.
  intro H.
  apply smt_bool_eq_true in H.
  rewrite symbolic_vs_concrete_seq_rule.
  rewrite symbolic_vs_concrete_seq_rule.
  apply H.
Qed.

(* Soundness lemma about equivalence_checker conditional on the axioms above *)
Lemma equivalence_checker_sound :
  forall s sr1 sr2 header_list state_var_list f,
  equivalence_checker s sr1 sr2 header_list state_var_list = None ->
  let c  := eval_sym_state s f in
  let c1 := eval_seq_rule_uint8 sr1 c in
  let c2 := eval_seq_rule_uint8 sr2 c in
  (forall v, In v header_list ->
  (header_map uint8 c1 v) = (header_map uint8 c2 v)) /\
  (forall v, In v state_var_list ->
  (state_var_map uint8 c1 v) = (state_var_map uint8 c2 v)).
Proof.
  intros s sr1 sr2 header_list state_var_list f.
  intro H.
  simpl.
  unfold equivalence_checker in H.
  split; intro h; intro H_in.
  -- specialize (smt_query_complete _ H f) as H_complete.
     apply check_headers_and_state_vars_false in H_complete.
     destruct H_complete as [H_header H_state_var].
     clear H_state_var. (* declutter *)
     specialize (H_header h H_in).
     apply eval_smt_bool_lemma_hdr. assumption.
  -- specialize (smt_query_complete _ H f) as H_complete.
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
Admitted.

Lemma eval_smt_bool_lemma_hdr_false :
  forall sr1 sr2 s h f,
  eval_smt_bool
(SmtBoolEq (header_map SmtArithExpr (eval_seq_rule_smt sr1 s) h)
(header_map SmtArithExpr (eval_seq_rule_smt sr2 s) h)) f = false ->
header_map uint8 (eval_seq_rule_uint8 sr1 (eval_sym_state s f)) h <>
header_map uint8 (eval_seq_rule_uint8 sr2 (eval_sym_state s f)) h.
Proof.
  intros sr1 sr2 s h f.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite symbolic_vs_concrete_seq_rule.
  rewrite symbolic_vs_concrete_seq_rule.
  apply H.
Qed.

Lemma eval_smt_bool_lemma_state_false :
  forall sr1 sr2 s sv f,
  eval_smt_bool
(SmtBoolEq (state_var_map SmtArithExpr (eval_seq_rule_smt sr1 s) sv)
(state_var_map SmtArithExpr (eval_seq_rule_smt sr2 s) sv)) f = false ->
state_var_map uint8 (eval_seq_rule_uint8 sr1 (eval_sym_state s f)) sv <>
state_var_map uint8 (eval_seq_rule_uint8 sr2 (eval_sym_state s f)) sv.
Proof.
  intros sr1 sr2 s sv f.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite symbolic_vs_concrete_seq_rule.
  rewrite symbolic_vs_concrete_seq_rule.
  apply H.
Qed.

(* Completeness lemma about equivalence_checker conditional on the axioms above *)
Lemma equivalence_checker_complete :
  forall s sr1 sr2 header_list state_var_list f',
  equivalence_checker s sr1 sr2 header_list state_var_list = Some f' ->
  let c' := eval_sym_state s f' in
  let c1 := eval_seq_rule_uint8 sr1 c' in
  let c2 := eval_seq_rule_uint8 sr2 c' in
  (exists v, In v header_list /\
  (header_map uint8 c1 v) <> (header_map uint8 c2 v)) \/
  (exists v, In v state_var_list /\
  (state_var_map uint8 c1 v) <> (state_var_map uint8 c2 v)).
Proof.
  intros s sr1 sr2 header_list state_var_list f'.
  intro H.
  simpl.
  unfold equivalence_checker in H.
  destruct (smt_query (check_headers_and_state_vars (eval_seq_rule_smt sr1 s) (eval_seq_rule_smt sr2 s) header_list state_var_list)) eqn:H_query.
  - injection H as Heq.
    subst f'.
    apply smt_query_sound in H_query.
    apply check_headers_and_state_vars_true in H_query.
    destruct H_query as [H_header | H_state_var].
    -- destruct H_header as [h Hw].
       destruct Hw.
       pose proof (eval_smt_bool_lemma_hdr_false sr1 sr2 s h s0 H0) as H_neq.
       left.
       exists h.
       split; assumption.
    -- destruct H_state_var as [sv Hw].
       destruct Hw.
       pose proof (eval_smt_bool_lemma_state_false sr1 sr2 s sv s0 H0) as H_neq.
       right.
       exists sv.
       split; assumption.
  - discriminate H.
Qed.