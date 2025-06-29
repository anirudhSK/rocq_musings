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

Lemma check_headers_and_state_vars_false:
  forall s1 s2 header_list state_var_list f,
  eval_smt_bool(check_headers_and_state_vars s1 s2 header_list state_var_list) f = false ->
  (forall h, In h header_list -> eval_smt_bool (SmtBoolEq (header_map SmtArithExpr s1 h) (header_map SmtArithExpr s2 h)) f = true) /\
  (forall sv, In sv state_var_list -> eval_smt_bool (SmtBoolEq (state_var_map SmtArithExpr s1 sv) (state_var_map SmtArithExpr s2 sv)) f = true).
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

  (* Need to use law of excluded middle to go from equivalence_checker definition (there is no valuation (None)
                                                                                   for which they are not equal (SmtBoolNot))
   to the forall condition that for all valuations they are equal for all headers and state vars *)

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
Admitted.