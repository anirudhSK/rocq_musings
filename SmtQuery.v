From MyProject Require Import SmtExpr.
Require Import Classical.
Require Import Coq.Lists.List.
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
  SmtBoolNot (List.fold_right (fun h acc => SmtBoolAnd acc (SmtBoolEq (header_map SmtArithExpr s1 h) (header_map SmtArithExpr s2 h))) 
                   (List.fold_right (fun sv acc => SmtBoolAnd acc (SmtBoolEq (state_var_map SmtArithExpr s1 sv) (state_var_map SmtArithExpr s2 sv))) 
                                    SmtTrue state_var_list) header_list).

(* Want to prove a lemma for check_headers_and_state_vars. Move it out of equivalence_checker as its own function. *)

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
  split.
  -- intros. admit.
  -- admit.
Admitted.

  (* Need to use law of excluded middle to go from equivalence_checker definition (there is no valuation (None)
                                                                                   for which they are not equal (SmtBoolNot))
   to the forall condition that for all valuations they are equal for all headers and state vars *)
(* Want to combine this with the main lemma about symbolic-concrete semantics from the bottom of ConcreteToSymbolicLemmas.v *)

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