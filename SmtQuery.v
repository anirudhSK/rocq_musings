From MyProject Require Import SmtExpr.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import InitStatus.
From MyProject Require Import CrProgramState.
From MyProject Require Import Maps.
From MyProject Require Import SmtTypes.
From MyProject Require Import Integers.
Require Import Classical.
Require Import Coq.Lists.List.
Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
From Coq Require Import FunctionalExtensionality.
Import ListNotations.

(* Import or define SeqRule and related types *)
From MyProject Require Import CrTransformer. (* Or replace with the correct module *)
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import ConcreteToSymbolicLemmas.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import UtilLemmas.

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
Definition check_headers_and_state_vars (s1 s2 : SymbolicState)
  (header_list : list Header) (state_var_list : list State)
  : SmtBoolExpr :=
  SmtBoolNot(
  SmtBoolAnd (List.fold_right (fun h acc => SmtBoolAnd acc (SmtBoolEq (lookup_hdr s1 h) (lookup_hdr s2 h))) 
                                    SmtTrue header_list)
             (List.fold_right (fun sv acc => SmtBoolAnd acc (SmtBoolEq (lookup_state s1 sv) (lookup_state s2 sv))) 
                                    SmtTrue state_var_list)).

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
  (exists sv :State, In sv state_var_list /\
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

Lemma eval_smt_bool_lemma_hdr :
  forall t1 t2 s h f,
  is_header_in_ps s h <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_hdr (eval_transformer_smt t1 s) h)
(lookup_hdr (eval_transformer_smt t2 s) h)) f = true ->
lookup_hdr (eval_transformer_concrete t1 (eval_sym_state s f)) h =
lookup_hdr (eval_transformer_concrete t2 (eval_sym_state s f)) h.
Proof.
  intros t1 t2 s h f.
  intro H.
  intros H_eq.
  apply smt_bool_eq_true in H_eq.
  rewrite commute_sym_vs_conc_transfomer_hdr.
  rewrite commute_sym_vs_conc_transfomer_hdr.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_hdr.
  rewrite commute_mapper_lookup_hdr.
  apply H_eq.
  assumption. assumption.
Qed.

Lemma eval_smt_bool_lemma_state :
  forall t1 t2 s sv f,
  is_state_var_in_ps s sv <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_state (eval_transformer_smt t1 s) sv)
(lookup_state (eval_transformer_smt t2 s) sv)) f = true ->
lookup_state (eval_transformer_concrete t1 (eval_sym_state s f)) sv =
lookup_state (eval_transformer_concrete t2 (eval_sym_state s f)) sv.
Proof.
  intros t1 t2 s sv f.
  intro H.
  intros H_eq.
  apply smt_bool_eq_true in H_eq.
  rewrite commute_sym_vs_conc_transfomer_sv.
  rewrite commute_sym_vs_conc_transfomer_sv.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_state.
  rewrite commute_mapper_lookup_state.
  apply H_eq.
  assumption. assumption.
Qed.

Lemma eval_smt_bool_lemma_hdr_false :
  forall t1 t2 s h f,
  is_header_in_ps s h <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_hdr (eval_transformer_smt t1 s) h)
(lookup_hdr (eval_transformer_smt t2 s) h)) f = false ->
lookup_hdr (eval_transformer_concrete t1 (eval_sym_state s f)) h <>
lookup_hdr (eval_transformer_concrete t2 (eval_sym_state s f)) h.
Proof.
  intros t1 t2 s h f.
  intro H1.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite commute_sym_vs_conc_transfomer_hdr.
  rewrite commute_sym_vs_conc_transfomer_hdr.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_hdr.
  rewrite commute_mapper_lookup_hdr.
  apply H.
  assumption. assumption.
Qed.

Lemma eval_smt_bool_lemma_state_false :
  forall t1 t2 s sv f,
  is_state_var_in_ps s sv <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_state (eval_transformer_smt t1 s) sv)
(lookup_state (eval_transformer_smt t2 s) sv)) f = false ->
lookup_state (eval_transformer_concrete t1 (eval_sym_state s f)) sv <>
lookup_state (eval_transformer_concrete t2 (eval_sym_state s f)) sv.
Proof.
  intros t1 t2 s sv f.
  intro H1.
  intro H.
  apply smt_bool_eq_false in H.
  rewrite commute_sym_vs_conc_transfomer_sv.
  rewrite commute_sym_vs_conc_transfomer_sv.
  unfold eval_sym_state.
  rewrite commute_mapper_lookup_state.
  rewrite commute_mapper_lookup_state.
  apply H.
  assumption. assumption.
Qed.

Definition equivalence_checker
  (s : SymbolicState)
  (t1 : Transformer) (t2 : Transformer)
  (header_list : list Header) (state_var_list : list State)
   :  SmtResult :=
  (* assume a starting symbolic state s*)
  (* convert t1 and t2 to an equivalent final SmtArithExpr, assuming a start state of s *)
  let s1 := eval_transformer_smt t1 s in
  let s2 := eval_transformer_smt t2 s in
  (* check if the headers and state vars are equivalent *)
  smt_query (check_headers_and_state_vars s1 s2 header_list state_var_list).

Definition equivalence_checker_cr_dsl (p1: CaracaraProgram) (p2: CaracaraProgram)
  : option SmtValuation := 
  match p1, p2 with
   | CaracaraProgramDef h1 s1 c1 t1, CaracaraProgramDef h2 s2 c2 t2 => 
      if hdr_list_equal h1 h2 then
        if state_list_equal s1 s2 then
          if ctrl_list_equal c1 c2 then
            match (equivalence_checker (init_symbolic_state p1) t1 t2 h1 s1) with
            (* TODO: Maybe equivalence_checker should take c as argument too? *)
            | SmtUnsat => None  (* if it is unsatisfiable, then all state vars and headers are equal *)
            | SmtSat f => Some f (* if it is satisfiable, then some state var or header is not equal *)
            | SmtUnknown => Some (fun _ => one) (* TODO: This is a hack *)
            end
          else
            Some (fun _ => one) (* TODO: This is a hack *)
        else
          Some (fun _ => one) (* TODO: This is a hack *)
      else
        Some (fun _ => one) (* TODO: This is a hack *)
  end.

(* Soundness lemma about equivalence_checker conditional on the axioms above *)
(* TODO: Joe said both equivalence checker lemmas should be named soundness lemmas,
         rather than completness. Resolve this item.*)
Lemma equivalence_checker_sound :
  forall s t1 t2 header_list state_var_list f,
  (forall v, In v header_list -> is_header_in_ps s v <> None) ->
  (forall v, In v state_var_list -> is_state_var_in_ps s v <> None) ->
  equivalence_checker s t1 t2 header_list state_var_list = SmtUnsat ->
  let c  := eval_sym_state s f in
  let c1 := eval_transformer_concrete t1 c in
  let c2 := eval_transformer_concrete t2 c in
  (forall v, In v header_list ->
  (lookup_hdr c1 v) = (lookup_hdr c2 v)) /\
  (forall v, In v state_var_list ->
  (lookup_state c1 v) = (lookup_state c2 v)).
Proof.
  intros s t1 t2 header_list state_var_list f.
  intro H1.
  intro H2.
  intro H.
  simpl.
  unfold equivalence_checker in H.
  split; intro h; intro H_in.
  -- specialize (smt_query_sound_none _ H f) as H_complete.
     apply check_headers_and_state_vars_false in H_complete.
     destruct H_complete as [H_header H_state_var].
     clear H_state_var. (* declutter *)
     specialize (H_header h H_in).
     apply eval_smt_bool_lemma_hdr.
     specialize (H1 h H_in). assumption. assumption.
  -- specialize (smt_query_sound_none _ H f) as H_complete.
     apply check_headers_and_state_vars_false in H_complete.
     destruct H_complete as [H_header H_state_var].
     clear H_header. (* declutter *)
     specialize (H_state_var h H_in).
     apply eval_smt_bool_lemma_state.
     specialize (H2 h H_in). assumption. assumption.
Qed.

Print Assumptions equivalence_checker_sound.

(* Completeness lemma about equivalence_checker conditional on the axioms above *)
Lemma equivalence_checker_complete :
  forall s t1 t2 header_list state_var_list f',
  (forall v, In v header_list -> is_header_in_ps s v <> None) ->
  (forall v, In v state_var_list -> is_state_var_in_ps s v <> None) ->
  equivalence_checker s t1 t2 header_list state_var_list = SmtSat f' ->
  let c' := eval_sym_state s f' in
  let c1 := eval_transformer_concrete t1 c' in
  let c2 := eval_transformer_concrete t2 c' in
  (exists v, In v header_list /\
  (lookup_hdr c1 v) <> (lookup_hdr c2 v)) \/
  (exists v, In v state_var_list /\
  (lookup_state c1 v) <> (lookup_state c2 v)).
Proof.
  intros s t1 t2 header_list state_var_list f'.
  intro Hh.
  intro Hsv.
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
       specialize (Hh h H).
       pose proof (eval_smt_bool_lemma_hdr_false t1 t2 s h f Hh H0) as H_neq.
       left.
       exists h.
       split; assumption.
    -- destruct H_state_var as [sv Hw].
       destruct Hw.
       specialize (Hsv sv H).
       pose proof (eval_smt_bool_lemma_state_false t1 t2 s sv f Hsv H0) as H_neq.
       right.
       exists sv.
       split; assumption.
  - discriminate H.
  - discriminate H.
Qed.

Lemma ptree_of_list_lemma_hdr :
    forall (l : list Header) (val_fn : Header -> SmtArithExpr) (h: Header),
    Coqlib.list_norepet l ->
    In h l ->
    In h (map (fun '(key, _) => HeaderCtr key)    
     (PTree.elements (PTree_Properties.of_list (combine (map (fun h => match h with | HeaderCtr x => x end) l) (map val_fn l))))).
Proof.
  intros l val_fn h H' H. (* apply in_map with (f := fun pos => (pos, key_fn) in H. *)
  generalize H as H_in.
  apply helper1 with (key_fn := (fun h => match h with | HeaderCtr x => x end)) (val_fn := val_fn) in H.
  intros.
  destruct h.
  remember (fun '(key, _) => HeaderCtr key) as f.
  assert(H_tmp: HeaderCtr uid =
         f (uid, val_fn (HeaderCtr uid))).
  { rewrite Heqf. reflexivity. }
  rewrite H_tmp.
  apply in_map with (f := f) (x := (uid, val_fn (HeaderCtr uid))) (l := (PTree.elements
  (PTree_Properties.of_list (combine (map (fun h => match h with | HeaderCtr x => x end) l) (map val_fn l))))).
  remember (uid, val_fn (HeaderCtr uid)) as pair_val.
  remember (combine (map (fun h : Header => match h with
    | HeaderCtr x => x
  end) l) (map val_fn l)) as l_combined.
  rewrite Heqpair_val in *.
  apply PTree.elements_correct with (m := PTree_Properties.of_list l_combined).
  apply PTree_Properties.of_list_norepet.
  - rewrite Heql_combined.
    simpl.
    rewrite map_combine2.
    apply Coqlib.list_map_norepet.
    -- assumption.
    -- intros.
       destruct x.
       destruct y.
       intro H_contra.
       apply H2.
       f_equal.
       assumption.
  - assumption.
Qed.

(* Same as ptree_of_list_lemma_hdr, but for state *)
Lemma ptree_of_list_lemma_state :
  forall (l : list State) (val_fn : State -> SmtArithExpr) (sv: State),
  Coqlib.list_norepet l ->
  In sv l ->
  In sv (map (fun '(key, _) => StateCtr key)    
   (PTree.elements (PTree_Properties.of_list (combine (map (fun sv => match sv with | StateCtr x => x end) l) (map val_fn l))))).
Proof.
  intros l val_fn sv H' H. (* apply in_map with (f := fun pos => (pos, key_fn) in H. *)
  generalize H as H_in.
  apply helper1_state with (key_fn := (fun sv => match sv with | StateCtr x => x end)) (val_fn := val_fn) in H.
  intros.
  destruct sv.
  remember (fun '(key, _) => StateCtr key) as f.
  assert(H_tmp: StateCtr uid =
     f (uid, val_fn (StateCtr uid))).
  { rewrite Heqf. reflexivity. }
  rewrite H_tmp.
  apply in_map with (f := f) (x := (uid, val_fn (StateCtr uid))) (l := (PTree.elements
  (PTree_Properties.of_list (combine (map (fun sv : State => match sv with
  | StateCtr x => x
  end) l) (map val_fn l))))).
  remember (uid, val_fn (StateCtr uid)) as pair_val.
  remember (combine (map (fun sv : State => match sv with | StateCtr x => x end) l) (map val_fn l)) as l_combined.
  rewrite Heqpair_val in *.
  apply PTree.elements_correct with (m := PTree_Properties.of_list l_combined).
  apply PTree_Properties.of_list_norepet.
  - rewrite Heql_combined.
  simpl.
  rewrite map_combine2.
  apply Coqlib.list_map_norepet.
  -- assumption.
  -- intros.
     destruct x.
     destruct y.
     intro H_contra.
     apply H2.
     f_equal.
     assumption.
  - assumption.
Qed.

Lemma init_symbolic_state_nodep_t : forall h s c t1 t2,
  init_symbolic_state (CaracaraProgramDef h s c t1) =
  init_symbolic_state (CaracaraProgramDef h s c t2).
Proof.
  intros h s c t1 t2.
  unfold init_symbolic_state.
  f_equal.
Qed.

(* Soundness lemma for equivalence_checker_cr_dsl *)
Lemma equivalence_checker_cr_sound_hdr :
  forall p1 p2 f,
  equivalence_checker_cr_dsl p1 p2 = None ->
  let c1_i  := eval_sym_state (init_symbolic_state p1) f in (* Get a sym state out of p1' headers, ctrls, and state *)
  let c2_i  := eval_sym_state (init_symbolic_state p2) f in (* Do the same for p2 *)
  let t1 := get_transformer_from_prog p1 in
  let t2 := get_transformer_from_prog p2 in
  let c1 := eval_transformer_concrete t1 c1_i in
  let c2 := eval_transformer_concrete t2 c2_i in
  well_formed_program p1 ->                          (* p1 is well-formed *)
  (forall v, In v (get_headers_from_prog p1) ->      (* then, every header in p1 *)
  (In v (get_headers_from_prog p2)) /\               (* must be in p2 *)
  (lookup_hdr c1 v) = (lookup_hdr c2 v)).            (* and their final values must be equal *)
Proof.
  intros p1 p2 f H.
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
           p2 as [h2 s2 c2 t2] eqn:desp2; simpl in H.
  destruct
  (hdr_list_equal h1 h2) eqn:H_hdr_eq,
  (state_list_equal s1 s2) eqn:H_state_eq,
  (ctrl_list_equal c1 c2) eqn:H_ctrl_eq in H; simpl in H; try (exfalso; congruence).
  intros.
  simpl in H1. (* TODO: May want to remove these *)
  split.
  - apply hdr_list_equal_lemma in H_hdr_eq.
    rewrite H_hdr_eq in H1.
    assumption.
  - destruct (equivalence_checker (init_symbolic_state (CaracaraProgramDef h1 s1 c1
t1)) t1 t2 h1 s1) eqn:H_eq; try (exfalso; congruence).
    apply equivalence_checker_sound with (f := f) in H_eq.
    + apply H_eq in H1.
      unfold c0.
      unfold c3.
      unfold c1_i.
      unfold c2_i.
      simpl.
      unfold t0.
      unfold t3.
      simpl.
      apply state_list_equal_lemma in H_state_eq.
      apply hdr_list_equal_lemma in H_hdr_eq.
      apply ctrl_list_equal_lemma in H_ctrl_eq.
      rewrite <- H_hdr_eq.
      rewrite <- H_state_eq.
      rewrite <- H_ctrl_eq.
      rewrite init_symbolic_state_nodep_t with (t2 := t2) in H1 at 2.
      assumption.
    + intros.
      apply is_header_in_ps_lemma.
      unfold init_symbolic_state.
      Transparent get_all_headers_from_ps.
      unfold get_all_headers_from_ps.
      simpl.
      rewrite map_pair_split.
      simpl.
      apply ptree_of_list_lemma_hdr.
      simpl in H0.
      destruct H0.
      assumption. assumption.
    + intros.
      apply is_state_in_ps_lemma.
      unfold init_symbolic_state.
      Transparent get_all_states_from_ps.
      unfold get_all_states_from_ps.
      simpl.
      rewrite map_pair_split.
      simpl.
      apply ptree_of_list_lemma_state.
      simpl in H0.
      destruct H0.
      destruct H3.
      assumption.
      assumption.
Qed.

(* Prove the same thing as above, but for state instead of headers *)
(* Soundness lemma for equivalence_checker_cr_dsl *)
Lemma equivalence_checker_cr_sound_state :
  forall p1 p2 f,
  equivalence_checker_cr_dsl p1 p2 = None ->
  let c1_i  := eval_sym_state (init_symbolic_state p1) f in (* Get a sym state out of p1' headers, ctrls, and state *)
  let c2_i  := eval_sym_state (init_symbolic_state p2) f in (* Do the same for p2 *)
  let t1 := get_transformer_from_prog p1 in
  let t2 := get_transformer_from_prog p2 in
  let c1 := eval_transformer_concrete t1 c1_i in
  let c2 := eval_transformer_concrete t2 c2_i in
  well_formed_program p1 ->                          (* p1 is well-formed *)
  (forall v, In v (get_states_from_prog p1) ->      (* then, every header in p1 *)
  (In v (get_states_from_prog p2)) /\               (* must be in p2 *)
  (lookup_state c1 v) = (lookup_state c2 v)).            (* and their final values must be equal *)
Proof.
  intros p1 p2 f H.
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
           p2 as [h2 s2 c2 t2] eqn:desp2; simpl in H.
  destruct
  (hdr_list_equal h1 h2) eqn:H_hdr_eq,
  (state_list_equal s1 s2) eqn:H_state_eq,
  (ctrl_list_equal c1 c2) eqn:H_ctrl_eq in H; simpl in H; try (exfalso; congruence).
  intros.
  simpl in H1. (* TODO: May want to remove these *)
  split.
  - apply state_list_equal_lemma in H_state_eq.
    rewrite H_state_eq in H1.
    assumption.
  - destruct (equivalence_checker (init_symbolic_state (CaracaraProgramDef h1 s1 c1
t1)) t1 t2 h1 s1) eqn:H_eq; try (exfalso; congruence).
    apply equivalence_checker_sound with (f := f) in H_eq.
    + apply H_eq in H1.
      unfold c0.
      unfold c3.
      unfold c1_i.
      unfold c2_i.
      simpl.
      unfold t0.
      unfold t3.
      simpl.
      apply state_list_equal_lemma in H_state_eq.
      apply hdr_list_equal_lemma in H_hdr_eq.
      apply ctrl_list_equal_lemma in H_ctrl_eq.
      rewrite <- H_hdr_eq.
      rewrite <- H_state_eq.
      rewrite <- H_ctrl_eq.
      rewrite init_symbolic_state_nodep_t with (t2 := t2) in H1 at 2.
      assumption.
    + intros.
      apply is_header_in_ps_lemma.
      unfold init_symbolic_state.
      Transparent get_all_headers_from_ps.
      unfold get_all_headers_from_ps.
      simpl.
      rewrite map_pair_split.
      simpl.
      apply ptree_of_list_lemma_hdr.
      simpl in H0.
      destruct H0.
      assumption. assumption.
    + intros.
      apply is_state_in_ps_lemma.
      unfold init_symbolic_state.
      Transparent get_all_states_from_ps.
      unfold get_all_states_from_ps.
      simpl.
      rewrite map_pair_split.
      simpl.
      apply ptree_of_list_lemma_state.
      simpl in H0.
      destruct H0.
      destruct H3.
      assumption.
      assumption.
Qed.

(* TODO: lemma for Sean to complete *)
Lemma ctrl_list_not_equal :
  forall c1 c2,
    ctrl_list_equal c1 c2 = false ->
    c1 <> c2.
Admitted.

(* TODO: lemma for Sean to complete *)
Lemma hdr_list_not_equal :
  forall h1 h2,
    hdr_list_equal h1 h2 = false ->
    h1 <> h2.
Admitted.

(* TODO: lemma for Sean to complete *)
Lemma state_list_not_equal :
  forall s1 s2,
    state_list_equal s1 s2 = false ->
    s1 <> s2.
Admitted.

(* TODO: lemma for Sean to complete *)
Lemma equal_program_states_ctrl:
  forall h1 s1 c1 t1 h2 s2 c2 t2,
    init_symbolic_state (CaracaraProgramDef h1 s1 c1 t1) = init_symbolic_state (CaracaraProgramDef h2 s2 c2 t2)
    ->
    c1 = c2.
Admitted.

(* Create two copies of the above lemma, one for state and one for header *)
(* TODO: lemma for Sean to complete *)
Lemma equal_program_states_hdr:
  forall h1 s1 c1 t1 h2 s2 c2 t2,
    init_symbolic_state (CaracaraProgramDef h1 s1 c1 t1) = init_symbolic_state (CaracaraProgramDef h2 s2 c2 t2)
    ->
    h1 = h2.
Admitted.

(* TODO: lemma for Sean to complete *)
Lemma equal_program_states_state:
  forall h1 s1 c1 t1 h2 s2 c2 t2,
    init_symbolic_state (CaracaraProgramDef h1 s1 c1 t1) = init_symbolic_state (CaracaraProgramDef h2 s2 c2 t2)
    ->
    s1 = s2.
Admitted.

(* TODO: lemma for Sean to complete *)
(* Completeness lemma for equivalence_checker_cr_dsl *)
Lemma equivalence_checker_cr_complete :
  forall p1 p2 f,
  equivalence_checker_cr_dsl p1 p2 = Some f ->
  let c1_i  := eval_sym_state (init_symbolic_state p1) f in (* Get a sym state out of p1' headers, ctrls, and state *)
  let c2_i  := eval_sym_state (init_symbolic_state p2) f in (* Do the same for p2 *)
  let t1 := get_transformer_from_prog p1 in
  let t2 := get_transformer_from_prog p2 in
  let c1 := eval_transformer_concrete t1 c1_i in
  let c2 := eval_transformer_concrete t2 c2_i in
  well_formed_program p1 ->                          (* p1 is well-formed *)
  well_formed_program p2 ->                          (* p2 is well-formed *)
  (init_symbolic_state p1 = init_symbolic_state p2) ->  (* both programs have the same initial symbolic state
                                                           , i.e., same headers, ctrls, and states *)
                                                           (* TODO handle case where programs
                                                           are not equivalent bcos headers, ctrls, and states differ *)
  ((exists v, In v (get_headers_from_prog p1) /\      (* then, there exists a header in p1 *)
  (lookup_hdr c1 v) <> (lookup_hdr c2 v)) \/          (* whose final values are not equal *)
  (exists v, In v (get_states_from_prog p1) /\        (* or there exists a state var in p1 *)
  (lookup_state c1 v) <> (lookup_state c2 v))).       (* whose final values are not equal *)
Proof.
  intros p1 p2 f H.
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
           p2 as [h2 s2 c2 t2] eqn:desp2; simpl in H.
  destruct
  (hdr_list_equal h1 h2) eqn:H_hdr_eq,
  (state_list_equal s1 s2) eqn:H_state_eq,
  (ctrl_list_equal c1 c2) eqn:H_ctrl_eq in H; simpl in H.
  - destruct (equivalence_checker (init_symbolic_state (CaracaraProgramDef h1 s1 c1
t1)) t1 t2 h1 s1) eqn:H_eq; try (exfalso; congruence).
    -- simpl.
       intros.
       apply equivalence_checker_complete
        with (f' := f0)
             (s := init_symbolic_state (CaracaraProgramDef h1 s1 c1 t1)) 
             (header_list := h1) (state_var_list := s1) in H_eq.
       ++ simpl.
          injection H as Heq.
          subst f0.
          apply hdr_list_equal_lemma in H_hdr_eq.
          rewrite <- H_hdr_eq.
          apply state_list_equal_lemma in H_state_eq.
          rewrite <- H_state_eq.
          apply ctrl_list_equal_lemma in H_ctrl_eq.
          rewrite <- H_ctrl_eq.
          apply H_eq.
       ++ intros.
          apply is_header_in_ps_lemma.
          unfold get_all_headers_from_ps.
          simpl.
          rewrite map_pair_split.
          apply ptree_of_list_lemma_hdr.
          destruct H0 as [H_wf_headers _].
          apply H_wf_headers.
          assumption.
       ++ intros.
          apply is_state_in_ps_lemma.
          unfold get_all_states_from_ps.
          simpl.
          rewrite map_pair_split.
          apply ptree_of_list_lemma_state.
          destruct H0 as [H_wf_headers H_wf_states].
          destruct H_wf_states as [H_wf_states _].
          apply H_wf_states.
          assumption.
    -- admit. (* equivalence_checker returns SmtUnknown,
                 TODO: need to come back to this *)
  (* Sean TODO: Capture the remaining 7 cases below into one lemma with hopefully less repetition *)
  -   intros.
      apply ctrl_list_not_equal in H_ctrl_eq.
      apply equal_program_states_ctrl in H2.
      rewrite H2 in H_ctrl_eq.
      contradiction.
  -   intros.
      apply state_list_not_equal in H_state_eq.
      apply equal_program_states_state in H2.
      rewrite H2 in H_state_eq.
      contradiction.
  -   intros.
      apply state_list_not_equal in H_state_eq.
      apply equal_program_states_state in H2.
      rewrite H2 in H_state_eq.
      contradiction.
  -   intros.
      apply hdr_list_not_equal in H_hdr_eq.
      apply equal_program_states_hdr in H2.
      rewrite H2 in H_hdr_eq.
      contradiction.
  -   intros.
      apply hdr_list_not_equal in H_hdr_eq.
      apply equal_program_states_hdr in H2.
      rewrite H2 in H_hdr_eq.
      contradiction.
  -   intros.
      apply hdr_list_not_equal in H_hdr_eq.
      apply equal_program_states_hdr in H2.
      rewrite H2 in H_hdr_eq.
      contradiction.
  -   intros.
      apply hdr_list_not_equal in H_hdr_eq.
      apply equal_program_states_hdr in H2.
      rewrite H2 in H_hdr_eq.
      contradiction.
Admitted.
    
Print Assumptions equivalence_checker_complete.
Print Assumptions equivalence_checker_cr_sound_hdr.
Print Assumptions equivalence_checker_cr_sound_state.
Print Assumptions equivalence_checker_cr_complete.
