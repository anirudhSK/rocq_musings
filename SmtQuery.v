From MyProject Require Import SmtExpr.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrModule.
From MyProject Require Import Maps.
From MyProject Require Import SmtTypes.
From MyProject Require Import Integers.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import CrVal.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import micromega.Lia.
Import ListNotations.

(* Import or define SeqRule and related types *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrTModSymbolicSemantics.
From MyProject Require Import CrTModConcreteSemantics.
From MyProject Require Import ConcreteToSymbolicLemmas.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import UtilLemmas.
From MyProject Require Import HelperLemmas.
From MyProject Require Import ListUtils.
From MyProject Require Import ConcreteTransformerLemmas.

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
  SmtBoolAnd (List.fold_right (fun h acc => SmtBoolAnd acc (SmtBoolEq (lookup_varlike s1 h) (lookup_varlike s2 h))) 
                                    SmtTrue header_list)
             (List.fold_right (fun sv acc => SmtBoolAnd acc (SmtBoolEq (lookup_varlike s1 sv) (lookup_varlike s2 sv))) 
                                    SmtTrue state_var_list)).

Lemma check_headers_and_state_vars_false:
  forall s1 s2 header_list state_var_list f,
  eval_smt_bool(check_headers_and_state_vars s1 s2 header_list state_var_list) f = false ->
  (forall h, In h header_list -> eval_smt_bool (SmtBoolEq (lookup_varlike s1 h) (lookup_varlike s2 h)) f = true) /\
  (forall sv, In sv state_var_list -> eval_smt_bool (SmtBoolEq (lookup_varlike s1 sv) (lookup_varlike s2 sv)) f = true).
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
                      eval_smt_bool (SmtBoolEq (lookup_varlike s1 h) (lookup_varlike s2 h)) f = false) \/
  (exists sv :State, In sv state_var_list /\
                      eval_smt_bool (SmtBoolEq (lookup_varlike s1 sv) (lookup_varlike s2 sv)) f = false).
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

Ltac prove_eval_smt_bool_lemma smt_bool_lemma commute_lemma:=
  intros t1 t2 s h f H H_eq;
  apply smt_bool_lemma in H_eq;
  rewrite (commute_lemma t1 f s h H);
  rewrite (commute_lemma t2 f s h H);
  unfold eval_sym_state;
  repeat rewrite commute_lookup_varlike;
  apply H_eq.

Lemma eval_smt_bool_lemma_hdr :
  forall t1 t2 s (h : Header) f,
  is_varlike_in_ps s h <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_varlike (eval_transformer_smt t1 s) h)
(lookup_varlike (eval_transformer_smt t2 s) h)) f = true ->
lookup_varlike (eval_transformer_concrete t1 (eval_sym_state s f)) h =
lookup_varlike (eval_transformer_concrete t2 (eval_sym_state s f)) h.
Proof.
  prove_eval_smt_bool_lemma smt_bool_eq_true commute_sym_vs_conc_transfomer_hdr.
Qed.

Lemma eval_smt_bool_lemma_state :
  forall t1 t2 s (sv : State) f,
  is_varlike_in_ps s sv <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_varlike (eval_transformer_smt t1 s) sv)
(lookup_varlike (eval_transformer_smt t2 s) sv)) f = true ->
lookup_varlike (eval_transformer_concrete t1 (eval_sym_state s f)) sv =
lookup_varlike (eval_transformer_concrete t2 (eval_sym_state s f)) sv.
Proof.
  prove_eval_smt_bool_lemma smt_bool_eq_true commute_sym_vs_conc_transfomer_sv.
Qed.

Lemma eval_smt_bool_lemma_hdr_false :
  forall t1 t2 s (h : Header) f,
  is_varlike_in_ps s h <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_varlike (eval_transformer_smt t1 s) h)
(lookup_varlike (eval_transformer_smt t2 s) h)) f = false ->
lookup_varlike (eval_transformer_concrete t1 (eval_sym_state s f)) h <>
lookup_varlike (eval_transformer_concrete t2 (eval_sym_state s f)) h.
Proof.
  prove_eval_smt_bool_lemma smt_bool_eq_false commute_sym_vs_conc_transfomer_hdr.
Qed.

Lemma eval_smt_bool_lemma_state_false :
  forall t1 t2 s (sv : State) f,
  is_varlike_in_ps s sv <> None ->
  eval_smt_bool
(SmtBoolEq (lookup_varlike (eval_transformer_smt t1 s) sv)
(lookup_varlike (eval_transformer_smt t2 s) sv)) f = false ->
lookup_varlike (eval_transformer_concrete t1 (eval_sym_state s f)) sv <>
lookup_varlike (eval_transformer_concrete t2 (eval_sym_state s f)) sv.
Proof.
  prove_eval_smt_bool_lemma smt_bool_eq_false commute_sym_vs_conc_transfomer_sv.
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

(* An inductive data type called EquivalenceResult *)
Inductive EquivalenceResult :=
  | Equivalent
  | NotEquivalent (witness: SmtValuation)
  | NotEquivalentUnknown
  | NotEquivalentVariablesDiffer.

Definition equivalence_checker_cr_dsl (p1: CaracaraProgram) (p2: CaracaraProgram)
  : EquivalenceResult := 
  match p1, p2 with
   | CaracaraProgramDef h1 s1 c1 t1, CaracaraProgramDef h2 s2 c2 t2 => 
      if varlike_list_equal h1 h2 then
        if varlike_list_equal s1 s2 then
          if varlike_list_equal c1 c2 then
            match (equivalence_checker (init_symbolic_state p1) t1 t2 h1 s1) with
            (* TODO: Maybe equivalence_checker should take c as argument too? *)
            | SmtUnsat => Equivalent (* if it is unsatisfiable, then all state vars and headers are equal *)
            | SmtSat f => NotEquivalent f (* if it is satisfiable, then some state var or header is not equal *)
            | SmtUnknown => NotEquivalentUnknown
            end
          else
            NotEquivalentVariablesDiffer
        else
          NotEquivalentVariablesDiffer
      else
        NotEquivalentVariablesDiffer
  end.

(* Soundness lemma about equivalence_checker conditional on the axioms above *)
(* TODO: Joe said both equivalence checker lemmas should be named soundness lemmas,
         rather than completness. Resolve this item.*)
Lemma equivalence_checker_sound :
  forall s t1 t2 header_list state_var_list f,
  (forall v, In v header_list -> is_varlike_in_ps s v <> None) ->
  (forall v, In v state_var_list -> is_varlike_in_ps s v <> None) ->
  equivalence_checker s t1 t2 header_list state_var_list = SmtUnsat ->
  let c  := eval_sym_state s f in
  let c1 := eval_transformer_concrete t1 c in
  let c2 := eval_transformer_concrete t2 c in
  (forall v, In v header_list ->
  (lookup_varlike c1 v) = (lookup_varlike c2 v)) /\
  (forall v, In v state_var_list ->
  (lookup_varlike c1 v) = (lookup_varlike c2 v)).
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
  (forall v, In v header_list -> is_varlike_in_ps s v <> None) ->
  (forall v, In v state_var_list -> is_varlike_in_ps s v <> None) ->
  equivalence_checker s t1 t2 header_list state_var_list = SmtSat f' ->
  let c' := eval_sym_state s f' in
  let c1 := eval_transformer_concrete t1 c' in
  let c2 := eval_transformer_concrete t2 c' in
  (exists v, In v header_list /\
  (lookup_varlike c1 v) <> (lookup_varlike c2 v)) \/
  (exists v, In v state_var_list /\
  (lookup_varlike c1 v) <> (lookup_varlike c2 v)).
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

Lemma init_symbolic_state_nodep_t : forall h s c t1 t2,
  init_symbolic_state (CaracaraProgramDef h s c t1) =
  init_symbolic_state (CaracaraProgramDef h s c t2).
Proof.
  intros h s c t1 t2.
  unfold init_symbolic_state.
  f_equal.
Qed.

Class CrVarProg A := {
  get_vars_from_prog : CaracaraProgram -> list A;
  lookup_var : ConcreteState -> A -> CrVal;
  get_vars_invariant_of_transformer:
    forall h s c t1 t2,
    get_vars_from_prog (CaracaraProgramDef h s c t1) =
    get_vars_from_prog (CaracaraProgramDef h s c t2);
  equivalence_checker_cr_sound :
    forall p1 p2 f,
    well_formed_program p1 ->                          (* p1 is well-formed *)
    equivalence_checker_cr_dsl p1 p2 = Equivalent ->
    let c1_i  := eval_sym_state (init_symbolic_state p1) f in (* Get a sym state out of p1 *)
    let c2_i  := eval_sym_state (init_symbolic_state p2) f in (* Do the same for p2 *)
    let t1 := get_transformer_from_prog p1 in
    let t2 := get_transformer_from_prog p2 in
    let c1 := eval_transformer_concrete t1 c1_i in
    let c2 := eval_transformer_concrete t2 c2_i in
    forall var, In var (get_vars_from_prog p1) ->      (* then, every var in p1 *)
    (In var (get_vars_from_prog p2)) /\                (* must be in p2 *)
    (lookup_var c1 var) = (lookup_var c2 var);         (* and their final values must be equal *)
}.

Ltac prove_in_var_list_implies_in_prog_state hypothesis type crvar_type :=
  intros;
  apply is_varlike_in_ps_lemma;
  unfold init_symbolic_state;
  unfold get_all_varlike_from_ps;
  simpl;
  repeat rewrite map_pair_split;
  simpl;
  apply (@ptree_of_list_lemma_generic type crvar_type);
  simpl in hypothesis;
  destruct hypothesis as [Hwf H3];
  destruct H3;
  assumption; assumption.

Ltac prove_equivalence_checker_cr_sound :=
  intros p1 p2 f Hwf H;
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
            p2 as [h2 s2 c2 t2] eqn:desp2; simpl in H;
  destruct
  (varlike_list_equal h1 h2) eqn:H_hdr_eq,
  (varlike_list_equal s1 s2) eqn:H_state_eq,
  (varlike_list_equal c1 c2) eqn:H_ctrl_eq in H; simpl in H; try (exfalso; congruence);
  apply varlike_list_equal_lemma in H_state_eq;
  apply varlike_list_equal_lemma in H_hdr_eq;
  apply varlike_list_equal_lemma in H_ctrl_eq;
  intros c1_i c2_i t0 t3 c0 c3 var H1;
  simpl in H1;
  split;
  try (rewrite H_hdr_eq in H1; assumption); try (rewrite H_state_eq in H1; assumption);
  destruct (equivalence_checker (init_symbolic_state (CaracaraProgramDef h1 s1 c1 t1)) t1 t2 h1 s1) eqn:H_eq; try (exfalso; congruence);
  apply equivalence_checker_sound with (f := f) in H_eq;
  try(apply H_eq in H1;
      unfold c0, c3, c1_i, c2_i, t0, t3;
      simpl;
      rewrite <- H_hdr_eq;
      rewrite <- H_state_eq;
      rewrite <- H_ctrl_eq;
      rewrite init_symbolic_state_nodep_t with (t2 := t2) in H1 at 2;
      assumption);
  try(prove_in_var_list_implies_in_prog_state Hwf Header CrVarLike_Header);
  try(prove_in_var_list_implies_in_prog_state Hwf State CrVarLike_State).

Transparent get_all_varlike_from_ps.
Instance CrVarProg_Header : CrVarProg Header.
Proof.
  refine {| get_vars_from_prog := get_headers_from_prog;
            lookup_var := fun s h => lookup_varlike s h; |}.
  - intros. simpl. reflexivity.
  - prove_equivalence_checker_cr_sound.
Defined.

Instance CrVarProg_State : CrVarProg State.
Proof.
  refine {| get_vars_from_prog := get_states_from_prog;
            lookup_var := fun s sv => lookup_varlike s sv; |}.
  - intros. simpl. reflexivity.
  - prove_equivalence_checker_cr_sound.
Defined.

Instance CrVarProg_Ctrl : CrVarProg Ctrl.
Proof.
  refine {| get_vars_from_prog := get_ctrls_from_prog;
            lookup_var := fun s c => lookup_varlike s c; |}.
  - intros. simpl. reflexivity.
  - prove_equivalence_checker_cr_sound. admit.
Admitted.

Transparent map_from_ps.
(* Completeness lemma for equivalence_checker_cr_dsl *)
Lemma equivalence_checker_cr_complete :
  forall p1 p2 f,
  well_formed_program p1 ->                          (* p1 is well-formed *)
  well_formed_program p2 ->                          (* p2 is well-formed *)
  equivalence_checker_cr_dsl p1 p2 = NotEquivalent f ->
  let c1_i  := eval_sym_state (init_symbolic_state p1) f in (* Get a sym state out of p1' headers, ctrls, and state *)
  let c2_i  := eval_sym_state (init_symbolic_state p2) f in (* Do the same for p2 *)
  let t1 := get_transformer_from_prog p1 in
  let t2 := get_transformer_from_prog p2 in
  let c1 := eval_transformer_concrete t1 c1_i in
  let c2 := eval_transformer_concrete t2 c2_i in
  (init_symbolic_state p1 = init_symbolic_state p2) ->  (* both programs have the same initial symbolic state
                                                           , i.e., same headers, ctrls, and states *)
                                                           (* TODO handle case where programs
                                                           are not equivalent bcos headers, ctrls, and states differ *)
  ((exists v, In v (get_headers_from_prog p1) /\      (* then, there exists a header in p1 *)
  (lookup_varlike c1 v) <> (lookup_varlike c2 v)) \/          (* whose final values are not equal *)
  (exists v, In v (get_states_from_prog p1) /\        (* or there exists a state var in p1 *)
  (lookup_varlike c1 v) <> (lookup_varlike c2 v))).       (* whose final values are not equal *)
Proof.
  intros p1 p2 f Hwf1 Hwf2 H.
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
           p2 as [h2 s2 c2 t2] eqn:desp2; simpl in H.
  destruct
  (varlike_list_equal h1 h2) eqn:H_hdr_eq,
  (varlike_list_equal s1 s2) eqn:H_state_eq,
  (varlike_list_equal c1 c2) eqn:H_ctrl_eq in H; simpl in H.
  2-8: discriminate H. (* The easy goals, where state, ctrl, or header lists are NOT equal, proof by explosion because we assume these lists ARE equal*)
  - destruct (equivalence_checker (init_symbolic_state (CaracaraProgramDef h1 s1 c1 (* The hard goal *)
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
          apply varlike_list_equal_lemma in H_hdr_eq.
          rewrite <- H_hdr_eq.
          apply varlike_list_equal_lemma in H_state_eq.
          rewrite <- H_state_eq.
          apply varlike_list_equal_lemma in H_ctrl_eq.
          rewrite <- H_ctrl_eq.
          apply H_eq.
       ++ intros.
          apply is_varlike_in_ps_lemma.
          unfold get_all_varlike_from_ps.
          unfold map_from_ps.
          simpl.
          rewrite map_pair_split.
          apply (@ptree_of_list_lemma_generic Header CrVarLike_Header).
          destruct Hwf1 as [H_wf_headers _].
          apply H_wf_headers.
          assumption.
       ++ intros.
          apply is_varlike_in_ps_lemma.
          unfold get_all_varlike_from_ps.
          unfold map_from_ps.
          simpl.
          rewrite map_pair_split.
          apply (@ptree_of_list_lemma_generic State CrVarLike_State).
          destruct Hwf1 as [H_wf_headers H_wf_states].
          destruct H_wf_states as [H_wf_states _].
          apply H_wf_states.
          assumption.
Qed.
Global Opaque map_from_ps.
Global Opaque get_all_varlike_from_ps.

Print Assumptions equivalence_checker_cr_sound.
Print Assumptions equivalence_checker_cr_complete.

Definition value_is_valid (v : CrVal) : Prop :=
  match v with
  | IntVal CrNilInt => True
  | IntVal (CrInt _) => True
  | _ => False
  end.

Definition map_is_valid (m : PMap.t CrVal) : Prop :=
  (fst m = IntVal CrNilInt) /\ (forall k, value_is_valid (m !! k)).

(* A concrete state cs is valid relative to a program p when:
   - each PMap has (IntVal CrNilInt) as its default,
   - every value in cs is either (IntVal CrNilInt) or a uint8, and
   - the initialized variables in cs are exactly the program variables of p. *)
Definition concrete_state_is_valid (p : CaracaraProgram) (cs : ConcreteState) : Prop :=
  map_is_valid (header_map cs) /\
  map_is_valid (state_map cs) /\
  map_is_valid (ctrl_map cs) /\
  (forall v : Header, lookup_varlike cs v <> (IntVal CrNilInt) <-> In v (get_headers_from_prog p)) /\
  (forall v : State,  lookup_varlike cs v <> (IntVal CrNilInt) <-> In v (get_states_from_prog p)) /\
  (forall v : Ctrl,   lookup_varlike cs v <> (IntVal CrNilInt) <-> In v (get_ctrls_from_prog p)).

(* try_match: search for a string match against prefix ++ pos_to_string id in a list. *)
Definition try_match_prefix
  (prefix : string) (l : list (positive * CrVal)) (name : string) : option CrVal :=
  fold_right (fun (p : positive * CrVal) acc =>
    let '(id, v) := p in
    if string_dec name (prefix ++ pos_to_string id)%string then Some v else acc
  ) None l.

Lemma try_match_prefix_found :
  forall prefix l id w,
    Coqlib.list_norepet (List.map fst l) ->
    In (id, w) l ->
    try_match_prefix prefix l (prefix ++ pos_to_string id)%string = Some w.
Proof.
  intros prefix l id w Hno Hin.
  induction l as [| [id' w'] rest IH].
  - simpl in Hin. contradiction.
  - simpl in Hno. inversion Hno; subst.
    simpl. simpl in Hin. destruct Hin as [Heq | Hin].
    + inversion Heq; subst. destruct (string_dec _ _); congruence.
    + destruct (string_dec (prefix ++ pos_to_string id)%string
                            (prefix ++ pos_to_string id')%string) as [Heqs | Hneqs].
      * (* id <> id' (since list_norepet), but strings are equal: contradiction *)
        exfalso.
        (* Cancel prefix from the left *)
        assert (Hpos : pos_to_string id = pos_to_string id').
        { clear -Heqs. revert Heqs.
          induction prefix as [| c pr IHpr]; simpl; intros HH.
          - exact HH.
          - injection HH as Hrest. apply IHpr. exact Hrest. }
        apply pos_to_string_inj in Hpos. subst id'.
        apply H1. apply in_map_iff. exists (id, w). split; auto.
      * apply IH; auto.
Qed.

Lemma try_match_prefix_not_found_diff_char :
  forall (c1 c2 : Ascii.ascii) (rest1 rest2 : string) l,
    c1 <> c2 ->
    try_match_prefix (String c1 rest1) l (String c2 rest2)%string = None.
Proof.
  intros c1 c2 rest1 rest2 l Hneq.
  induction l as [| [id v] rest IH].
  - reflexivity.
  - cbn [try_match_prefix fold_right].
    destruct (string_dec (String c2 rest2) (String c1 rest1 ++ pos_to_string id)%string) as [Heq | _].
    + exfalso. cbn in Heq. inversion Heq. apply Hneq. symmetry. assumption.
    + exact IH.
Qed.

Definition build_valuation_for_cs (cs : ConcreteState) : SmtValuation :=
  fun name =>
    match try_match_prefix "hdr_" (PTree.elements (snd (header_map cs))) name with
    | Some v => v
    | None =>
      match try_match_prefix "state_" (PTree.elements (snd (state_map cs))) name with
      | Some v => v
      | None =>
        match try_match_prefix "ctrl_" (PTree.elements (snd (ctrl_map cs))) name with
        | Some v => v
        | None => IntVal (CrInt (repr 0))
        end
      end
    end.

Local Ltac uint8_finalize valid_lemma id_var :=
  pose proof (valid_lemma id_var) as Hvv;
  unfold value_is_valid in Hvv;
  match goal with
  | |- context [PMap.get ?i ?m] =>
      destruct (PMap.get i m) as [i'| | |] eqn:Hpm; try contradiction;
      destruct i'; try contradiction; reflexivity
  end.
Lemma valid_states_realizable :
  (* for all concrete states *)
  forall p cs,
  (* where p is well-formed *)
  well_formed_program p ->
  (* and cs is valid for p (initialized vars are exactly p's program vars) *)
  concrete_state_is_valid p cs ->
  (* there is a valuation f under which init_symbolic_state p concretizes
     to a state that agrees with cs at every variable *)
  exists f,
  let c := eval_sym_state (init_symbolic_state p) f in
  (forall (v : Header), lookup_varlike c v = lookup_varlike cs v) /\
  (forall (v : State),  lookup_varlike c v = lookup_varlike cs v) /\
  (forall (v : Ctrl),   lookup_varlike c v = lookup_varlike cs v).
Proof.
  intros p cs Hwf Hvalid.
  destruct p as [hp sp cp tp].
  simpl in Hwf.
  destruct Hwf as [Hwf_h [Hwf_s [Hwf_c _]]].
  destruct Hvalid as [Hh [Hs [Hc [Hh_in [Hs_in Hc_in]]]]].
  simpl in Hh_in, Hs_in, Hc_in.
  destruct Hh as [Hh_def Hh_valid].
  destruct Hs as [Hs_def Hs_valid].
  destruct Hc as [Hc_def Hc_valid].
  exists (build_valuation_for_cs cs).
  simpl.
  rewrite (init_symbolic_state_nodep_t hp sp cp tp []).
  split; [| split].
  - (* Headers *)
    intros [id].
    rewrite commute_lookup_eval_varlike.
    rewrite lookup_varlike_header_PMap.
    rewrite lookup_varlike_header_PMap_concrete.
    destruct (List.in_dec posesque_eq_dec (HeaderCtr id) hp) as [Hin | Hnin].
    + (* In p's list: cs is initialized at id, agrees with f *)
      assert (Hneq : PMap.get id (header_map cs) <> IntVal CrNilInt).
      { apply (proj2 (Hh_in (HeaderCtr id))). assumption. }
      assert (Htree : (snd (header_map cs)) ! id = Some (PMap.get id (header_map cs))).
      { eapply cs_initialized_in_tree_header; eauto. }
      rewrite init_sym_header_lookup with (id := id).
      3: { assumption. }
      2: { apply list_norepet_header_inner. assumption. }
      simpl.
      unfold build_valuation_for_cs.
      rewrite try_match_prefix_found
        with (id := id) (w := PMap.get id (header_map cs)).
      * uint8_finalize Hh_valid id.
      * apply PTree.elements_keys_norepet.
      * apply PTree.elements_correct. assumption.
    + (* Not in p's list: both sides equal IntVal CrNilInt *)
      rewrite (init_sym_header_lookup_default (CaracaraProgramDef hp sp cp []) id).
      2: { simpl. assumption. }
      simpl.
      pose proof (Hh_in (HeaderCtr id)) as Hiff.
      rewrite lookup_varlike_header_PMap_concrete in Hiff.
      pose proof (Hh_valid id) as Hvv. unfold value_is_valid, PMap.get in *.
      destruct ((snd (header_map cs)) ! id) as [w|] eqn:Htree.
      * destruct w as [i| | |]; try contradiction.
        destruct i; try contradiction.
        -- exfalso. apply Hnin. apply (proj1 Hiff). discriminate.
        -- reflexivity.
      * symmetry. exact Hh_def.
  - (* States *)
    intros [id].
    rewrite commute_lookup_eval_varlike.
    rewrite lookup_varlike_state_PMap.
    rewrite lookup_varlike_state_PMap_concrete.
    destruct (List.in_dec posesque_eq_dec (StateCtr id) sp) as [Hin | Hnin].
    + assert (Hneq : PMap.get id (state_map cs) <> IntVal CrNilInt).
      { apply (proj2 (Hs_in (StateCtr id))). assumption. }
      assert (Htree : (snd (state_map cs)) ! id = Some (PMap.get id (state_map cs))).
      { eapply cs_initialized_in_tree_state; eauto. }
      rewrite init_sym_state_lookup with (id := id).
      3: { assumption. }
      2: { apply list_norepet_state_inner. assumption. }
      simpl.
      unfold build_valuation_for_cs.
      rewrite try_match_prefix_not_found_diff_char with (c1 := "h"%char) (c2 := "s"%char).
      2: { intros H; inversion H. }
      rewrite try_match_prefix_found
        with (id := id) (w := PMap.get id (state_map cs)).
      * uint8_finalize Hs_valid id.
      * apply PTree.elements_keys_norepet.
      * apply PTree.elements_correct. assumption.
    + rewrite (init_sym_state_lookup_default (CaracaraProgramDef hp sp cp []) id).
      2: { simpl. assumption. }
      simpl.
      pose proof (Hs_in (StateCtr id)) as Hiff.
      rewrite lookup_varlike_state_PMap_concrete in Hiff.
      pose proof (Hs_valid id) as Hvv. unfold value_is_valid, PMap.get in *.
      destruct ((snd (state_map cs)) ! id) as [w|] eqn:Htree.
      * destruct w as [i| | |]; try contradiction.
        destruct i; try contradiction.
        -- exfalso. apply Hnin. apply (proj1 Hiff). discriminate.
        -- reflexivity.
      * symmetry. exact Hs_def.
  - (* Ctrls *)
    intros [id].
    rewrite commute_lookup_eval_varlike.
    rewrite lookup_varlike_ctrl_PMap.
    rewrite lookup_varlike_ctrl_PMap_concrete.
    destruct (List.in_dec posesque_eq_dec (CtrlCtr id) cp) as [Hin | Hnin].
    + assert (Hneq : PMap.get id (ctrl_map cs) <> IntVal CrNilInt).
      { apply (proj2 (Hc_in (CtrlCtr id))). assumption. }
      assert (Htree : (snd (ctrl_map cs)) ! id = Some (PMap.get id (ctrl_map cs))).
      { eapply cs_initialized_in_tree_ctrl; eauto. }
      rewrite init_sym_ctrl_lookup with (id := id).
      3: { assumption. }
      2: { apply list_norepet_ctrl_inner. assumption. }
      simpl.
      unfold build_valuation_for_cs.
      rewrite try_match_prefix_not_found_diff_char with (c1 := "h"%char) (c2 := "c"%char).
      2: { intros H; inversion H. }
      rewrite try_match_prefix_not_found_diff_char with (c1 := "s"%char) (c2 := "c"%char).
      2: { intros H; inversion H. }
      rewrite try_match_prefix_found
        with (id := id) (w := PMap.get id (ctrl_map cs)).
      * uint8_finalize Hc_valid id.
      * apply PTree.elements_keys_norepet.
      * apply PTree.elements_correct. assumption.
    + rewrite (init_sym_ctrl_lookup_default (CaracaraProgramDef hp sp cp []) id).
      2: { simpl. assumption. }
      simpl.
      pose proof (Hc_in (CtrlCtr id)) as Hiff.
      rewrite lookup_varlike_ctrl_PMap_concrete in Hiff.
      pose proof (Hc_valid id) as Hvv. unfold value_is_valid, PMap.get in *.
      destruct ((snd (ctrl_map cs)) ! id) as [w|] eqn:Htree.
      * destruct w as [i| | |]; try contradiction.
        destruct i; try contradiction.
        -- exfalso. apply Hnin. apply (proj1 Hiff). discriminate.
        -- reflexivity.
      * symmetry. exact Hc_def.
Qed.

Transparent get_all_varlike_from_ps.
Transparent map_from_ps.
Lemma in_program_implies_in_init_sym_header :
  forall p (v : Header),
    well_formed_program p ->
    In v (get_headers_from_prog p) ->
    is_varlike_in_ps (init_symbolic_state p) v <> None.
Proof.
  intros p v Hwf Hin.
  apply is_varlike_in_ps_lemma.
  unfold get_all_varlike_from_ps, map_from_ps.
  destruct p as [h s c t]. simpl in *.
  rewrite map_pair_split.
  apply (@ptree_of_list_lemma_generic Header CrVarLike_Header).
  - destruct Hwf as [Hwfh _]. assumption.
  - assumption.
Qed.

Lemma in_program_implies_in_init_sym_state :
  forall p (v : State),
    well_formed_program p ->
    In v (get_states_from_prog p) ->
    is_varlike_in_ps (init_symbolic_state p) v <> None.
Proof.
  intros p v Hwf Hin.
  apply is_varlike_in_ps_lemma.
  unfold get_all_varlike_from_ps, map_from_ps.
  destruct p as [h s c t]. simpl in *.
  rewrite map_pair_split.
  apply (@ptree_of_list_lemma_generic State CrVarLike_State).
  - destruct Hwf as [_ [Hwfs _]]. assumption.
  - assumption.
Qed.
Global Opaque get_all_varlike_from_ps.
Global Opaque map_from_ps.

Lemma stronger_equivalence_checker_cr_sound :
  forall p1 p2 c_init,
  well_formed_program p1 ->
  well_formed_program p2 ->
  equivalence_checker_cr_dsl p1 p2 = Equivalent ->
  concrete_state_is_valid p1 c_init ->
  let c1_f := eval_transformer_concrete (get_transformer_from_prog p1) c_init in
  let c2_f := eval_transformer_concrete (get_transformer_from_prog p2) c_init in
  (forall v, In v (get_headers_from_prog p1) ->
  (lookup_varlike c1_f v) = (lookup_varlike c2_f v)) /\
  (forall v, In v (get_states_from_prog p1) ->
  (lookup_varlike c1_f v) = (lookup_varlike c2_f v)).
Proof.
  intros p1 p2 c_init Hwf1 Hwf2 Heq' Hvalid1 c1_f c2_f.
  pose proof Hwf1 as Hwf1_orig.
  pose proof (valid_states_realizable p1 c_init Hwf1 Hvalid1) as
    [f [Hvsr1_hdrs [Hvsr1_states Hvsr1_ctrls]]].
  unfold equivalence_checker_cr_dsl in Heq'.
  destruct p1 as [h1 s1 c1 t1] eqn:desp1,
           p2 as [h2 s2 c2 t2] eqn:desp2.
  unfold c1_f, c2_f. simpl.
  rewrite <- desp1 in *. rewrite <- desp2 in *.
  destruct (varlike_list_equal h1 h2),
           (varlike_list_equal s1 s2),
           (varlike_list_equal c1 c2); try congruence.
  destruct (equivalence_checker (init_symbolic_state p1) t1 t2 h1 s1) eqn:Heq; try congruence.
  clear Heq'.
  unfold equivalence_checker in Heq.
  apply smt_query_sound_none with (v' := f) in Heq.
  apply check_headers_and_state_vars_false in Heq.
  destruct Heq as [Hheq Hseq].
  assert (Hbridge : forall (h : Header) (s : State) (c : Ctrl),
    lookup_varlike c_init h = lookup_varlike (eval_sym_state (init_symbolic_state p1) f) h /\
    lookup_varlike c_init s = lookup_varlike (eval_sym_state (init_symbolic_state p1) f) s /\
    lookup_varlike c_init c = lookup_varlike (eval_sym_state (init_symbolic_state p1) f) c).
  { intros h s c. split; [| split].
    - rewrite (Hvsr1_hdrs h). reflexivity.
    - rewrite (Hvsr1_states s). reflexivity.
    - rewrite (Hvsr1_ctrls c). reflexivity. }
  pose proof (transformer_preserves_lookup_equality_lemma t1 _ _ Hbridge) as Hbridge_t1.
  pose proof (transformer_preserves_lookup_equality_lemma t2 _ _ Hbridge) as Hbridge_t2.
  split; intros v Hv.
  - (* Headers case *)
    specialize (Hheq v Hv).
    apply smt_bool_eq_true in Hheq.
    repeat rewrite commute_conc_and_lookup in Hheq.
    assert (Hin_ps : is_varlike_in_ps (init_symbolic_state p1) v <> None).
    { apply in_program_implies_in_init_sym_header with (p := p1).
      - exact Hwf1_orig.
      - rewrite desp1. simpl. exact Hv. }
    rewrite <- commute_sym_vs_conc_transformer_header_map
      with (t := t1) (f := f) (s1 := init_symbolic_state p1) (h := v) in Hheq;
      try assumption.
    rewrite <- commute_sym_vs_conc_transformer_header_map
      with (t := t2) (f := f) (s1 := init_symbolic_state p1) (h := v) in Hheq;
      try assumption.
    specialize (Hbridge_t1 v (StateCtr 1) (CtrlCtr 1)) as [Hbt1 _].
    specialize (Hbridge_t2 v (StateCtr 1) (CtrlCtr 1)) as [Hbt2 _].
    rewrite Hbt1, Hbt2.
    assumption.
  - (* States case *)
    specialize (Hseq v Hv).
    apply smt_bool_eq_true in Hseq.
    repeat rewrite commute_conc_and_lookup in Hseq.
    assert (Hin_ps : is_varlike_in_ps (init_symbolic_state p1) v <> None).
    { apply in_program_implies_in_init_sym_state with (p := p1).
      - exact Hwf1_orig.
      - rewrite desp1. simpl. exact Hv. }
    rewrite <- commute_sym_vs_conc_transformer_state_var_map
      with (t := t1) (f := f) (s1 := init_symbolic_state p1) (sv := v) in Hseq;
      try assumption.
    rewrite <- commute_sym_vs_conc_transformer_state_var_map
      with (t := t2) (f := f) (s1 := init_symbolic_state p1) (sv := v) in Hseq;
      try assumption.
    specialize (Hbridge_t1 (HeaderCtr 1) v (CtrlCtr 1)) as [_ [Hbt1 _]].
    specialize (Hbridge_t2 (HeaderCtr 1) v (CtrlCtr 1)) as [_ [Hbt2 _]].
    rewrite Hbt1, Hbt2.
    assumption.
Qed.
