From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrSymbolicSemanticsTransformer.
Require Import ZArith.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
From Coq Require Import FunctionalExtensionality.
From MyProject Require Import HelperLemmas.
From MyProject Require Import CtrlPlaneInvariants.
From MyProject Require Import CrProgramState.

(* Simpler lemma with no state update *)
Lemma commute_sym_conc_expr:
  forall (ho: HdrOp) (s : SymbolicState) (f : SmtValuation),
    eval_hdr_op_expr_concrete ho (eval_sym_state s f) =
    eval_smt_arith (eval_hdr_op_expr_smt ho s) f.
Proof.
  intros ho s f.
  destruct ho, f0, arg1, arg2; simpl;
  try repeat (rewrite PMapHelperLemmas.commute_lookup_eval_ctrl); try reflexivity;
  try repeat (rewrite PMapHelperLemmas.commute_lookup_eval_state); try reflexivity; (* TODO: How did this work before? *)
  try repeat (rewrite PMapHelperLemmas.commute_lookup_eval_hdr); try reflexivity.
Qed.

Lemma commute_update_eval_state:
  forall (s : SymbolicState) (f : SmtValuation) (sv : State) (v : SmtArithExpr),
    eval_sym_state (update_state s sv v) f =
    update_state (eval_sym_state s f) sv (eval_smt_arith v f).
Proof.
  intros s f h v.
  unfold eval_sym_state.
  specialize (commute_mapper_update_state (T1 := SmtArithExpr) (T2 := (InitStatus uint8))). (* TODO: Maybe typedef for InitStatus uint8 *)
  intros.
  apply H.
Qed.

Lemma commute_update_eval_hdr:
  forall (s : SymbolicState) (f : SmtValuation) (h : Header) (v : SmtArithExpr),
    eval_sym_state (update_hdr s h v) f =
    update_hdr (eval_sym_state s f) h (eval_smt_arith v f).
Proof.
  intros s f h v.
  unfold eval_sym_state.
  specialize (commute_mapper_update_hdr (T1 := SmtArithExpr) (T2 := InitStatus uint8)).
  intros.
  apply H.
Qed.

(* for any symbolic state, symbolic valuation, and header operation, 
  concretizing and then evaluating EQUALS
  evaluating and then concretizing *)
Lemma commute_sym_conc_assign:
  forall (ho : HdrOp) (s : SymbolicState) (f : SmtValuation),
     eval_hdr_op_assign_concrete ho (eval_sym_state s f) =
      eval_sym_state (eval_hdr_op_assign_smt ho s) f.
Proof.
  intros ho s f.
  unfold eval_hdr_op_assign_concrete.
  unfold eval_hdr_op_assign_smt.
  rewrite commute_sym_conc_expr.
  destruct ho, f0, arg1, arg2, s; simpl; try rewrite commute_update_eval_state; simpl; try reflexivity;
  try rewrite commute_update_eval_hdr; simpl; try reflexivity.
Qed.

Lemma commute_sym_vs_conc_hdr_op_list :
  forall (hol : list HdrOp) (f : SmtValuation)
         (s1 : SymbolicState)
         (c1 : ConcreteState),
    c1 = eval_sym_state s1 f ->
    eval_hdr_op_list_concrete hol c1 = (* first concretize, and then interpret *) 
    eval_sym_state (eval_hdr_op_list_smt hol s1) f.    (* first interpret, and then concretize *)
Proof.
  intros hol f s1 c1 Hc1.
  induction hol as [| h rest IHrest].
  - simpl. assumption.
  - simpl. rewrite IHrest.
    rewrite commute_sym_conc_assign.
    reflexivity.
Qed.

(* For any Header, uint8 pair,
   concrete and symbolic execution match up. *)
Lemma commute_sym_vs_conc_match_cond :
  forall (hv_pair: Header * uint8) (f : SmtValuation)
         (s1 : SymbolicState)
         (c1 : ConcreteState),
    c1 = eval_sym_state s1 f ->
    eval_match_concrete [hv_pair] c1 = (* first concretize, and then interpret *)
    eval_smt_bool (eval_match_smt [hv_pair] s1) f. (* first interpret, and then concretize *)
Proof.
  intros hv_pair f s1 c1 Hc1.
  destruct hv_pair as [h v].
  simpl.
  rewrite andb_true_r.
  rewrite Hc1.
  assert (H : lookup_hdr (eval_sym_state s1 f) h =
              eval_smt_arith (lookup_hdr s1 h) f).
  { unfold eval_sym_state.
    simpl.
    rewrite commute_mapper_lookup_hdr.
    reflexivity. }
  rewrite H.
  destruct (initstatus_uint8_equal (eval_smt_arith (lookup_hdr s1 h) f) (Initialized uint8 v)).
  - reflexivity.
  - reflexivity.
Qed.

(* The same lemma as above, but
   generalized to a MatchPattern instead of a header_pair *)
Lemma commute_sym_vs_conc_match_pattern :
  forall (mp: MatchPattern) (f : SmtValuation)
         (s1 : SymbolicState)
         (c1 : ConcreteState),
    c1 = eval_sym_state s1 f ->
    eval_match_concrete mp c1 = (* first concretize, and then interpret *)
    eval_smt_bool (eval_match_smt mp s1) f. (* first interpret , and then concretize *)
Proof.
  intros mp f s1 c1 Hc1.
  induction mp as [| hv_pair rest IHrest].
  - simpl. reflexivity.
  - assert (H1 : eval_match_concrete (hv_pair :: rest) c1 =
                 eval_match_concrete [hv_pair] c1 && eval_match_concrete rest c1).
    { simpl. rewrite andb_true_r. reflexivity. } 
    rewrite H1.
    assert (H3 : eval_smt_bool (SmtBoolAnd (eval_match_smt [hv_pair] s1) (eval_match_smt rest s1)) f
                 = eval_smt_bool (eval_match_smt [hv_pair] s1) f &&
                   eval_smt_bool (eval_match_smt rest s1) f).
    { reflexivity. }
    rewrite (commute_sym_vs_conc_match_cond hv_pair f s1 c1 Hc1).
    rewrite IHrest.
    destruct hv_pair as [h v].
    simpl.
    destruct (eval_match_smt rest s1); try reflexivity.
    destruct (initstatus_uint8_equal (eval_smt_arith (lookup_hdr s1 h) f) (Initialized uint8 v)) eqn:des.
    -- rewrite andb_true_r. simpl. rewrite des. reflexivity.
    -- rewrite andb_false_l. simpl. rewrite des. reflexivity.
Qed.

Lemma commute_sym_vs_conc_helper_seq_par_rule_hdr :
  forall (mp: MatchPattern) (hol: list HdrOp) (f : SmtValuation)
         (s1 : SymbolicState) (h : Header),
         is_header_in_ps s1 h <> None ->
    lookup_hdr (if eval_match_concrete mp (eval_sym_state s1 f)
    then eval_hdr_op_list_concrete hol (eval_sym_state s1 f)
    else eval_sym_state s1 f) h =
    lookup_hdr (eval_sym_state (update_all_states
                   (update_all_hdrs s1 (fun h => SmtConditional (eval_match_smt mp s1)
                                                                (lookup_hdr (eval_hdr_op_list_smt hol s1) h) (lookup_hdr s1 h)))
                   (fun s => SmtConditional (eval_match_smt mp s1)
                             (lookup_state (eval_hdr_op_list_smt hol s1) s) (lookup_state s1 s))) f) h.
Proof.
  intros mp hol f s1 h Hh.
  unfold eval_sym_state at 4.
  rewrite commute_mapper_lookup_hdr.
  rewrite <- commute_state_hdr_updates.
  rewrite lookup_hdr_after_update_all_hdrs.
  -- destruct (eval_match_concrete mp (eval_sym_state s1 f)) eqn:Hmatch.
     + simpl.
       rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); auto.
       rewrite Hmatch.
       rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1); auto.
       rewrite commute_lookup_eval_hdr.
       reflexivity.
     + simpl.
       rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); auto.
       rewrite Hmatch.
       rewrite commute_lookup_eval_hdr.
       reflexivity.
  -- rewrite is_header_in_ps_after_update_all_states. assumption.
Qed.

Lemma commute_sym_vs_conc_helper_seq_par_rule_sv :
  forall (mp: MatchPattern) (hol: list HdrOp) (f : SmtValuation)
         (s1 : SymbolicState) (sv : State),
         is_state_var_in_ps s1 sv <> None ->
    lookup_state (if eval_match_concrete mp (eval_sym_state s1 f)
    then eval_hdr_op_list_concrete hol (eval_sym_state s1 f)
    else eval_sym_state s1 f) sv =
    lookup_state (eval_sym_state (update_all_states
                   (update_all_hdrs s1 (fun h => SmtConditional (eval_match_smt mp s1)
                                                                (lookup_hdr (eval_hdr_op_list_smt hol s1) h) (lookup_hdr s1 h)))
                   (fun s => SmtConditional (eval_match_smt mp s1)
                             (lookup_state (eval_hdr_op_list_smt hol s1) s) (lookup_state s1 s))) f) sv.
Proof.
  intros mp hol f s1 sv Hsv.
  unfold eval_sym_state at 4.
  rewrite commute_mapper_lookup_state.
  rewrite lookup_state_after_update_all_states.
  -- destruct (eval_match_concrete mp (eval_sym_state s1 f)) eqn:Hmatch.
     + simpl.
       rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); auto.
       rewrite Hmatch.
       rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1); auto.
       rewrite commute_lookup_eval_state.
       reflexivity.
     + simpl.
       rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); auto.
       rewrite Hmatch.
       rewrite commute_lookup_eval_state.
       reflexivity.
  -- rewrite is_state_var_in_ps_after_update_all_hdrs. assumption.
Qed.

Lemma commute_sym_vs_conc_seq_rule_hdr :
  forall (sr: SeqRule) (f : SmtValuation)
         (s1 : SymbolicState) (h : Header),
      is_header_in_ps s1 h <> None ->
      lookup_hdr (eval_seq_rule_concrete sr (eval_sym_state s1 f)) h = (* first concretize, and then interpret *)
      lookup_hdr (eval_sym_state (eval_seq_rule_smt sr s1) f) h. (* first interpret, and then concretize *)
Proof.
  intros sr f s1 h Hh.
  destruct sr as [mp hol].
  unfold eval_seq_rule_concrete.
  unfold eval_seq_rule_smt.
  apply commute_sym_vs_conc_helper_seq_par_rule_hdr. assumption.
Qed.

Lemma commute_sym_vs_conc_par_rule_hdr :
  forall (pr: ParRule) (f : SmtValuation)
         (s1 : SymbolicState) (h : Header),
    is_header_in_ps s1 h <> None ->
    lookup_hdr (eval_par_rule_concrete pr (eval_sym_state s1 f)) h = (* first concretize, and then interpret *)
    lookup_hdr (eval_sym_state (eval_par_rule_smt pr s1) f) h. (* first interpret, and then concretize *)
Proof.
  intros pr f s1 h Hh.
  destruct pr as [mp hol].
  unfold eval_par_rule_concrete.
  unfold eval_par_rule_smt.
  apply commute_sym_vs_conc_helper_seq_par_rule_hdr. assumption.
Qed.

(* Same as above two lemmas but for state variables *)
Lemma commute_sym_vs_conc_seq_rule_sv :
  forall (sr: SeqRule) (f : SmtValuation)
         (s1 : SymbolicState) (sv : State),
    is_state_var_in_ps s1 sv <> None ->
    lookup_state (eval_seq_rule_concrete sr (eval_sym_state s1 f)) sv = (* first concretize, and then interpret *)
    lookup_state (eval_sym_state (eval_seq_rule_smt sr s1) f) sv. (* first interpret, and then concretize *)
Proof.
  intros sr f s1 sv Hsv.
  destruct sr as [mp hol].
  unfold eval_seq_rule_concrete.
  unfold eval_seq_rule_smt.
  apply commute_sym_vs_conc_helper_seq_par_rule_sv. assumption.
Qed.

Lemma commute_sym_vs_conc_par_rule_sv :
  forall (pr: ParRule) (f : SmtValuation)
         (s1 : SymbolicState) (sv : State),
    is_state_var_in_ps s1 sv <> None ->
    lookup_state (eval_par_rule_concrete pr (eval_sym_state s1 f)) sv = (* first concretize, and then interpret *)
    lookup_state (eval_sym_state (eval_par_rule_smt pr s1) f) sv. (* first interpret, and then concretize *)
Proof.
  intros pr f s1 sv Hsv.
  destruct pr as [mp hol].
  unfold eval_par_rule_concrete.
  unfold eval_par_rule_smt.
  apply commute_sym_vs_conc_helper_seq_par_rule_sv. assumption.
Qed.

Lemma commute_sym_vs_conc_ma_rule_hdr:
  forall (ma : MatchActionRule) (f : SmtValuation)
         (s1 : SymbolicState) (h: Header),
    is_header_in_ps s1 h <> None ->
    lookup_hdr (eval_match_action_rule_concrete ma (eval_sym_state s1 f)) h = (* first concretize, and then interpret *)
    lookup_hdr (eval_sym_state (eval_match_action_rule_smt ma s1) f) h. (* first interpret, and then concretize *)
Proof.
  intros ma f s1 h Hh.
  destruct ma as [sr | pr].
  - apply commute_sym_vs_conc_seq_rule_hdr. assumption.
  - apply commute_sym_vs_conc_par_rule_hdr. assumption.
Qed.

Lemma commute_sym_vs_conc_ma_rule_sv:
  forall (ma : MatchActionRule) (f : SmtValuation)
         (s1 : SymbolicState) (sv: State),
    is_state_var_in_ps s1 sv <> None ->
    lookup_state (eval_match_action_rule_concrete ma (eval_sym_state s1 f)) sv = (* first concretize, and then interpret *)
    lookup_state (eval_sym_state (eval_match_action_rule_smt ma s1) f) sv. (* first interpret, and then concretize *)
Proof.
  intros ma f s1 sv Hsv.
  destruct ma as [sr | pr].
  - apply commute_sym_vs_conc_seq_rule_sv. assumption.
  - apply commute_sym_vs_conc_par_rule_sv. assumption.
Qed.

Lemma one_rule_transformer_equals_ma_rule:
  forall m c,
         eval_transformer_concrete [m] c = 
         eval_match_action_rule_concrete m c.
Proof.
  intros m c.
  unfold eval_transformer_concrete.
  unfold eval_match_action_rule_concrete.
  destruct m as [sr | pr].
  - simpl. destruct sr. destruct (eval_match_concrete match_pattern c) eqn:des.
    -- reflexivity.
    -- simpl. rewrite des. reflexivity.
  - simpl. destruct pr. destruct (eval_match_concrete match_pattern c) eqn:des.
    -- reflexivity.
    -- simpl. rewrite des. reflexivity.
Qed.

Lemma eval_conditionals :
  forall condexpr thenexpr elseexpr f,
    eval_smt_bool condexpr f = true ->
    eval_smt_arith (SmtConditional condexpr thenexpr elseexpr) f =
    eval_smt_arith thenexpr f.
Proof.
  intros.
  simpl.
  rewrite H.
  reflexivity.
Qed.

Lemma switch_case_expr_some_match_lemma :
  forall t f s1 h rule,
    is_header_in_ps s1 h <> None ->
    Some rule = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    lookup_hdr (eval_match_action_rule_concrete rule (eval_sym_state s1 f)) h =
    eval_smt_arith (switch_case_expr (combine (get_match_results_smt t s1)
                                              (map (fun ps : SymbolicState => lookup_hdr ps h)
                                                   (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                     (lookup_hdr s1 h)) f.
Proof.
  intros t f s1 h rule Hh H.
  induction t.
  - simpl.
    simpl in H.
    discriminate H.
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (In (true, rule)  (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_hdr.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply header_map_ps. assumption.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_hdr.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule_hdr.
        assumption. assumption. assumption.
    --assert (In (true, rule)  (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_hdr.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply header_map_ps. assumption.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_hdr.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule_hdr.
        assumption. assumption. assumption.
Qed.

Lemma switch_case_expr_no_match_lemma :
  forall t f s1 h,
    is_header_in_ps s1 h <> None ->
    None = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    eval_smt_arith (lookup_hdr s1 h) f =
    eval_smt_arith (switch_case_expr  (combine (get_match_results_smt t s1)
                                               (map (fun ps : SymbolicState => lookup_hdr ps h)
                                                    (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                      (lookup_hdr s1 h)) f.
Proof.
  intros t f s1 h Hh H.
  induction t.
  - reflexivity.
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (forall x, In x (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_concrete match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_concrete match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action))  as tmp.
      assert (H_premise : tmp = tmp \/ In tmp (combine (get_match_results t (eval_sym_state s1 f)) t)). { left. reflexivity. }
      apply H0 in H_premise.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H_premise; try reflexivity.
      rewrite H_premise.
      simpl.
      simpl in H.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H; try reflexivity.
      rewrite H_premise in H.
      apply IHt in H.
      assumption.
    --assert (forall x, In x (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_concrete match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_concrete match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action))  as tmp.
      assert (H_premise : tmp = tmp \/ In tmp (combine (get_match_results t (eval_sym_state s1 f)) t)). { left. reflexivity. }
      apply H0 in H_premise.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H_premise; try reflexivity.
      rewrite H_premise.
      simpl.
      simpl in H.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H; try reflexivity.
      rewrite H_premise in H.
      apply IHt in H.
      assumption.
Qed.

(* Create 2 lemmas similar to the switch_case lemmas above,
   except with lookup_hdr replaced by lookup_state.
   The remaining aspects can be identical. *)
Lemma switch_case_expr_some_match_state_var_lemma :
  forall t f s1 sv rule,
    is_state_var_in_ps s1 sv <> None ->
    Some rule = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    lookup_state (eval_match_action_rule_concrete rule (eval_sym_state s1 f)) sv =
    eval_smt_arith (switch_case_expr (combine (get_match_results_smt t s1)
                                              (map (fun ps : SymbolicState => lookup_state ps sv)
                                                   (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                     (lookup_state s1 sv)) f.
Proof.
  intros t f s1 sv rule Hsv H.
  induction t.
  - simpl.
    simpl in H.
    discriminate H.
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (In (true, rule)  (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_sv.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply state_var_map_ps.
        assumption.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_sv.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule_sv.
        assumption. assumption. assumption.
    --assert (In (true, rule)  (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_sv.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply state_var_map_ps.
        assumption.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule_sv.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule_sv.
        assumption. assumption. assumption.
Qed.

Lemma switch_case_expr_no_match_state_var_lemma :
  forall t f s1 sv,
    is_state_var_in_ps s1 sv <> None ->
    None = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    eval_smt_arith (lookup_state s1 sv) f =
    eval_smt_arith (switch_case_expr  (combine (get_match_results_smt t s1)
                                               (map (fun ps : SymbolicState => lookup_state ps sv)
                                                    (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                      (lookup_state s1 sv)) f.
Proof.
  intros t f s1 sv Hsv H.
  induction t.
  - reflexivity. 
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (forall x, In x (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_concrete match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_concrete match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action))  as tmp.
      assert (H_premise : tmp = tmp \/ In tmp (combine (get_match_results t (eval_sym_state s1 f)) t)). { left. reflexivity. }
      apply H0 in H_premise.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H_premise; try reflexivity.
      rewrite H_premise.
      simpl.
      simpl in H.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H; try reflexivity.
      rewrite H_premise in H.
      apply IHt in H.
      assumption.
    --assert (forall x, In x (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_concrete match_pattern (eval_sym_state s1 f ), Par (ParCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_concrete match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action))  as tmp.
      assert (H_premise : tmp = tmp \/ In tmp (combine (get_match_results t (eval_sym_state s1 f)) t)). { left. reflexivity. }
      apply H0 in H_premise.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H_premise; try reflexivity.
      rewrite H_premise.
      simpl.
      simpl in H.
      rewrite commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) in H; try reflexivity.
      rewrite H_premise in H.
      apply IHt in H.
      assumption.
Qed.

Lemma hdr_transformer_helper:
  forall t s1 h,
     is_header_in_ps s1 h <> None ->
     (lookup_hdr (eval_transformer_smt t s1) h) =
     switch_case_expr
     (combine (get_match_results_smt t s1)
     (map (fun ps : SymbolicState => lookup_hdr ps h)
     (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
     (lookup_hdr s1 h).
Proof.
  intros.
  unfold eval_transformer_smt.
  rewrite <- commute_state_hdr_updates.
  rewrite lookup_hdr_after_update_all_hdrs.
  -- reflexivity.
  -- rewrite is_header_in_ps_after_update_all_states.
     assumption.
Qed.

Lemma commute_sym_vs_conc_transformer_header_map:
  forall t f s1 h,
    is_header_in_ps s1 h <> None ->
    lookup_hdr (eval_transformer_concrete t (eval_sym_state s1 f)) h = (* TODO: Can use some notation for lookup_hdr *)
    lookup_hdr (eval_sym_state (eval_transformer_smt t s1) f) h.
Proof.
  intros.
  simpl.
  unfold eval_transformer_concrete.
  remember (find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t)) as concrete_match.
  destruct concrete_match eqn:des.
  - repeat rewrite <- lookup_hdr_trivial.
    rewrite commute_lookup_eval_hdr. rewrite hdr_transformer_helper. apply switch_case_expr_some_match_lemma. assumption. assumption. assumption. (* TODO: This seems kind of brittle. *)
  - assert(H0: lookup_hdr (eval_sym_state (eval_transformer_smt t s1) f) h =
               eval_smt_arith (lookup_hdr (eval_transformer_smt t s1) h ) f).
               { rewrite commute_lookup_eval_hdr. reflexivity. }
    repeat rewrite <- lookup_hdr_trivial.
    rewrite H0.
    rewrite hdr_transformer_helper.
    rewrite commute_lookup_eval_hdr.
    apply switch_case_expr_no_match_lemma. assumption. assumption. assumption. (* TODO: This seems kind of brittle. *)
Qed.

Lemma state_transformer_helper:
  forall t s1 sv,
     is_state_var_in_ps s1 sv <> None ->
     (lookup_state (eval_transformer_smt t s1) sv) =
     switch_case_expr
     (combine (get_match_results_smt t s1)
     (map (fun ps : SymbolicState => lookup_state ps sv)
     (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
     (lookup_state s1 sv).
Proof.
  intros.
  unfold eval_transformer_smt.
  rewrite lookup_state_after_update_all_states.
  -- reflexivity.
  -- rewrite is_state_var_in_ps_after_update_all_hdrs.
     assumption. 
Qed.

Lemma commute_sym_vs_conc_transformer_state_var_map:
  forall t f s1 sv,
    is_state_var_in_ps s1 sv <> None ->
    lookup_state (eval_transformer_concrete t (eval_sym_state s1 f)) sv = (* first concretize, and then interpret *)
    lookup_state (eval_sym_state (eval_transformer_smt t s1) f) sv. (* first interpret, and then concretize *)
Proof.
  intros.
  simpl.
  unfold eval_transformer_concrete.
  remember (find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t)) as concrete_match.
  destruct concrete_match eqn:des.
  - repeat rewrite <- lookup_state_trivial.
    rewrite commute_lookup_eval_state. rewrite state_transformer_helper. apply switch_case_expr_some_match_state_var_lemma. assumption. assumption. assumption. (* TODO: This seems kind of brittle. *)
  - assert(H0: lookup_state (eval_sym_state (eval_transformer_smt t s1) f) sv =
               eval_smt_arith (lookup_state (eval_transformer_smt t s1) sv ) f).
               { rewrite commute_lookup_eval_state. reflexivity. }
    repeat rewrite <- lookup_state_trivial.
    rewrite H0.
    rewrite state_transformer_helper.
    rewrite commute_lookup_eval_state.
    apply switch_case_expr_no_match_state_var_lemma. assumption. assumption. assumption. (* TODO: This seems kind of brittle. *)
Qed.

Lemma commute_sym_vs_conc_transformer_ctrl_map:
  forall t f s1,
  ctrl_map (eval_transformer_concrete t (eval_sym_state s1 f)) =
  ctrl_map (eval_sym_state (eval_transformer_smt t s1) f).
Proof.
  intros t f s1.
  rewrite ctrl_plane_invariant_transformer.
  unfold eval_sym_state.
  simpl.
  reflexivity.
Qed.

Lemma commute_sym_vs_conc_transfomer_hdr:
  forall (t: Transformer) (f : SmtValuation)
         (s1 : SymbolicState)
         (h : Header),
    is_header_in_ps s1 h <> None ->
    lookup_hdr (eval_transformer_concrete t (eval_sym_state s1 f)) h = (* first concretize, and then interpret *)
    lookup_hdr (eval_sym_state (eval_transformer_smt t s1) f) h. (* first interpret, and then concretize *)
Proof.
  intros t f s1 h.
  induction t as [| m rest IHrest].
  - simpl.
    unfold eval_transformer_concrete.
    simpl.
    unfold eval_transformer_smt.
    simpl.
    rewrite program_state_unchanged.
    reflexivity.
  - simpl.
    apply commute_sym_vs_conc_transformer_header_map.
Qed.

Lemma commute_sym_vs_conc_transfomer_sv:
  forall (t: Transformer) (f : SmtValuation)
         (s1 : SymbolicState)
         (sv : State),
    is_state_var_in_ps s1 sv <> None ->
    lookup_state (eval_transformer_concrete t (eval_sym_state s1 f)) sv = (* first concretize, and then interpret *)
    lookup_state (eval_sym_state (eval_transformer_smt t s1) f) sv. (* first interpret, and then concretize *)
Proof.
  intros t f s1 sv.
  induction t as [| m rest IHrest].
  - simpl.
    unfold eval_transformer_concrete.
    simpl.
    unfold eval_transformer_smt.
    simpl.
    rewrite program_state_unchanged.
    reflexivity.
  - simpl.
    apply commute_sym_vs_conc_transformer_state_var_map.
Qed.