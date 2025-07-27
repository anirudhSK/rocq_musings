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
  forall (ho: HdrOp) (s : ProgramState SmtArithExpr) (f : SmtValuation),
    eval_hdr_op_expr_uint8 ho (eval_sym_state s f) =
    eval_smt_arith (eval_hdr_op_expr_smt ho s) f.
Proof.
  intros ho s f.
  destruct ho, f0, arg1, arg2; simpl; try repeat (rewrite PMapHelperLemmas.commute_lookup_eval_ctrl); try reflexivity.
Qed.

Lemma commute_update_eval_state:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation) (sv : StateVar) (v : SmtArithExpr),
    eval_sym_state (update_state s sv v) f =
    update_state (eval_sym_state s f) sv (eval_smt_arith v f).
Proof.
  intros s f h v.
  unfold eval_sym_state.
  specialize (commute_mapper_update_state (T1 := SmtArithExpr) (T2 := uint8)).
  intros.
  apply H.
Qed.

Lemma commute_update_eval_hdr:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation) (h : Header) (v : SmtArithExpr),
    eval_sym_state (update_hdr s h v) f =
    update_hdr (eval_sym_state s f) h (eval_smt_arith v f).
Proof.
  intros s f h v.
  unfold eval_sym_state.
  specialize (commute_mapper_update_hdr (T1 := SmtArithExpr) (T2 := uint8)).
  intros.
  apply H.
Qed.

(* for any symbolic state, symbolic valuation, and header operation, 
  concretizing and then evaluating EQUALS
  evaluating and then concretizing *)
Lemma commute_sym_conc_assign:
  forall (ho : HdrOp) (s : ProgramState SmtArithExpr) (f : SmtValuation),
     eval_hdr_op_assign_uint8 ho (eval_sym_state s f) =
      eval_sym_state (eval_hdr_op_assign_smt ho s) f.
Proof.
  intros ho s f.
  unfold eval_hdr_op_assign_uint8.
  unfold eval_hdr_op_assign_smt.
  rewrite commute_sym_conc_expr.
  destruct ho, f0, arg1, arg2, s; simpl; try rewrite commute_update_eval_state; simpl; try reflexivity;
  try rewrite commute_update_eval_hdr; simpl; try reflexivity.
Qed.

Lemma commute_sym_vs_conc_hdr_op_list :
  forall (hol : list HdrOp) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr)
         (c1 : ProgramState uint8),
    c1 = eval_sym_state s1 f ->
    eval_hdr_op_list_uint8 hol c1 = (* first concretize, and then interpret *) 
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
         (s1 : ProgramState SmtArithExpr)
         (c1 : ProgramState uint8),
    c1 = eval_sym_state s1 f ->
    eval_match_uint8 [hv_pair] c1 = (* first concretize, and then interpret *)
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
    reflexivity. }
  rewrite H.
  destruct (eq (eval_smt_arith (lookup_hdr s1 h) f) v).
  - reflexivity.
  - reflexivity.
Qed.

(* The same lemma as above, but
   generalized to a MatchPattern instead of a header_pair *)
Lemma commute_sym_vs_conc_match_pattern :
  forall (mp: MatchPattern) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr)
         (c1 : ProgramState uint8),
    c1 = eval_sym_state s1 f ->
    eval_match_uint8 mp c1 = (* first concretize, and then interpret *)
    eval_smt_bool (eval_match_smt mp s1) f. (* first interpret , and then concretize *)
Proof.
  intros mp f s1 c1 Hc1.
  induction mp as [| hv_pair rest IHrest].
  - simpl. reflexivity.
  - assert (H1 : eval_match_uint8 (hv_pair :: rest) c1 =
                 eval_match_uint8 [hv_pair] c1 && eval_match_uint8 rest c1).
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
    destruct (eq (eval_smt_arith (lookup_hdr s1 h) f) v) eqn:des.
    -- rewrite andb_true_r. simpl. rewrite des. reflexivity.
    -- rewrite andb_false_l. simpl. rewrite des. reflexivity.
Qed.

(* Same as above lemma, but for a HdrOp gated by a match pattern *)
Lemma commute_sym_vs_conc_hdr_op_match_pattern :
  forall (ho: HdrOp) (mp: MatchPattern) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
    eval_hdr_op_assign_uint8_conditional mp ho (eval_sym_state s1 f  )= (* first concretize, and then interpret *)
    eval_sym_state (eval_hdr_op_assign_smt_conditional mp ho s1) f. (* first interpret, and then concretize *)
Proof.
  intros ho mp f s1.
  unfold eval_hdr_op_assign_uint8_conditional.
  unfold eval_hdr_op_assign_smt_conditional.
  unfold eval_hdr_op_assign_uint8.
  destruct ho;
  destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des.
  - rewrite commute_update_eval_state.
    f_equal.
    simpl.
    erewrite <- commute_sym_vs_conc_match_pattern.
    rewrite des.
    destruct f0; simpl; repeat (rewrite commute_lookup_eval); reflexivity. reflexivity.
  - rewrite commute_update_eval_state.
    f_equal.
    simpl.
    erewrite <- commute_sym_vs_conc_match_pattern; try reflexivity.
    rewrite des.
    apply nothing_changed_state.
  - rewrite commute_update_eval_hdr.
    f_equal.
    simpl.
    erewrite <- commute_sym_vs_conc_match_pattern.
    rewrite des.
    destruct f0; simpl; repeat (rewrite commute_lookup_eval); reflexivity. reflexivity.
  - rewrite commute_update_eval_hdr.
    f_equal.
    simpl.
    erewrite <- commute_sym_vs_conc_match_pattern; try reflexivity.
    rewrite des.
    apply nothing_changed_hdr.
Qed.

Lemma commute_sym_vs_conc_helper_seq_par_rule :
  forall (mp: MatchPattern) (hol: list HdrOp) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
    (if eval_match_uint8 mp (eval_sym_state s1 f)
    then eval_hdr_op_list_uint8 hol (eval_sym_state s1 f)
    else eval_sym_state s1 f) =
    eval_sym_state (update_all_states
                   (update_all_hdrs s1 (fun h => SmtConditional (eval_match_smt mp s1)
                                                                (lookup_hdr (eval_hdr_op_list_smt hol s1) h) (lookup_hdr s1 h)))
                   (fun s => SmtConditional (eval_match_smt mp s1)
                             (lookup_state (eval_hdr_op_list_smt hol s1) s) (lookup_state s1 s))) f.
Proof.
  intros mp hol f s1.
  apply program_state_equality.
  - simpl.
    destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des.
    + induction hol.
      * simpl. reflexivity.
      * simpl. rewrite ctrl_plane_invariant_hdr_op.
        rewrite IHhol.
        reflexivity.
    + simpl. reflexivity.
  - destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des;
    unfold eval_sym_state;
    apply functional_extensionality;
    intros x;
    destruct x;
    remember (header_map (* TODO: Ask Joe if there's a better way to capture this than remembering a complex application. *)
(program_state_mapper (fun e : SmtArithExpr => eval_smt_arith e f)
(fun e : SmtArithExpr => eval_smt_arith e f)
(fun e : SmtArithExpr => eval_smt_arith e f)
(update_all_states
(update_all_hdrs s1
(fun h : Header =>
SmtConditional (eval_match_smt mp s1)
(lookup_hdr (eval_hdr_op_list_smt hol s1) h)
(lookup_hdr s1 h)))
(fun s : StateVar =>
SmtConditional (eval_match_smt mp s1)
(lookup_state (eval_hdr_op_list_smt hol s1) s)
(lookup_state s1 s)))) (HeaderCtr uid)) as tmp;
    rewrite commute_mapper_lookup_hdr in Heqtmp;
    rewrite Heqtmp;
    rewrite <- lookup_hdr_unchanged_by_update_all_states with (fs := (fun s : StateVar => SmtConditional (eval_match_smt mp s1) (lookup_state (eval_hdr_op_list_smt hol s1) s)
                                                                                                           (lookup_state s1 s)));
    simpl;
    rewrite lookup_hdr_after_update_all_hdrs;
    simpl;
    rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity;
    rewrite des.
    + rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1) (c1 := eval_sym_state s1 f); reflexivity.
    + reflexivity.
  - destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des;
    unfold eval_sym_state;
    apply functional_extensionality;
    intros x;
    destruct x;

    remember (state_var_map
(program_state_mapper (fun e : SmtArithExpr => eval_smt_arith e f)
(fun e : SmtArithExpr => eval_smt_arith e f)
(fun e : SmtArithExpr => eval_smt_arith e f)
(update_all_states
(update_all_hdrs s1
(fun h : Header =>
SmtConditional (eval_match_smt mp s1)
(lookup_hdr (eval_hdr_op_list_smt hol s1) h)
(lookup_hdr s1 h)))
(fun s : StateVar =>
SmtConditional (eval_match_smt mp s1)
(lookup_state (eval_hdr_op_list_smt hol s1) s)
(lookup_state s1 s)))) (StateVarCtr uid)) as tmp;
    rewrite commute_mapper_lookup_state in Heqtmp;
    rewrite Heqtmp;

    rewrite <- commute_state_hdr_updates;
    rewrite <- lookup_state_unchanged_by_update_all_hdrs with (fh := (fun h : Header => SmtConditional (eval_match_smt mp s1) (lookup_hdr (eval_hdr_op_list_smt hol s1) h)
                                                                                                           (lookup_hdr s1 h)));
    simpl;
    rewrite lookup_state_after_update_all_states;
    simpl;
    rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity;
    rewrite des.
    + rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1) (c1 := eval_sym_state s1 f); reflexivity.
    + reflexivity.
Qed.

Lemma commute_sym_vs_conc_seq_rule :
  forall (sr: SeqRule) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
      eval_seq_rule_uint8 sr (eval_sym_state s1 f) = (* first concretize, and then interpret *)
      eval_sym_state (eval_seq_rule_smt sr s1) f. (* first interpret, and then concretize *)
Proof.
  intros sr f s1.
  destruct sr as [mp hol].
  unfold eval_seq_rule_uint8.
  unfold eval_seq_rule_smt. 
  apply commute_sym_vs_conc_helper_seq_par_rule.
Qed.

Lemma commute_sym_vs_conc_par_rule :
  forall (pr: ParRule) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
      eval_par_rule_uint8 pr (eval_sym_state s1 f) = (* first concretize, and then interpret *)
      eval_sym_state (eval_par_rule_smt pr s1) f. (* first interpret, and then concretize *)
Proof.
  intros pr f s1.
  destruct pr as [mp hol].
  unfold eval_par_rule_uint8.
  unfold eval_par_rule_smt.
  apply commute_sym_vs_conc_helper_seq_par_rule.
Qed.

Lemma commute_sym_vs_conc_ma_rule:
  forall (ma : MatchActionRule) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
    eval_match_action_rule_uint8 ma (eval_sym_state s1 f) = (* first concretize, and then interpret *)
    eval_sym_state (eval_match_action_rule_smt ma s1) f. (* first interpret, and then concretize *)
Proof.
  intros ma f s1.
  destruct ma as [sr | pr].
  - apply commute_sym_vs_conc_seq_rule.
  - apply commute_sym_vs_conc_par_rule.
Qed.

Lemma one_rule_transformer_equals_ma_rule:
  forall m c,
         eval_transformer_uint8 [m] c = 
         eval_match_action_rule_uint8 m c.
Proof.
  intros m c.
  unfold eval_transformer_uint8.
  unfold eval_match_action_rule_uint8.
  destruct m as [sr | pr].
  - simpl. destruct sr. destruct (eval_match_uint8 match_pattern c) eqn:des.
    -- reflexivity.
    -- simpl. rewrite des. reflexivity.
  - simpl. destruct pr. destruct (eval_match_uint8 match_pattern c) eqn:des.
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

Lemma one_rule_transformer_evals_to_ma_rule_smt:
  forall m f s,
         eval_sym_state (eval_transformer_smt [m] s) f =
         eval_match_action_rule_uint8 m (eval_sym_state s f).
Proof.
  intros m f s.
  unfold eval_transformer_smt.
  unfold eval_match_action_rule_smt.
  destruct m as [sr | pr].
  - apply program_state_equality.
    + destruct sr as [mp hol].
      simpl.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite ctrl_plane_invariant_hdr_op_list.
        reflexivity.
      * reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct sr as [mp hol].
      simpl.
      rewrite <- header_map_lookup_hdr.
      rewrite header_map_ps.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des;
      rewrite <- lookup_hdr_unchanged_by_update_all_states;
      rewrite lookup_hdr_after_update_all_hdrs;
      rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity;
      rewrite <- commute_state_hdr_updates;
      rewrite lookup_hdr_after_update_all_hdrs;
      simpl; rewrite des.
      * rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct sr as [mp hol].
      simpl.
      rewrite <- state_var_map_lookup_state.
      rewrite state_var_map_ps.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des;
      rewrite <- commute_state_hdr_updates;
      rewrite <- lookup_state_unchanged_by_update_all_hdrs;
      rewrite lookup_state_after_update_all_states;
      rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity;
      rewrite lookup_state_after_update_all_states;
      simpl; rewrite des.
      * rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * reflexivity.
  - apply program_state_equality.
    + destruct pr as [mp hol].
      simpl.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite ctrl_plane_invariant_hdr_op_list.
        reflexivity.
      * reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct pr as [mp hol].
      simpl.
      rewrite <- header_map_lookup_hdr.
      rewrite header_map_ps.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des;
      rewrite <- lookup_hdr_unchanged_by_update_all_states;
      rewrite lookup_hdr_after_update_all_hdrs;
      rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity;
      rewrite <- commute_state_hdr_updates;
      rewrite lookup_hdr_after_update_all_hdrs;
      simpl; rewrite des.
      * rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct pr as [mp hol].
      simpl.
      rewrite <- state_var_map_lookup_state.
      rewrite state_var_map_ps.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des;
      rewrite <- commute_state_hdr_updates;
      rewrite <- lookup_state_unchanged_by_update_all_hdrs;
      rewrite lookup_state_after_update_all_states;
      rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity;
      rewrite lookup_state_after_update_all_states;
      simpl; rewrite des.
      * rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * reflexivity.
Qed.

(* The transformer with one rule is equivalent to the match action rule *)
Lemma transfomer_with_one_rule:
  forall (m : MatchActionRule) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
  eval_transformer_uint8 [m] (eval_sym_state s1 f) = (* first concretize, and then interpret *)
  eval_sym_state (eval_transformer_smt [m] s1) f. (* first interpret, and then concretize *)
Proof.
  intros m f s1.
  rewrite one_rule_transformer_equals_ma_rule.
  rewrite one_rule_transformer_evals_to_ma_rule_smt.
  reflexivity.
Qed.

Lemma switch_case_expr_some_match_lemma :
  forall t f s1 h rule,
    Some rule = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    lookup_hdr (eval_match_action_rule_uint8 rule (eval_sym_state s1 f)) h =
    eval_smt_arith (switch_case_expr (combine (get_match_results_smt t s1)
                                              (map (fun ps : ProgramState SmtArithExpr => lookup_hdr ps h)
                                                   (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                     (lookup_hdr s1 h)) f.
Proof.
  intros.
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
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply header_map_ps.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule.
        assumption.
    --assert (In (true, rule)  (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply header_map_ps.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule.
        assumption.
Qed.

Lemma switch_case_expr_no_match_lemma :
  forall t f s1 h,
    None = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    eval_smt_arith (lookup_hdr s1 h) f =
    eval_smt_arith (switch_case_expr  (combine (get_match_results_smt t s1)
                                               (map (fun ps : ProgramState SmtArithExpr => lookup_hdr ps h)
                                                    (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                      (lookup_hdr s1 h)) f.
Proof.
  intros.
  induction t.
  - reflexivity.
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (forall x, In x (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_uint8 match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_uint8 match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action))  as tmp.
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
      specialize (H0 (eval_match_uint8 match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_uint8 match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action))  as tmp.
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
    Some rule = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    lookup_state (eval_match_action_rule_uint8 rule (eval_sym_state s1 f)) sv =
    eval_smt_arith (switch_case_expr (combine (get_match_results_smt t s1)
                                              (map (fun ps : ProgramState SmtArithExpr => lookup_state ps sv)
                                                   (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                     (lookup_state s1 sv)) f.
Proof.
  intros.
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
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply state_var_map_ps.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule.
        assumption.
    --assert (In (true, rule)  (combine
                               (get_match_results (Par (ParCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Par (ParCtr match_pattern action) :: t))).
      { apply find_first_match_lemma2. assumption. }
      simpl in H0.
      destruct (eval_smt_bool (eval_match_smt match_pattern s1) f) eqn:des.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        inversion H.
        apply state_var_map_ps.
      + rewrite <- commute_sym_vs_conc_match_pattern with (s1 := s1) (f := f) (c1 := eval_sym_state s1 f) in des; try reflexivity.
        rewrite des in H0.
        rewrite commute_sym_vs_conc_ma_rule.
        simpl in H.
        rewrite des in H.
        apply IHt in H.
        rewrite <- commute_sym_vs_conc_ma_rule.
        assumption.
Qed.

Lemma switch_case_expr_no_match_state_var_lemma :
  forall t f s1 sv,
    None = find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t) ->
    eval_smt_arith (lookup_state s1 sv) f =
    eval_smt_arith (switch_case_expr  (combine (get_match_results_smt t s1)
                                               (map (fun ps : ProgramState SmtArithExpr => lookup_state ps sv)
                                                    (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
                                      (lookup_state s1 sv)) f.
Proof.
  intros.
  induction t.
  - reflexivity. 
  - simpl.
    destruct a; try destruct s; try destruct p.
    --assert (forall x, In x (combine
                               (get_match_results (Seq (SeqCtr match_pattern action) :: t) (eval_sym_state s1 f))
                               (Seq (SeqCtr match_pattern action) :: t)) -> fst x = false).
      {apply find_first_match_lemma. assumption. }
      simpl in H0.
      specialize (H0 (eval_match_uint8 match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_uint8 match_pattern (eval_sym_state s1 f), Seq (SeqCtr match_pattern action))  as tmp.
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
      specialize (H0 (eval_match_uint8 match_pattern (eval_sym_state s1 f ), Par (ParCtr match_pattern action)) ).
      simpl in H0.
      remember (eval_match_uint8 match_pattern (eval_sym_state s1 f), Par (ParCtr match_pattern action))  as tmp.
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
     (lookup_hdr (eval_transformer_smt t s1) h) =
     switch_case_expr
     (combine (get_match_results_smt t s1)
     (map (fun ps : ProgramState SmtArithExpr => lookup_hdr ps h)
     (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
     (lookup_hdr s1 h).
Proof.
  intros.
  unfold eval_transformer_smt.
  rewrite <- commute_state_hdr_updates.
  rewrite lookup_hdr_after_update_all_hdrs.
  reflexivity.
Qed.

Lemma commute_sym_vs_conc_transformer_header_map:
  forall t f s1,
    lookup_hdr (eval_transformer_uint8 t (eval_sym_state s1 f)) =
    lookup_hdr (eval_sym_state (eval_transformer_smt t s1) f).
Proof.
  intros.
  simpl.
  apply functional_extensionality.
  intro h.
  unfold eval_transformer_uint8.
  remember (find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t)) as concrete_match.
  destruct concrete_match eqn:des.
  - rewrite commute_lookup_eval_hdr. rewrite hdr_transformer_helper. apply switch_case_expr_some_match_lemma. assumption.
  - assert(H0: lookup_hdr (eval_sym_state (eval_transformer_smt t s1) f) h =
               eval_smt_arith (lookup_hdr (eval_transformer_smt t s1) h ) f).
               { rewrite commute_lookup_eval_hdr. reflexivity. }
    rewrite H0.
    rewrite hdr_transformer_helper.
    rewrite commute_lookup_eval_hdr.
    apply switch_case_expr_no_match_lemma. assumption.
Qed.

Lemma state_transformer_helper:
  forall t s1 h,
     (lookup_state (eval_transformer_smt t s1) h) =
     switch_case_expr
     (combine (get_match_results_smt t s1)
     (map (fun ps : ProgramState SmtArithExpr => lookup_state ps h)
     (map (fun rule : MatchActionRule => eval_match_action_rule_smt rule s1) t)))
     (lookup_state s1 h).
Proof.
  intros.
  unfold eval_transformer_smt.
  rewrite lookup_state_after_update_all_states.
  reflexivity.
Qed.

Lemma commute_sym_vs_conc_transformer_state_var_map:
  forall t f s1,
    lookup_state (eval_transformer_uint8 t (eval_sym_state s1 f)) = lookup_state (eval_sym_state (eval_transformer_smt t s1) f).
Proof.
  intros.
  simpl.
  apply functional_extensionality.
  intro sv.
  unfold eval_transformer_uint8.
  remember (find_first_match (combine (get_match_results t (eval_sym_state s1 f)) t)) as concrete_match.
  destruct concrete_match eqn:des.
  - rewrite commute_lookup_eval_state. rewrite state_transformer_helper. apply switch_case_expr_some_match_state_var_lemma. assumption.
  - assert(H0: lookup_state (eval_sym_state (eval_transformer_smt t s1) f) sv =
               eval_smt_arith (lookup_state (eval_transformer_smt t s1) sv ) f).
               { rewrite commute_lookup_eval_state. reflexivity. }
    rewrite H0.
    rewrite state_transformer_helper.
    rewrite commute_lookup_eval_state.
    apply switch_case_expr_no_match_state_var_lemma. assumption.
Qed.

Lemma commute_sym_vs_conc_transformer_ctrl_plane_map:
  forall t f s1,
  ctrl_plane_map (eval_transformer_uint8 t (eval_sym_state s1 f)) =
  ctrl_plane_map (eval_sym_state (eval_transformer_smt t s1) f).
Proof.
  intros t f s1.
  rewrite ctrl_plane_invariant_transformer.
  unfold eval_sym_state.
  simpl.
  reflexivity.
Qed.

Lemma commute_sym_vs_conc_transfomer:
  forall (t: Transformer) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
    eval_transformer_uint8 t (eval_sym_state s1 f) = (* first concretize, and then interpret *)
    eval_sym_state (eval_transformer_smt t s1) f. (* first interpret, and then concretize *)
Proof.
  intros t f s1.
  induction t as [| m rest IHrest].
  - simpl. reflexivity.
  - simpl.
    apply program_state_equality.
    -- apply commute_sym_vs_conc_transformer_ctrl_plane_map.
    -- apply commute_sym_vs_conc_transformer_header_map.
    -- apply commute_sym_vs_conc_transformer_state_var_map.
Qed.

Print Assumptions commute_sym_vs_conc_seq_rule.
