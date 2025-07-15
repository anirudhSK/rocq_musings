From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrSymbolicSemantics.
Require Import ZArith.
Require Import Coq.Strings.String.
Local Open Scope string_scope.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Bool.Bool.
From Coq Require Import FunctionalExtensionality.

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: ProgramState SmtArithExpr) (f : SmtValuation) : ProgramState uint8 :=
  {| header_map := fun h => eval_smt_arith (header_map s h) f;
     ctrl_plane_map := fun c => eval_smt_arith (ctrl_plane_map s c) f;
     state_var_map := fun sv => eval_smt_arith (state_var_map s sv) f |}.

(* Simpler lemma with no state update *)
Lemma commute_sym_conc_expr:
  forall (ho: HdrOp) (s : ProgramState SmtArithExpr) (f : SmtValuation),
    eval_hdr_op_expr_uint8 ho (eval_sym_state s f) =
    eval_smt_arith (eval_hdr_op_expr_smt ho s) f.
Proof.
  intros ho s f.
  destruct ho, f0, arg1, arg2; simpl; try reflexivity.
Qed.

Lemma commute_update_eval_state:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation) (sv : StateVar) (v : SmtArithExpr),
    eval_sym_state (update_state s sv v) f =
    update_state (eval_sym_state s f) sv (eval_smt_arith v f).
Proof.
  intros s f sv v.
  destruct s as [con_ctrl con_hdr con_state].
  simpl.
  unfold eval_sym_state.
  unfold update_state.
  f_equal.
  - apply functional_extensionality.
    simpl.
    intros x.
    destruct x.
    destruct sv.
    destruct (Pos.eqb uid0 uid).
    + reflexivity.
    + reflexivity.
Qed.

Lemma commute_update_eval_hdr:
  forall (s : ProgramState SmtArithExpr) (f : SmtValuation) (h : Header) (v : SmtArithExpr),
    eval_sym_state (update_hdr s h v) f =
    update_hdr (eval_sym_state s f) h (eval_smt_arith v f).
Proof.
  intros s f h v.
  destruct s as [con_ctrl con_hdr con_state].
  simpl.
  unfold eval_sym_state.
  unfold update_hdr.
  f_equal.
  - apply functional_extensionality.
    simpl.
    intros x.
    destruct x.
    destruct h.
    destruct (Pos.eqb uid0 uid).
    + reflexivity.
    + reflexivity.
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
  assert (H : header_map (eval_sym_state s1 f) h =
              eval_smt_arith (header_map s1 h) f).
  { unfold eval_sym_state.
    simpl.
    reflexivity. }
  rewrite H.
  destruct (eq (eval_smt_arith (header_map s1 h) f) v).
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
    destruct (eq (eval_smt_arith (header_map s1 h) f) v) eqn:des.
    -- rewrite andb_true_r. simpl. rewrite des. reflexivity.
    -- rewrite andb_false_l. simpl. rewrite des. reflexivity.
Qed.

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
     (eval_smt_arith (state_var_map s target) f).
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
     (eval_smt_arith (header_map s target) f).
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

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op:
  forall (ho: HdrOp)
         (c1: ProgramState uint8),
  ctrl_plane_map (eval_hdr_op_assign_uint8 ho c1) =
  ctrl_plane_map c1.
Proof.
  intros ho c1.
  destruct ho; simpl; try reflexivity.
Qed.

(* Effectively, ctrl plane doesn't change *)
Lemma ctrl_plane_invariant_hdr_op_list:
  forall hol c1,
  ctrl_plane_map (eval_hdr_op_list_uint8 hol c1) =
  ctrl_plane_map c1.
Proof.
  intros.
  induction hol.
  - reflexivity.
  - simpl. rewrite <- IHhol.
    apply ctrl_plane_invariant_hdr_op.
Qed.

Lemma commute_sym_vs_conc_helper_seq_par_rule :
  forall (mp: MatchPattern) (hol: list HdrOp) (f : SmtValuation)
         (s1 : ProgramState SmtArithExpr),
    (if eval_match_uint8 mp (eval_sym_state s1 f)
    then eval_hdr_op_list_uint8 hol (eval_sym_state s1 f)
    else eval_sym_state s1 f) =
    eval_sym_state {| ctrl_plane_map := ctrl_plane_map s1;
                      header_map := fun h : Header => SmtConditional (eval_match_smt mp s1)
                                                      (header_map (eval_hdr_op_list_smt hol s1) h) (header_map s1 h);
                      state_var_map := fun s : StateVar => SmtConditional (eval_match_smt mp s1)
                                                           (state_var_map (eval_hdr_op_list_smt hol s1) s) (state_var_map s1 s)
                    |} f.
Proof.
  intros mp hol f s1.
  apply program_state_equality.
  - apply functional_extensionality.
    intros x.
    destruct x.
    simpl.
    destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des.
    + induction hol.
      * simpl. reflexivity.
      * simpl. rewrite <- IHhol.
        rewrite ctrl_plane_invariant_hdr_op.
        reflexivity. 
    + simpl. reflexivity.
  - apply functional_extensionality.
    intros x.
    destruct x.
    simpl.
    destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des.
    + rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity.
      rewrite des.
      rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1) (c1 := eval_sym_state s1 f);
      reflexivity.
    + rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity.
      rewrite des.
      simpl. reflexivity.
  - apply functional_extensionality.
    intros x.
    destruct x.
    simpl.
    destruct (eval_match_uint8 mp (eval_sym_state s1 f)) eqn:des.
    + rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity.
      rewrite des.
      rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s1) (c1 := eval_sym_state s1 f);
      reflexivity.
    + rewrite <- commute_sym_vs_conc_match_pattern with (c1 := eval_sym_state s1 f); try reflexivity.
      rewrite des.
      simpl. reflexivity.
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
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct sr as [mp hol].
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
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        simpl. reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct sr as [mp hol].
      simpl.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        simpl. reflexivity.
  - apply program_state_equality.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct pr as [mp hol].
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
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        simpl. reflexivity.
    + apply functional_extensionality.
      intros x.
      simpl.
      destruct pr as [mp hol].
      simpl.
      destruct (eval_match_uint8 mp (eval_sym_state s f)) eqn:des.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        rewrite commute_sym_vs_conc_hdr_op_list with (f := f) (s1 := s); try reflexivity.
      * rewrite commute_sym_vs_conc_match_pattern with (f := f) (s1 := s) in des; try reflexivity.
        rewrite des.
        simpl. reflexivity.
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

Lemma ctrl_plane_invariant_seq_rule:
  forall s c,
    ctrl_plane_map (eval_seq_rule_uint8 s c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_seq_rule_uint8.
  destruct s.
  destruct (eval_match_uint8 match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_par_rule:
  forall p c,
    ctrl_plane_map (eval_par_rule_uint8 p c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_par_rule_uint8.
  destruct p.
  destruct (eval_match_uint8 match_pattern c).
  apply ctrl_plane_invariant_hdr_op_list.
  reflexivity.
Qed.

Lemma ctrl_plane_invariant_ma_rule:
  forall m c,
    ctrl_plane_map (eval_match_action_rule_uint8 m c) =
    ctrl_plane_map c.
Proof.
  intros.
  unfold eval_match_action_rule_uint8.
  destruct m.
  - apply ctrl_plane_invariant_seq_rule.
  - apply ctrl_plane_invariant_par_rule.
Qed.

Lemma ctrl_plane_invariant_transformer_intermediate:
  forall a t c,
    ctrl_plane_map (eval_transformer_uint8 (a :: t) c) =
    ctrl_plane_map (eval_transformer_uint8 t c).
Proof.
  intros.
  unfold eval_transformer_uint8.
  remember (a :: t) as full_list.
  remember (find_first_match (combine (get_match_results full_list c) full_list)) as outer_match.
  remember (find_first_match (combine (get_match_results t c) t)) as inner_match.
  destruct (outer_match) eqn:des; destruct inner_match eqn:des2; try rewrite ctrl_plane_invariant_ma_rule; try reflexivity.
  rewrite ctrl_plane_invariant_ma_rule. reflexivity.
Qed.

Lemma ctrl_plane_invariant_transformer:
  forall c t,
    ctrl_plane_map (eval_transformer_uint8 t c) = ctrl_plane_map c.
Proof.
  intros.
  induction t.
  - reflexivity.
  - rewrite <- IHt. apply ctrl_plane_invariant_transformer_intermediate.
Qed.

Lemma commute_sym_vs_conc_transformer_ctrl_plane_map:
  forall t f s1,
    ctrl_plane_map (eval_transformer_uint8 t (eval_sym_state s1 f)) = ctrl_plane_map (eval_sym_state (eval_transformer_smt t s1) f).
Proof.
  intros.
  simpl.
  rewrite ctrl_plane_invariant_transformer.
  reflexivity.
Qed.

Lemma commute_sym_vs_conc_transformer_header_map:
  forall t f s1,
    header_map (eval_transformer_uint8 t (eval_sym_state s1 f)) = header_map (eval_sym_state (eval_transformer_smt t s1) f).
Admitted.

Lemma commute_sym_vs_conc_transformer_state_var_map:
  forall t f s1,
    state_var_map (eval_transformer_uint8 t (eval_sym_state s1 f)) = state_var_map (eval_sym_state (eval_transformer_smt t s1) f).
Admitted.

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