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

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: ProgramState SmtArithExpr) (f : SmtValuation) : ProgramState uint8 :=
  {| header_map := fun h => eval_smt_arith (header_map SmtArithExpr s h) f;
     ctrl_plane_map := fun c => eval_smt_arith (ctrl_plane_map SmtArithExpr s c) f;
     state_var_map := fun sv => eval_smt_arith (state_var_map SmtArithExpr s sv) f |}.

(* Simpler lemma with no state update *)
Lemma commute_smt_conc_expr:
  forall (ho: HdrOp) (s : ProgramState SmtArithExpr) (f : SmtValuation),
    eval_hdr_op_expr_uint8 ho (eval_sym_state s f) =
    eval_smt_arith (eval_hdr_op_expr_smt ho s) f.
Proof.
  intros ho s f.
  destruct ho, f0, arg1, arg2; simpl; try reflexivity.
Qed.

Axiom functional_extensionality :
  forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) -> f = g.

Lemma commute_update_eval:
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

Lemma commute2_update_eval:
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
Lemma commute_sym_conc:
  forall (ho : HdrOp) (s : ProgramState SmtArithExpr) (f : SmtValuation),
     eval_hdr_op_assign_uint8 ho (eval_sym_state s f) =
      eval_sym_state (eval_hdr_op_assign_smt ho s) f.
Proof.
  intros ho s f.
  unfold eval_hdr_op_assign_uint8.
  unfold eval_hdr_op_assign_smt.
  rewrite commute_smt_conc_expr.
  destruct ho, f0, arg1, arg2, s; simpl; try rewrite commute_update_eval; simpl; try reflexivity;
  try rewrite commute2_update_eval; simpl; try reflexivity.
Qed.

Lemma symbolic_vs_concrete_hdr_op_list :
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
    rewrite commute_sym_conc.
    reflexivity.
Qed.

(* For any Header, uint8 pair,
   concrete and symbolic execution match up. *)
Lemma symbolic_vs_concrete_cond :
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
  assert (H : header_map uint8 (eval_sym_state s1 f) h =
              eval_smt_arith (header_map SmtArithExpr s1 h) f).
  { unfold eval_sym_state.
    simpl.
    reflexivity. }
  rewrite H.
  destruct (eq (eval_smt_arith (header_map SmtArithExpr s1 h) f) v).
  - reflexivity.
  - reflexivity.
Qed.