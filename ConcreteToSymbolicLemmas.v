From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
From MyProject Require Import CrSymbolicSemantics.
Require Import ZArith.
Require Import Coq.Strings.String.
Local Open Scope string_scope.

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: ProgramState SmtExpr) (f : SmtValuation) : ProgramState uint8 :=
  {| header_map := fun h => eval_smt_expr (header_map SmtExpr s h) f;
     ctrl_plane_map := fun c => eval_smt_expr (ctrl_plane_map SmtExpr s c) f;
     state_var_map := fun sv => eval_smt_expr (state_var_map SmtExpr s sv) f |}.

(* Simpler lemma with no state update *)
Lemma commute_smt_conc_expr:
  forall (ho: HdrOp) (s : ProgramState SmtExpr) (f : SmtValuation),
    eval_hdr_op_expr_uint8 ho (eval_sym_state s f) =
    eval_smt_expr (eval_hdr_op_expr_smt ho s) f.
Proof.
  intros ho s f.
  destruct ho, f0, arg1, arg2; simpl; try reflexivity.
Qed.

Axiom functional_extensionality :
  forall (A B : Type) (f g : A -> B),
    (forall x, f x = g x) -> f = g.

Lemma commute_update_eval:
  forall (s : ProgramState SmtExpr) (f : SmtValuation) (sv : StateVar) (v : SmtExpr),
    eval_sym_state (update_state s sv v) f =
    update_state (eval_sym_state s f) sv (eval_smt_expr v f).
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
    destruct (string_dec name0 name).
    + reflexivity.
    + reflexivity.
Qed.

Lemma commute2_update_eval:
  forall (s : ProgramState SmtExpr) (f : SmtValuation) (h : Header) (v : SmtExpr),
    eval_sym_state (update_hdr s h v) f =
    update_hdr (eval_sym_state s f) h (eval_smt_expr v f).
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
    destruct (string_dec name0 name).
    + reflexivity.
    + reflexivity.
Qed.

(* for any symbolic state, symbolic valuation, and header operation, 
  concretizing and then evaluating EQUALS
  evaluating and then concretizing *)
Lemma commute_sym_conc:
  forall (ho : HdrOp) (s : ProgramState SmtExpr) (f : SmtValuation),
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

(* Joe's theorem relating the concrete and symbolic worlds translated into rocq slack *)
Lemma symbolic_vs_concrete :
  forall (f : SmtValuation) (ho : HdrOp)
         (c1 : ProgramState uint8) (s1 : ProgramState SmtExpr)
         (c2 : ProgramState uint8) (s2 : ProgramState SmtExpr),
    c1 = eval_sym_state s1 f ->
    c2 = eval_hdr_op_assign ho c1 ->
    s2 = eval_hdr_op_assign ho s1 ->
    c2 = eval_sym_state s2 f.
Proof.
  intros f ho c1 s1 c2 s2.
  intros Hc1 Hc2 Hs2.
  destruct ho.
  destruct f0.
  rewrite Hs2.
  rewrite Hc2.
  rewrite Hc1.
  - apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply commute_sym_conc.
Qed.