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

(* Some kind of non interference,
  Copilot proved this automatically, huh? *)
Lemma non_interference:
  forall (c1 c2 : ProgramState uint8) (v : uint8) (s : StateVar),
    c2 = update_state c1 s v ->
    header_map uint8 c2 = header_map uint8 c1 /\
    ctrl_plane_map uint8 c2 = ctrl_plane_map uint8 c1.
Proof.
  intros c1 c2 v s H.
  destruct c1 as [con_ctrl con_hdr con_state].
  destruct c2 as [con_ctrl' con_hdr' con_state'].
  inversion H.
  split;
  reflexivity.
Qed.

Lemma project_from_record :
  forall (c : CtrlPlaneConfigNameMap uint8) (h : HeaderMap uint8) (s : StateVarMap uint8),
    (state_var_map uint8 {| ctrl_plane_map := c; header_map := h; state_var_map := s |}) = s.
Proof.
  intros c h s.
  unfold state_var_map.
  reflexivity.
Qed.

Lemma update_state_on_record:
  forall (c : CtrlPlaneConfigNameMap uint8) (h : HeaderMap uint8) (s : StateVarMap uint8) (sv : StateVar) (v : uint8),
      (* update_state is a record update, so it only changes the state_var_map *)
    (state_var_map uint8
     (update_state ({|ctrl_plane_map := c; header_map := h; state_var_map := s|}) sv v) sv) = v.
Proof.
  intros c h s sv v.
  unfold state_var_map.
  unfold update_state.
  unfold state_var_map.
  destruct sv.
  destruct (string_dec name name).
  - reflexivity.
  - destruct n. reflexivity.
Qed.

Lemma state_alone_updated:
forall (c1 c2 : ProgramState uint8) (v : uint8) (s : StateVar),
    c2 = update_state c1 s v ->
    (state_var_map uint8 c2) s = v.
Proof.
  intros c1 c2 v s H.
  destruct c1 as [con_ctrl con_hdr con_state].
  destruct c2 as [con_ctrl' con_hdr' con_state'].
  inversion H.
  unfold state_var_map.
  subst.
  destruct s.
  destruct (string_dec name name).
  - reflexivity.
  - destruct n. reflexivity.
Qed.

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
Lemma update_eval_compose:
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
  (* To prove f (e1 e2 e3) = f (e1' e2' e3'), it's enough to show e1 = e1', e2 = e2', e3 = e3'.*)
  (* Record {|field1 := f1 ; field2 = f2 ; field3 = f3 ;|} is equivalent to mkRecord (f1 f2 f3)
  and so then you can apply f_equal. *)
  (* Can use the same f_equal for pairs, tuples, lists, etc. 
     Any constructor of a type: f_equal is a good idea. *)
  - apply functional_extensionality.
    simpl.
    intros x.
    destruct x.
    destruct sv.
    destruct (string_dec name0 name).
    + reflexivity.
    + reflexivity.
Qed.

Lemma update_eval_compose2:
  forall (s : ProgramState SmtExpr) (f : SmtValuation) (h : Header) (v : SmtExpr),
    eval_sym_state (update_hdr s h v) f =
    update_hdr (eval_sym_state s f) h (eval_smt_expr v f).
Admitted.


(* for any symbolic state, symbolic valuation, and header operation, 
  concretizing and then evaluating EQUALS
  evaluating and then concretizing *)
Lemma compose_sym_conc_lemma:
  forall (ho : HdrOp) (s : ProgramState SmtExpr) (f : SmtValuation),
     eval_hdr_op_assign_uint8 ho (eval_sym_state s f) =
      eval_sym_state (eval_hdr_op_assign_smt ho s) f.
Proof.
  intros ho s f.
  unfold eval_hdr_op_assign_uint8.
  unfold eval_hdr_op_assign_smt.
  rewrite commute_smt_conc_expr.
  destruct ho, f0, arg1, arg2, s; simpl; try rewrite update_eval_compose; simpl; try reflexivity;
  try rewrite update_eval_compose2; simpl; try reflexivity.
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
  - apply compose_sym_conc_lemma.
  - rewrite Hc2.
    rewrite Hs2.
    rewrite Hc1.
    apply compose_sym_conc_lemma.
Qed.