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

(* for any symbolic state, symbolic valuation, and header operation, 
   evaluating the header assignment on the concrete state equals
   as evaluating the symbolic state on the header assignment *)
Lemma compose_sym_conc_lemma:
  forall (ho : HdrOp) (s : ProgramState SmtExpr) (f : SmtValuation),
     eval_hdr_op_assign ho (eval_sym_state s f) =
      eval_sym_state (eval_hdr_op_assign ho s) f.
Proof.
Admitted.

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