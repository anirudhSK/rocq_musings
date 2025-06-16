From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
From MyProject Require Import CrSymbolicSemantics.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: ProgramState SmtExpr) (f : SmtValuation) : ProgramState uint8 :=
  {| header_map := fun h => eval_smt_expr (header_map SmtExpr s h) f;
     ctrl_plane_map := fun c => eval_smt_expr (ctrl_plane_map SmtExpr s c) f;
     state_var_map := fun sv => eval_smt_expr (state_var_map SmtExpr s sv) f |}.

(* Joe's theorem relating the concrete and symbolic worlds translated into rocq slack *)
Lemma symbolic_vs_concrete :
  forall (f : SmtValuation) (ho : HdrOp)
         (c1 : ProgramState uint8) (s1 : ProgramState SmtExpr)
         (c2 : ProgramState uint8) (s2 : ProgramState SmtExpr),
    c1 = eval_sym_state s1 f ->
    c2 = eval_hdr_op_assign ho c1 ->
    s2 = eval_hdr_op_assign ho s1 ->
    c2 = eval_sym_state s2 f.
Admitted.