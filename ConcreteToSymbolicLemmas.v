From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import SmtExpr.
From MyProject Require Import StringUtils.
From MyProject Require Import CrSymbolicSemantics.
Require Import ZArith.
Require Import Coq.Strings.String.

(* Lemma relating evaluation of CR program and
                  evaluation of SMT expression *)
Lemma cr_eval_to_smt_eval :
  forall (hop : HdrOp) (ps : ProgramState uint8), eval_hdr_op_expr hop ps = eval_smt_expr (eval_hdr_op_expr_smt hop) (prog_state_to_smt_val ps).
Proof.
  destruct hop, f, arg1, arg2; (* destruct on header op, binary function, and 2 arguments *)
  simpl;
  try destruct h; (* if the two arguments are headers, destruct on these *)
  try destruct h0;
  try destruct c; (* similar with ctrl plane args *)
  try destruct c0;
  try destruct s; (* and state variables *)
  try destruct s0;
  simpl;
  reflexivity.
Qed.

(* Prove something using this assignment function above *)
Lemma cr_assign_correctness_stateful :
  forall (f : BinaryOp) (arg1 arg2 : FunctionArgument) (target : StateVar) (ps: ProgramState uint8),
    (state_var_map uint8 (eval_hdr_op (StatefulOp f arg1 arg2 target) ps)) target = (* updated value of target  *)
      eval_hdr_op_expr (StatefulOp f arg1 arg2 target) ps.                (* is what one would expect *)
Proof.
  intros.
  destruct f, arg1, arg2, target; simpl; destruct (string_dec name name); try reflexivity; try congruence.
Qed.