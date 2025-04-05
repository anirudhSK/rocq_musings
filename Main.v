Require Import Arith.
Require Import Bool.
From Coq Require Import Strings.String.
Open Scope string_scope.
From MyProject Require Export SmtEquivChecker.

(* Kind of like the constant folding optimizations in the K2 project that speeded up equivalence checking *)
Definition constant_fold(e : expr):=
  match e with
  | Plus (Constant n1) (Constant n2) => Constant (n1 + n2)
  | Minus (Constant n1) (Constant n2) => Constant (n1 - n2)
  | Mul (Constant n1) (Constant n2) => Constant (n1 * n2)
  | _ => e
end.

(* Prove correctness of constant_fold *)
Theorem constant_fold_thm : forall (e : expr) (s : state),
   eval_expr (constant_fold e) s =  eval_expr e s.
Proof.
  destruct e; try reflexivity || destruct e1, e2; reflexivity.
Qed.

Theorem smt_checker_reflexive : forall (e : expr) (s : state),
  smt_equiv_checker e e s = true.
Proof.
  intros.
  destruct e; try unfold smt_equiv_checker; try unfold symbolize_expr; try apply reflexive_sym_checker.
Qed.

Theorem thm1 : forall (e : expr) (s : state),
  smt_equiv_checker (constant_fold e) (e) s = true.
Proof.
  intros.
  unfold smt_equiv_checker.
  eapply eval_sym_checker.
  apply constant_fold_thm.
Qed.

Theorem smt_equiv_constant_fold : forall (e : expr) (s: state),
  smt_equiv_checker (constant_fold e) e s = true.
Proof.
  intros.
  apply thm1.
Qed.

(* TODO: Write a slicing optimizer that allows us to check different parts of the expression
   separately. *)

(* TODO: Effectively can think of an equivalence checker as an
   optimizing compiler from DSL to SMT that does state merging, constant folding, slicing, etc. *)