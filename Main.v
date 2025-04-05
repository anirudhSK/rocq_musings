Require Import Arith.
Require Import Bool.
From Coq Require Import Strings.String.
Open Scope string_scope.
From MyProject Require Export SynEquivChecker.
From MyProject Require Export SmtEquivChecker.

Lemma sound_syn_checker (e1 e2 : expr)  (s : state) :
  syn_equiv_checker e1 e2 s = true -> e1 = e2.
  Proof.
    intros H.
    revert H.
    revert e2.
    induction e1; intros e2 H; destruct e2; try discriminate.
    - apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
    - simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H.
      rewrite (IHe1_1 _ H).
      rewrite (IHe1_2 e2_2 H0).
      reflexivity.
    - simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H.
      rewrite (IHe1_1 _ H).
      rewrite (IHe1_2 e2_2 H0).
      reflexivity.
    - simpl in H.
      apply Bool.andb_true_iff in H.
      destruct H.
      rewrite (IHe1_1 _ H).
      rewrite (IHe1_2 e2_2 H0).
      reflexivity.
    - apply String.eqb_eq in H.
      rewrite H.
      reflexivity.
  Qed.

(* Prove that the equivalence checker is correct *)
Theorem syn_equiv_checker_correct:
  forall (e1 e2 : expr) (s : state), syn_equiv_checker e1 e2 s = true -> aequiv e1 e2 s.
Proof.
intros e1 e2.
unfold aequiv.
intros s.
intros H.
apply sound_syn_checker in H.
rewrite H.
reflexivity.
Qed.

Lemma smt_plus_lemma:
 forall (e1 e2 : expr),
 symbolize_expr (Plus e1 e2) = SymPlus (symbolize_expr e1) (symbolize_expr e2).
 Proof.
  intros.
  destruct e1, e2; try unfold symbolize_expr; reflexivity.
 Qed.

 Lemma smt_minus_lemma:
 forall (e1 e2 : expr),
 symbolize_expr (Minus e1 e2) = SymMinus (symbolize_expr e1) (symbolize_expr e2).
 Proof.
  intros.
  destruct e1, e2; try unfold symbolize_expr; reflexivity.
 Qed.

(* Prove that the SMT equivalence checker is correct *)
Theorem smt_equiv_checker_correct:
  forall (e1 e2 : expr) (s : state), smt_equiv_checker e1 e2 s = true -> aequiv e1 e2 s.
Proof.
  apply sound_smt_checker.
Qed.

(* TODO: Write a constant fold optimizer before passing stuff into the z3 solver *)
(* Kind of like the optimizations in the K2 project that speeded up equivalence checking *)
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