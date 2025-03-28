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
  intros e1 e2 s.
  unfold aequiv.
  intros H.
  destruct e1, e2; try discriminate.
  - unfold smt_equiv_checker in H.
    apply Nat.eqb_eq in H.
    rewrite H.
    reflexivity.
  - unfold smt_equiv_checker in H.
    apply sound_smt_checker.
    rewrite smt_plus_lemma.
    rewrite smt_plus_lemma.
    apply H.
  - unfold smt_equiv_checker in H.
    apply sound_smt_checker.
    rewrite smt_minus_lemma.
    rewrite smt_minus_lemma.
    apply H.
  - unfold smt_equiv_checker in H.
    apply String.eqb_eq in H.
    rewrite H.
    reflexivity.
Qed.