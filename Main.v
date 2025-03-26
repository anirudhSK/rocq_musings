Require Import Arith.
Require Import Bool.
From Coq Require Import Strings.String.
Open Scope string_scope.
From MyProject Require Export EquivalenceChecker.

(* destruct and induction both generate the same number of goals:
     one for each data constructor,
     the difference is induction generates additional inductive hypothesis
     for the recursive data constructors (like Plus, Mul, MInus)*)
Lemma one_more_lemma (e1 e2 : expr)  (s : state) :
  equivalence_checker e1 e2 s = true -> e1 = e2.
  Proof. (* intro is one term, intros is multiple terms *)
    intros H. (* Stuff on the right hand side of the colon doesn't go automatically into environment or context*)
    (* TODO: Need a more general induction hypothesis here .*)
    revert H.
    revert e2.
    induction e1; intros e2 H; destruct e2; try discriminate.
    - apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
    - simpl in H. (* TODO: lookup beta reduction *)
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

Lemma plus_lemma: (forall (e1_1 e1_2 e2_1 e2_2 : expr) (s : state), 
  equivalence_checker e1_1 e2_1 s &&
  equivalence_checker e1_2 e2_2 s = true -> Plus e1_1 e1_2 = Plus e2_1 e2_2).
  Proof.
    intros.
    apply Bool.andb_true_iff in H.
    destruct H.
    apply one_more_lemma in H.
    apply one_more_lemma in H0.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Lemma minus_lemma: (forall (e1_1 e1_2 e2_1 e2_2 : expr) (s : state), 
  equivalence_checker e1_1 e2_1 s &&
  equivalence_checker e1_2 e2_2 s = true -> Minus e1_1 e1_2 = Minus e2_1 e2_2).
  Proof.
    intros.
    apply Bool.andb_true_iff in H.
    destruct H.
    apply one_more_lemma in H.
    apply one_more_lemma in H0.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.


Lemma mul_lemma: (forall (e1_1 e1_2 e2_1 e2_2 : expr) (s : state), 
  equivalence_checker e1_1 e2_1 s &&
  equivalence_checker e1_2 e2_2 s = true -> Mul e1_1 e1_2 = Mul e2_1 e2_2).
  Proof.
    intros.
    apply Bool.andb_true_iff in H.
    destruct H.
    apply one_more_lemma in H.
    apply one_more_lemma in H0.
    rewrite H.
    rewrite H0.
    reflexivity.
Qed.

Lemma lemma1 :
  forall (e1 e2 : expr) (s : state), equivalence_checker e1 e2 s = true -> e1 = e2.
  Proof.
    intros e1 e2 s.
    unfold equivalence_checker.
    destruct e1, e2; try discriminate.
    - intros H.
      apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
    - apply plus_lemma.
    - apply minus_lemma.
    - apply mul_lemma.
    - intros H.
      apply String.eqb_eq in H.
      rewrite H.
      reflexivity.
Qed.

Lemma trivial_lemma1 :
  forall (e1 e2 : expr) (s : state), trivial_equivalence_checker e1 e2 s = true -> e1 = e2.
  Proof.
    intros e1 e2 s.
    unfold trivial_equivalence_checker.
    destruct e1, e2; try discriminate.
    - intros H.
      apply Nat.eqb_eq in H.
      rewrite H.
      reflexivity.
  Qed.

(* Prove that the equivalence checker is correct *)
Theorem equivalence_checker_correct:
  forall (e1 e2 : expr) (s : state), equivalence_checker e1 e2 s = true -> aequiv e1 e2 s.
Proof.
intros e1 e2.
unfold aequiv.
intros s.
intros H.
apply lemma1 in H.
rewrite H.
reflexivity.
Qed.

(* Prove that trivial equivalence checker is correct *)
Theorem trivial_equivalence_checker_correct:
  forall (e1 e2 : expr) (s : state), trivial_equivalence_checker e1 e2 s = true -> aequiv e1 e2 s.
Proof.
  intros e1 e2 s.
  unfold aequiv.
  intros H.
  apply trivial_lemma1 in H.
  rewrite H.
  reflexivity.
Qed.

(* A*(B+C) = AB + AC *)
Example distribute:
forall (a b c : expr) (s : state), 
  eval_expr (Mul a (Plus b c)) s =
  (eval_expr (Mul a b) s) + (eval_expr (Mul a c) s).
Proof.
 intros a b c s.
 simpl.
 ring.
 Qed.

(* Constant folding pass *)
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