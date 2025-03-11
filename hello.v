Require Import Arith.
Require Import Bool.
From Coq Require Import Strings.String.
Open Scope string_scope.

(* Simple data type of expressions (or computations) *)
Inductive expr : Type :=
  | Constant (n1 : nat)
  | Plus (e1 e2 : expr)
  | Minus (e1 e2 : expr)
  | Mul (e1 e2 : expr)
  | Var (name : string).


  (* State of the machine with current values of variables *)
Definition state := string -> nat.

(* Empty state with no current values *)
Definition empty_state (s : string) :=
  match s with
    | _ =>0
  end.

(* Function to evaluate expressions *)
Fixpoint eval_expr (e: expr) (s : state) :=
  match e with
    | Constant n => n
    | Plus e1 e2 => (eval_expr e1 s) + (eval_expr e2 s)
    | Minus e1 e2 => (eval_expr e1 s) - (eval_expr e2 s)
    | Mul e1 e2 => (eval_expr e1 s) * (eval_expr e2 s)
    | Var name => s name
  end.

(* Expression equivalence *)
Definition aequiv (a1 a2 : expr) (s : state) : Prop :=
    eval_expr a1 s = eval_expr a2 s.

(* Simple equivalence checker *)
Fixpoint equivalence_checker (e1 e2 : expr) (s : state) : bool := 
  match e1, e2 with
    | Constant n1, Constant n2 => Nat.eqb n1 n2
    | Var name1, Var name2 => String.eqb name1 name2
    | Plus e11 e12, Plus e21 e22 => andb (equivalence_checker e11 e21 s) (equivalence_checker e12 e22 s)
    | _, _ => false
  end.

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
      specialize (IHe1_1 e2_1 H).
      rewrite IHe1_1.
      specialize (IHe1_2 e2_2 H0).
      rewrite IHe1_2.
      reflexivity.
    (* TODO: Maybe ask for help here ... *)
    - apply String.eqb_eq in H.
      rewrite H.
      reflexivity.
  Qed.

Lemma rec_lemma: (forall (e1_1 e1_2 e2_1 e2_2 : expr) (s : state), 
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
    - apply rec_lemma.
    - intros H.
      apply String.eqb_eq in H.
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
  (* induction e also seems to work here:
   See https://www.cs.cornell.edu/courses/cs3110/2018sp/a5/coq-tactics-cheatsheet.html#induction
   and https://www.reddit.com/r/Coq/comments/186hyk8/can_i_always_replace_destruct_with_induction/?rdt=33660
  *)
Qed.