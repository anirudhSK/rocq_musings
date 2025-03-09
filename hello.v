Require Import Arith.
Require Import Bool.
Require Import Coq.Logic.ClassicalFacts.  (* for excluded middle *)
From Coq Require Import Strings.String.
Open Scope string_scope.

(* A few more concepts to model:
local state, graphs of computations, concurrency,
locks, etc.*)
(* Here's something from SO on how to model graphs:
https://stackoverflow.com/questions/24753975/simple-graph-theory-proofs-using-coq
Definition graph : Type := {V : Type & V -> V -> bool}.
*)

(* Simple data type of expressions (or computations) *)
Inductive expr : Type :=
  | Constant (n1 : nat)
  | Plus (e1 e2 : expr)
  | Minus (e1 e2 : expr)
  | Mul (e1 e2 : expr)
  | Var (name : string).

Record pkt_proc_module : Set :=
   { local_state : nat;
      computation : expr}.

Check pkt_proc_module.

(* Graphs connect packet processing modules together. *)
(* Maybe use this definition of graphs with simplifications:
https://gist.github.com/andrejbauer/8dade8489dff8819c352e88f446154a1#file-graph-v-L16
*)

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

(* Simple theorem *)
Theorem equivalence_example:
  aequiv (Plus (Constant 5) (Var "x")) (Plus (Var "x") (Constant 5)) empty_state.
Proof.
  unfold aequiv.
  simpl.
  reflexivity.
Qed.

(* Simple equivalence checker *)
Definition equivalence_checker (e1 e2 : expr) (s : state) : bool := 
  Nat.eqb (eval_expr e1 s) (eval_expr e2 s).
(* TODO: Is this %nat a new coq thing? what is going on with intros H*)

(* Prove that the equivalence checker is correct *)
Theorem equivalence_checker_correct:
  forall (e1 e2 : expr) (s : state), equivalence_checker e1 e2 s = true -> aequiv e1 e2 s.
Proof.
intros e1 e2.
unfold aequiv.
unfold equivalence_checker.
intros s.
intros H. (* TODO: I don't get this intros H business *)
apply Nat.eqb_eq.
apply H.
Qed.

(* Prove that the equivalence checker is complete *)
Theorem equivalence_checker_complete:
  forall (e1 e2 : expr) (s : state), aequiv e1 e2 s -> equivalence_checker e1 e2 s = true.
Proof.
  intros e1 e2.
  unfold aequiv.
  intros s.
  intros H.
  unfold equivalence_checker.
  apply Nat.eqb_eq.
  apply H.
Qed.

(* TODO: How to simplify the proof below using excluded_middle? *)
(* The stuff below follows from law of excluded middle, which you can add as an axiom. *)
(* Prove that the equivalence checker is sound *)
Theorem equivalence_checker_sound:
  forall (e1 e2 : expr) (s : state), equivalence_checker e1 e2 s = false -> ~aequiv e1 e2 s.
Proof. 
  intros e1 e2.
  unfold aequiv.
  intros s.
  intros H.
  unfold equivalence_checker in H.
  apply Nat.eqb_neq in H.
  apply H.
Qed.

(* Evaluate expressions*)
Compute (eval_expr (Plus (Constant 5) (Constant 6)) empty_state).
Compute (eval_expr (Minus (Constant 6) (Constant 10)) empty_state).
Compute (eval_expr (Minus (Constant 6) (Constant 2)) empty_state).
Compute (eval_expr (Mul (Constant 6) (Constant 2)) empty_state).

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