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