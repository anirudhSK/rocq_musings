Require Import Arith.

(* Simple data type of expressions *)
Inductive expr : Type :=
  | Constant (n1 : nat)
  | Plus (e1 e2 : expr)
  | Minus (e1 e2 : expr)
  | Mul (e1 e2 : expr).

(* Function to evaluate expressions *)
Fixpoint eval_expr(e: expr) :=
  match e with
    | Constant n => n
    | Plus e1 e2 => (eval_expr e1) + (eval_expr e2)
    | Minus e1 e2 => (eval_expr e1) - (eval_expr e2)
    | Mul e1 e2 => (eval_expr e1) * (eval_expr e2)
  end.  

(* Evaluate expressions*)
Compute (eval_expr (Plus (Constant 5) (Constant 6))).
Compute (eval_expr (Minus (Constant 6) (Constant 10))).
Compute (eval_expr (Minus (Constant 6) (Constant 2))).
Compute (eval_expr (Mul (Constant 6) (Constant 2))).

(* A*(B+C) = AB + AC *)
Example distribute:
forall a b c: expr, 
  eval_expr (Mul a (Plus b c)) =
  eval_expr (Mul a b) + eval_expr (Mul a c).
Proof.
 intros a b c.
 destruct a, b, c; simpl; ring.
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
Theorem constant_fold_thm : forall e,
   eval_expr (constant_fold e) =  eval_expr e.
Proof.
  destruct e. (* TODO: induction e also seems to work here, ask JoeT *)
  - reflexivity. (* Why do you not need an unfold constant_fold here? *)
  - destruct e1, e2; reflexivity.
  - destruct e1, e2; reflexivity.
  - destruct e1, e2; reflexivity.
Qed.