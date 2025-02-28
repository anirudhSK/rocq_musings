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

(* Distributivity of eval_expr
   with commutativity thrown in*)
Example test4:
(forall e1 e2: expr, (eval_expr e1) + (eval_expr e2) = (eval_expr (Plus e2 e1))).
Proof.
 intros e1 e2.
 destruct e1, e2; simpl; ring.
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

(* Check some types *)
Check constant_fold_thm.

Check forall e : expr, eval_expr (constant_fold e) = eval_expr e.
(* Why is this Prop? *)

Check constant_fold.

Check expr->expr.
(* Why is this Set? *)

Check Set.

Check Prop.
(* Set and Prop both are of type Type *)