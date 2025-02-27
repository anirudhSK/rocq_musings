Require Import Arith.

(* Simple data type of expressions *)
Inductive expr : Type :=
  | Plus (e1 e2 : expr)
  | Constant (n1 : nat).

(* Function to evaluate expressions *)
Fixpoint eval_expr(e: expr) :=
  match e with
    | Constant n => n
    | Plus e1 e2 => (eval_expr e1) + (eval_expr e2)
  end.  

(* Evaluate expressions*)
Compute (eval_expr (Plus (Constant 5) (Constant 6))).

(* Distributivity of eval_expr *)
Example test3:
(forall e1 e2: expr, (eval_expr e1) + (eval_expr e2) = (eval_expr (Plus e1 e2))).
Proof.
 intros e1 e2.
 destruct e1, e2.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
 - simpl. reflexivity.
Qed.

(* Distributivity of eval_expr
   with commutativity thrown in*)
Example test4:
(forall e1 e2: expr, (eval_expr e1) + (eval_expr e2) = (eval_expr (Plus e2 e1))).
Proof.
 intros e1 e2.
 destruct e1, e2.
 - simpl. ring.
 - simpl. ring.
 - simpl. ring.
 - simpl. ring.
 Qed.

(* Constant folding pass *)
Definition constant_fold(e : expr):=
  match e with
  | Plus (Constant n1) (Constant n2) => Constant (n1 + n2)
  | _ => e
end.

(* Prove correctness of constant_fold *)
Theorem constant_fold_thm : forall e,
   eval_expr (constant_fold e) =  eval_expr e.
Proof.
  intros.
  destruct e. (* TODO: induction e also seems to work here, ask JoeT *)
  - unfold constant_fold. destruct e1, e2.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- unfold eval_expr. reflexivity.
  - intros. unfold constant_fold. reflexivity.
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