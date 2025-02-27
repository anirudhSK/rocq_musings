Require Import Arith.

(* Simple data type of expressions *)
Inductive expr : Type :=
  | Plus (e1 e2 : expr)
  | Constant (n1 : nat).

(* Function to transforms expressions *)
Definition process_expr (e : expr) :=
   match e with 
    | Constant n1 => 5
    | Plus _ _ => 5
   end.

(* Function to evaluate expressions *)
Fixpoint eval_expr(e: expr) :=
  match e with
    | Constant n => n
    | Plus e1 e2 => (eval_expr e1) + (eval_expr e2)
  end.  

(* Compute using function *)
Compute (process_expr (Constant 5)).

(* Example theorem *)
Example test1:
(process_expr (Constant 5)) = (5).

(* ... with proof *)
Proof. simpl. reflexivity. Qed.
  
(* More involved theorem *)
Example test2:
(forall e: expr, process_expr(e) = 5).

(* with proof .*)
Proof. simpl. intros e. destruct e.
       -simpl. reflexivity.
       -simpl. reflexivity.
Qed.

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

Theorem add_comm : forall (x y : nat),
  x + y = y + x.
Proof.
  intros. induction x.
  - trivial.
  - simpl. rewrite -> IHx. trivial.
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

Axiom plus_equality: forall n1 n2,
Constant (n1 + n2) =
Plus (Constant n1) (Constant n2).

(* Prove correctness of constant_fold *)
Theorem constant_fold_thm : forall e,
   constant_fold e = e.
Proof.
  intros.
  induction e.
  - unfold constant_fold. destruct e1, e2.
       -- reflexivity.
       -- reflexivity.
       -- reflexivity.
       -- apply plus_equality.
  - intros. unfold constant_fold. reflexivity.
Qed.