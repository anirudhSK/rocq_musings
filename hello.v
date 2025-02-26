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