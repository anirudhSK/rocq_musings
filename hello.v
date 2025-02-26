Inductive expr : Type :=
  | Plus (e1 e2 : expr)
  | Constant (n1 : nat).

Definition process_expr (e : expr) :=
   match e with 
    | Constant n1 => 5
    | Plus _ _ => 5
   end.

