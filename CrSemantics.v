(* Provide semantics for CrDsl using inductive propositions *)
Inductive my_favorite_numbers : nat -> Prop :=
| ILike17 : my_favorite_numbers 17
| ILike23 : my_favorite_numbers 23
| ILike42 : my_favorite_numbers 42.

Check my_favorite_numbers. 
Check ILike17.
Check my_favorite_numbers 17.