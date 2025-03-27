From MyProject Require Export Expr.
From Coq Require Import Strings.String.

Inductive smt_expr : Type :=
  | SymConstant (n1 : nat)
  | SymBV (name: string)
  | Empty.

Definition symbolize_expr (e : expr) : smt_expr := Empty.

Definition sym_plus (e1 e2 : smt_expr) : smt_expr := Empty.

Definition check_sym_equality (e1 e2 : smt_expr) : bool := false.

Definition fn (e1 e2 : smt_expr) : bool.
Admitted. (* Is this reasonable programming in Coq? *)

Check fn.

(* And prove it equivalent in the same way ... *)
Definition smt_equivalence_checker (e1 e2 : expr) (s : state) : bool := 
  match e1, e2 with
    | Constant n1, Constant n2 => Nat.eqb n1 n2
    | Var name1, Var name2 => String.eqb name1 name2
    | Plus e11 e12, Plus e21 e22 => check_sym_equality (sym_plus (symbolize_expr e11) (symbolize_expr e12))
                                                       (sym_plus (symbolize_expr e21) (symbolize_expr e22))
    | _, _ => false
  end.