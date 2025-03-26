From MyProject Require Export Expr.

(* Slightly more complex equivalence checker *)
Fixpoint equivalence_checker (e1 e2 : expr) (s : state) : bool := 
  match e1, e2 with
    | Constant n1, Constant n2 => Nat.eqb n1 n2
    | Var name1, Var name2 => String.eqb name1 name2
    | Plus e11 e12, Plus e21 e22 => andb (equivalence_checker e11 e21 s) (equivalence_checker e12 e22 s)
    | Minus e11 e12, Minus e21 e22 => andb (equivalence_checker e11 e21 s) (equivalence_checker e12 e22 s)
    | Mul e11 e12, Mul e21 e22 => andb (equivalence_checker e11 e21 s) (equivalence_checker e12 e22 s)
    | _, _ => false
  end.

Definition trivial_equivalence_checker (e1 e2 : expr) (s : state) : bool := 
  match e1, e2 with
    | Constant n1, Constant n2 => Nat.eqb n1 n2
    | _, _ => false
  end.