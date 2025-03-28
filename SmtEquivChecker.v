From MyProject Require Export Expr.
From Coq Require Import Strings.String.

Inductive smt_expr : Type :=
  | SymConstant (n1 : nat)
  | SymBV (name: string)
  | SymPlus (se1 se2 : smt_expr)
  | SymMinus (se1 se2 : smt_expr)
  | Empty.

Fixpoint symbolize_expr (e : expr) : smt_expr :=
  match e with
  | Constant n => SymConstant n
  | Plus e1 e2 => SymPlus (symbolize_expr e1) (symbolize_expr e2)
  | Minus e1 e2 => SymMinus (symbolize_expr e1) (symbolize_expr e2)
  | Var name => SymBV name
  | _ => Empty
  end.

(* Function signature for Z3 equivalence checker *)
Parameter sym_checker :  smt_expr -> smt_expr -> bool.

(* Soundness of Z3: if the symbolic versions of 2 exprs are shown equivalent by z3, then the 2 exprs are equivalent *)
Axiom sound_smt_checker : forall e1 e2 : expr, sym_checker (symbolize_expr e1) (symbolize_expr e2) = true -> forall s, aequiv e1 e2 s.
(* Can make it return Option<bool>, true, false, or error *)
(* The most rigorous way of doing this is a syntax and semantics for SMT-LIB. Like the smt2 library for Lean. But may not buy you that much. *)
(* Think about this as a converter from a DSL into SMTLIB. Rather than using a Z3 or bitvector tactic (like with the smt2 tactic z3). *)

(* And prove it equivalent in the same way ... *)
Definition smt_equiv_checker (e1 e2 : expr) (s : state) : bool := 
  match e1, e2 with
    | Constant n1, Constant n2 => Nat.eqb n1 n2
    | Var name1, Var name2 => String.eqb name1 name2
    | Plus e11 e12, Plus e21 e22 => sym_checker (SymPlus (symbolize_expr e11) (symbolize_expr e12))
                                                (SymPlus (symbolize_expr e21) (symbolize_expr e22))
    | Minus e11 e12, Minus e21 e22 => sym_checker (SymMinus (symbolize_expr e11) (symbolize_expr e12) )
                                                  (SymMinus (symbolize_expr e21) (symbolize_expr e22))
    | _, _ => false
  end.