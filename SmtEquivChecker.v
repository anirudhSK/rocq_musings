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
Parameter sym_checker :  smt_expr -> smt_expr -> state -> bool.

Definition smt_equiv_checker (e1 e2 : expr) (s : state) : bool := 
  sym_checker (symbolize_expr e1) (symbolize_expr e2) s.

(* Soundness of Z3: if the symbolic versions of 2 exprs are shown equivalent by z3, then the 2 exprs are equivalent *)
Axiom sound_smt_checker : forall (e1 e2 : expr) (s : state), smt_equiv_checker e1 e2 s = true -> aequiv e1 e2 s.

(* sym_checker satisfies reflexivity at the least; think we still need this. *)
Axiom reflexive_sym_checker:  forall (e: smt_expr) (s: state), sym_checker e e s = true.

(* If two exprs eval to the same thing, then the sym_checker will say true *)
Axiom eval_sym_checker: forall (e1 e2: expr) (s: state), (eval_expr e1 s) = (eval_expr e2 s) -> smt_equiv_checker e1 e2 s = true.

(* Can make it return Option<bool>, true, false, or error *)
(* The most rigorous way of doing this is a syntax and semantics for SMT-LIB. Like the smt2 library for Lean. But may not buy you that much. *)
(* Think about this as a converter from a DSL into SMTLIB. Rather than using a Z3 or bitvector tactic (like with the smt2 tactic z3). *)