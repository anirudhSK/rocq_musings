(* Write out semantics for bitvectors in SMT,
   show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import CrIdentifiers.
From Coq.Strings Require Import String.

(* Note that these strings may or may not have a one-to-one correspondence with
  identifiers in the CrDsl program. *)
(* Currently only need valuations from strings to uint8 because there are no bools in IR. *)
(* TODO: Does that sound reasonable overall? *)
Definition SmtValuation := string -> uint8.

(* Basic starting point of Smt expressions, just have 8 bit ands, ors, and nots.
   Can express everything a sat solver cares about by just setting 7 bits to zero.
   so seems complete in some sense.*)
Inductive SmtArithExpr :=
    | SmtConst (value : uint8)
    | SmtArithVar (name : string)
    | SmtBitAdd (e1 e2 : SmtArithExpr)
    | SmtBitSub (e1 e2 : SmtArithExpr) (* Note: this is modulo 256 subtraction *)
    (* Bitwise operations *)
    | SmtBitAnd (e1 e2 : SmtArithExpr)
    | SmtBitOr (e1 e2 : SmtArithExpr)
    | SmtBitXor (e1 e2 : SmtArithExpr)
    | SmtBitNot (e : SmtArithExpr)
    | SmtBitMul (e1 e2 : SmtArithExpr)
    | SmtBitDiv (e1 e2 : SmtArithExpr)
    | SmtBitMod (e1 e2 : SmtArithExpr).

Inductive SmtBoolExpr :=
    | SmtTrue
    | SmtFalse
    | SmtBoolNot (e : SmtBoolExpr)
    | SmtBoolAnd (e1 e2 : SmtBoolExpr)
    | SmtBoolOr (e1 e2 : SmtBoolExpr)
    | SmtBoolEq  (e1 e2 : SmtArithExpr).   

(* Provide semantics for the SmtArithExpr above using the uint8 functions from Integer.v *)
Fixpoint eval_smt_arith (e : SmtArithExpr) (v : SmtValuation) : uint8 :=
    match e with
    | SmtConst value => value
    | SmtArithVar name => v name
    (* Note: we assume that the valuation v is well-formed,
       i.e., it contains all the variables that appear in the expression *)
    | SmtBitAdd e1 e2 => add (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitSub e1 e2 => sub (eval_smt_arith e1 v) (eval_smt_arith e2 v) (* Modulo 256 subtraction *)
    (* Bitwise operations *)
    | SmtBitAnd e1 e2 => and (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitOr e1 e2 => or (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitXor e1 e2 => xor  (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitNot e => not (eval_smt_arith e v)
    | SmtBitMul e1 e2 => mul (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitDiv e1 e2 => divu  (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitMod e1 e2 => modu  (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    end.

Fixpoint eval_smt_bool (e : SmtBoolExpr) (v : SmtValuation) : bool :=
    match e with
    | SmtTrue => true
    | SmtFalse => false
    | SmtBoolNot e' => negb (eval_smt_bool e' v)
    | SmtBoolAnd e1 e2 => andb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolOr e1 e2 => orb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolEq e1 e2 => if (eq (eval_smt_arith e1 v) (eval_smt_arith e2 v)) then true else false
    end.