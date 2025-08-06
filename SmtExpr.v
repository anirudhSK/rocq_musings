(* Write out semantics for bitvectors in SMT,
   show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import CrIdentifiers.
From Coq.Strings Require Import String.

(* Note that these strings may or may not have a one-to-one correspondence with
  identifiers in the CrDsl program. *)
(* Currently only need valuations from strings to uint8
  because there are no primitive bool variables within the IR.
  Expressions can still be bools though (for conditionals, equalities, etc.) *)
Definition SmtValuation := string -> (InitStatus uint8).

Inductive SmtBoolExpr : Type :=
    | SmtTrue
    | SmtFalse
    | SmtBoolNot (e : SmtBoolExpr)
    | SmtBoolAnd (e1 e2 : SmtBoolExpr)
    | SmtBoolOr (e1 e2 : SmtBoolExpr)
    | SmtBoolEq (e1 e2 : SmtArithExpr)
with SmtArithExpr : Type :=
    | SmtConst (value : uint8)
    | SmtArithVar (name : string)
    | SmtConditional (cond : SmtBoolExpr) (then_expr else_expr : SmtArithExpr)
    (* Arithmetic operations *)
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

(* Evaluate a SMT Bool expression given a valuation *)
Fixpoint eval_smt_bool (e : SmtBoolExpr) (v : SmtValuation) : bool :=
    match e with
    | SmtTrue => true
    | SmtFalse => false
    | SmtBoolNot e' => negb (eval_smt_bool e' v)
    | SmtBoolAnd e1 e2 => andb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolOr e1 e2 => orb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolEq e1 e2 => if (initstatus_uint8_equal (eval_smt_arith e1 v) (eval_smt_arith e2 v)) then true else false
    end
with eval_smt_arith (e : SmtArithExpr) (v : SmtValuation) : (InitStatus uint8) :=
    match e with
    | SmtConst value => Initialized uint8 value
    | SmtArithVar name => v name
    | SmtConditional cond then_expr else_expr => 
        if eval_smt_bool cond v 
        then eval_smt_arith then_expr v 
        else eval_smt_arith else_expr v
    | SmtBitAdd e1 e2 => InitStatus.add (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitSub e1 e2 => InitStatus.sub (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitAnd e1 e2 => InitStatus.and (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitOr e1 e2 =>  InitStatus.or (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitXor e1 e2 => InitStatus.xor (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitNot e =>     InitStatus.not (eval_smt_arith e v)
    | SmtBitMul e1 e2 => InitStatus.mul (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitDiv e1 e2 => InitStatus.divu (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitMod e1 e2 => InitStatus.modu (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    end.
(* InitStatus: might be unnecessary and error prone because Z3 may not map 1-to-1 to this. *)