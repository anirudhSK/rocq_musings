(* Write out semantics for bitvectors in SMT,
show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import CrIdentifiers.
From MyProject Require Import MyInts.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVal.
From Coq.Strings Require Import String.

(* TODO: Look through K2 code *)
Inductive SmtBoolExpr : Type :=
    | SmtTrue
    | SmtFalse
    | SmtBoolNot (e : SmtBoolExpr)
    | SmtBoolAnd (e1 e2 : SmtBoolExpr)
    | SmtBoolOr (e1 e2 : SmtBoolExpr)
    | SmtBoolEq (e1 e2 : SmtArithExpr)
with SmtArithExpr : Type :=
    | SmtArithConst (value : CrInt_T)
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
    | SmtBitMod (e1 e2 : SmtArithExpr)
    | SmtArrSel (e1 : SmtArrExpr) (e2 : (*SmtPtrExpr*) SmtArithExpr) (e3 : SmtArithExpr)
(* with SmtPtrExpr : Type := *)
    | SmtPtrConst (e1 : CrPtr_T) (* e.g. 0x7fffffff0000 *)
    | SmtPtrVar (e1 : string) (* e.g. x *)
with SmtArrExpr : Type :=
    | SmtArrInit
    | SmtArrSt (e1 : SmtArrExpr) (e2 : (*SmtPtrExpr*) SmtArithExpr) (e3 : SmtArithExpr) (e4 : SmtArithExpr).

(* Evaluate a SMT Bool expression given a valuation *)
Fixpoint eval_smt_bool (e : SmtBoolExpr) (v : SmtValuation) : bool :=
    match e with
    | SmtTrue => true
    | SmtFalse => false
    | SmtBoolNot e' => negb (eval_smt_bool e' v)
    | SmtBoolAnd e1 e2 => andb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolOr e1 e2 => orb (eval_smt_bool e1 v) (eval_smt_bool e2 v)
    | SmtBoolEq e1 e2 => if (CrVal.eqb
      (eval_smt_arith e1 v) (eval_smt_arith e2 v)) then true else false
    end
with eval_smt_arith (e : SmtArithExpr) (v : SmtValuation) : CrVal :=
    match e with
    | SmtArithConst value => IntVal value
    | SmtArithVar name => match v name with
      | IntVal v' => IntVal v'
      | _ => ErrorVal
      end
    | SmtConditional cond then_expr else_expr =>
        if eval_smt_bool cond v 
        then (eval_smt_arith then_expr v)
        else (eval_smt_arith else_expr v)
    | SmtBitAdd e1 e2 => CrVal.add
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitSub e1 e2 => CrVal.sub
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitAnd e1 e2 => CrVal.and
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitOr e1 e2 => CrVal.or
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitXor e1 e2 => CrVal.xor
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitNot e => CrVal.not (eval_smt_arith e v)
    | SmtBitMul e1 e2 => CrVal.mul
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitDiv e1 e2 => CrVal.divu
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtBitMod e1 e2 => CrVal.modu
        (eval_smt_arith e1 v)
        (eval_smt_arith e2 v)
    | SmtArrSel e1 e2 e3 =>
        match CrVal.ld
            (eval_smt_mem e1 v)
            (eval_smt_arith e2 v)
            (eval_smt_arith e3 v)
        with
        | Legal v' => v'
        | Illegal => ErrorVal
        end
    | SmtPtrConst value => PtrVal value
    | SmtPtrVar name => match v name with
      | PtrVal v' => PtrVal v'
      | _ => ErrorVal
      end
    end
(* with eval_smt_ptr (e : SmtPtrExpr) (v : SmtValuation) : CrVal :=
    unwrap_val match e with
    | SmtPtrConst value => Legal (PtrVal value)
    | SmtPtrVar name => match v name with
      | PtrVal v' => Legal (PtrVal v')
      | _ => Illegal
      end
    | SmtPtrAdd e1 e2 => CrVal.add (eval_smt_ptr e1 v) (eval_smt_arith e2 v)
    end *)
with eval_smt_mem (e : SmtArrExpr) (v : SmtValuation) : Memory CrVal :=
    match e with
    | SmtArrInit => @CrVal.tabula_rasa CrVal
    | SmtArrSt e1 e2 e3 e4 => CrVal.st (eval_smt_mem e1 v) ((*eval_smt_ptr*) eval_smt_arith e2 v) (eval_smt_arith e3 v) (eval_smt_arith e4 v)
    end.

(* InitStatus: might be unnecessary and error prone because Z3 may not map 1-to-1 to this. *)