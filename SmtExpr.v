(* Write out semantics for bitvectors in SMT,
show that a single hdr_op evaluation can be converted to the appropriate SMT formula in Z3 *)
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVal.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From Stdlib.Strings Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

(* TODO: Look through K2 code *)
Inductive SmtBoolExpr : Type :=
    | SmtTrue
    | SmtFalse
    | SmtBoolNot (e : SmtBoolExpr)
    | SmtBoolAnd (e1 e2 : SmtBoolExpr)
    | SmtBoolOr (e1 e2 : SmtBoolExpr)
    | SmtBoolEq (e1 e2 : SmtArithExpr)
    | SmtBoolLt (e1 e2 : SmtArithExpr)
    (* A free boolean variable (e.g. a single symbolic packet bit).  Evaluated
       via the valuation, interpreting a nonzero stored value as [true]. *)
    | SmtBoolVar (name : string)
with SmtArithExpr : Type :=
    | SmtArithConst (val : uint64) (ty : CrIntType)
    | SmtUninit  (* the uninitialized value; evaluates to UninitVal *)
    | SmtArithVar (name : string)
    (* The [u64] value denoted by a run of bits, MSB first (head = most
       significant).  A packet field extraction produces one of these; it lowers
       to a bitvector [concat] in Z3 (free), rather than an arithmetic
       assembly chain. *)
    | SmtBitsToInt (bits : list SmtBoolExpr)
    (* Extract bits [lo, hi) of a sub-expression (LSB-indexed) into a [u64];
       mirrors [CrVal.slice_val].  Used for parser [select] sub-field matches. *)
    | SmtBitSlice (lo hi : nat) (e : SmtArithExpr)
    | SmtConditional (cond : SmtBoolExpr) (then_expr else_expr : SmtArithExpr)
    (* Cast a sub-expression from one int type to another: the operand must
       already be typed [from], the result is typed [to]. *)
    | SmtCast (from to : CrIntType) (e : SmtArithExpr)
    (* Arithmetic / bitwise operations carry the type they act at; both operands
       must already carry that type, else the result is ErrorVal. *)
    | SmtBitAdd (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitSub (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitAnd (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitOr  (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitXor (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitNot (e : SmtArithExpr)
    | SmtBitMul (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitDiv (ty : CrIntType) (e1 e2 : SmtArithExpr)
    | SmtBitMod (ty : CrIntType) (e1 e2 : SmtArithExpr)
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
    | SmtBoolLt e1 e2 => CrVal.ltb
      (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBoolVar name => match v name with
      | IntVal a _ => negb (Integers.eq a Integers.zero)
      | _ => false
      end
    end
with eval_smt_arith (e : SmtArithExpr) (v : SmtValuation) : CrVal :=
    match e with
    | SmtArithConst val ty => mk_int ty (unsigned val)
    | SmtUninit => UninitVal
    | SmtArithVar name => match v name with
      | IntVal a t => IntVal a t
      | _ => ErrorVal
      end
    | SmtBitsToInt bits =>
        (* Fold the bits MSB first as [acc := 2*acc + bit]; the [u64] result
           agrees with the old [assemble_bits_symbolic] assembly. *)
        mk_int u64
          ((fix go (bs : list SmtBoolExpr) (acc : Z) {struct bs} : Z :=
              match bs with
              | nil => acc
              | b :: rest =>
                  go rest (Z.add (Z.mul 2 acc)
                                 (if eval_smt_bool b v then 1%Z else 0%Z))
              end) bits 0%Z)
    | SmtBitSlice lo hi e => slice_val lo hi (eval_smt_arith e v)
    | SmtConditional cond then_expr else_expr =>
        if eval_smt_bool cond v
        then (eval_smt_arith then_expr v)
        else (eval_smt_arith else_expr v)
    | SmtCast from to e => cast from to (eval_smt_arith e v)
    | SmtBitAdd ty e1 e2 => add_at  ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitSub ty e1 e2 => sub_at  ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitAnd ty e1 e2 => and_at  ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitOr  ty e1 e2 => or_at   ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitXor ty e1 e2 => xor_at  ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitNot e => CrVal.not (eval_smt_arith e v)
    | SmtBitMul ty e1 e2 => mul_at  ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitDiv ty e1 e2 => divu_at ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
    | SmtBitMod ty e1 e2 => modu_at ty (eval_smt_arith e1 v) (eval_smt_arith e2 v)
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
with eval_smt_mem (e : SmtArrExpr) (v : SmtValuation) : Memory CrVal :=
    match e with
    | SmtArrInit => @CrVal.tabula_rasa CrVal
    | SmtArrSt e1 e2 e3 e4 => CrVal.st (eval_smt_mem e1 v) ((*eval_smt_ptr*) eval_smt_arith e2 v) (eval_smt_arith e3 v) (eval_smt_arith e4 v)
    end.

Record ConditionalVal (T : Type) := {
  cvc : SmtBoolExpr;
  cvv : T;
}.

Arguments cvc {T} _.
Arguments cvv {T} _.
