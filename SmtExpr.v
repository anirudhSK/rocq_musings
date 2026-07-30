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
    (* Two regions hold the same thing over their first [n] cells.

       [n] is here for the SEMANTICS, the mirror image of the [len] on
       [SmtArrSel] being there for the Z3 lowering: [eval_smt_bool] has to
       return a bool, so it needs a finite bound to fold over, and the region's
       own [arr_len] is a runtime value.  The Z3 lowering ignores [n] and emits
       one extensional array equality -- see [SOUNDNESS.md] for why that is the
       same statement on the terms this checker builds, and what would break it. *)
    | SmtArrEq (n : nat) (a1 a2 : SmtArrExpr)
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
    (* Read offset [idx] of region [a].  Out of bounds is [ErrorVal], where the
       bound is the region's declared length -- see [smt_arr_len]. *)
    | SmtArrSel (a : SmtArrExpr) (idx : SmtArithExpr)
with SmtArrExpr : Type :=
    (* An undeclared region: reads are out of bounds, writes are dropped. *)
    | SmtArrInit
    (* A region's contents on entry, as a free array variable. *)
    | SmtArrVar (name : string) (len : uint64)
    | SmtArrSt (a : SmtArrExpr) (idx : SmtArithExpr) (v : SmtArithExpr)
    (* Path merging.  [SmtConditional] only builds arith expressions, so
       merging two versions of a region needs its own conditional. *)
    | SmtArrIte (cond : SmtBoolExpr) (a1 a2 : SmtArrExpr).

(* Do two loads agree?  [ld_arr] is partial, and an out-of-bounds read on both
   sides counts as agreement -- the same convention the concrete semantics uses
   when it turns [Illegal] into [ErrorVal]. *)
Definition check_crval_eqb (x y : Check_T CrVal) : bool :=
  match x, y with
  | Legal a, Legal b => CrVal.eqb a b
  | Illegal, Illegal => true
  | _, _ => false
  end.

(* Cell-by-cell agreement of two regions over their first [n] cells. *)
Definition arr_agree_upto (n : nat) (a1 a2 : @Array CrVal) : bool :=
  List.forallb
    (fun i => check_crval_eqb (ld_arr a1 (mk_int u64 (Z.of_nat i)))
                              (ld_arr a2 (mk_int u64 (Z.of_nat i))))
    (List.seq 0 n).

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
    | SmtBoolVar name => match sv_ints v name with
      | IntVal a _ => negb (Integers.eq a Integers.zero)
      | _ => false
      end
    | SmtArrEq n a1 a2 =>
        arr_agree_upto n (eval_smt_mem a1 v) (eval_smt_mem a2 v)
    end
with eval_smt_arith (e : SmtArithExpr) (v : SmtValuation) : CrVal :=
    match e with
    | SmtArithConst val ty => mk_int ty (unsigned val)
    | SmtUninit => UninitVal
    | SmtArithVar name => match sv_ints v name with
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
    (* An out-of-bounds (or undeclared-region) read is [ErrorVal], not a
       rejection: see the totality argument on [CrTransformer.LoadOp].  The
       [len] on the node is redundant with the region's own [arr_len] here --
       it exists for the Z3 lowering, which has no [arr_len] to consult. *)
    | SmtArrSel a idx =>
        match CrVal.ld_arr (eval_smt_mem a v) (eval_smt_arith idx v) with
        | Legal v' => v'
        | Illegal => ErrorVal
        end
    end
with eval_smt_mem (e : SmtArrExpr) (v : SmtValuation) : @Array CrVal :=
    match e with
    | SmtArrInit => Unallocated
    (* The model supplies the bytes; the declaration supplies the length. *)
    | SmtArrVar name len => region_with_len len (sv_arrs v name)
    (* An out-of-bounds write is dropped rather than invalidating the region,
       the store-side mirror of [SmtArrSel]'s [ErrorVal].  Z3's [store] is
       total, but a total store is observationally equal to this one: the only
       index it differs at is out of bounds, and every read of an out-of-bounds
       index is guarded, as is the checker's memory-equality conjunct. *)
    | SmtArrSt a idx val =>
        let a' := eval_smt_mem a v in
        match CrVal.st_arr a' (eval_smt_arith idx v) (eval_smt_arith val v) with
        | Legal a'' => a''
        | Illegal => a'
        end
    | SmtArrIte cond a1 a2 =>
        if eval_smt_bool cond v then eval_smt_mem a1 v else eval_smt_mem a2 v
    end.

(* The declared length of the region an array expression denotes.  A store
   preserves it and a path merge joins two versions of the same region, so it
   is fixed by the leaf.  The Z3 lowering uses this to emit the bounds guard
   that [ld_arr] applies here: Z3's [select] is total, so without it the solver
   and the concrete semantics would disagree on every out-of-bounds read. *)
Fixpoint smt_arr_len (a : SmtArrExpr) : uint64 :=
  match a with
  | SmtArrInit => repr 0
  | SmtArrVar _ len => len
  | SmtArrSt a' _ _ => smt_arr_len a'
  | SmtArrIte _ a1 _ => smt_arr_len a1
  end.

Record ConditionalVal (T : Type) := {
  cvc : SmtBoolExpr;
  cvv : T;
}.

Arguments cvc {T} _.
Arguments cvv {T} _.
