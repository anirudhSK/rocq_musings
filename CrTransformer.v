(* Transformer section below *)

(* Import necessary modules *)
From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

(* Where an operand's value comes from. Operands are width-free: the width at
   which an operand is read is fixed by the operation that consumes it. *)
Inductive Operand :=
  | OpCtrlPlane (c : Ctrl)
  | OpHeader (h : Header)
  | OpConst (n : CrInt_T) (* TODO: Can have constant ptrs as well *)
  | OpStateful (s : State).

Inductive CmpOp :=
  | CmpEq
  | CmpGt
  | CmpLt.

(* A BinaryOp's operands are width-free; the operation's [CrIntType] (carried
   on the HdrOp) fixes the width it reads and writes at. *)
Inductive BinaryOp :=
  | AddOp
  | SubOp (* In modulo u8 *)
  | AndOp
  | OrOp
  | XorOp
  | MulOp 
  | DivOp 
  | ModOp.

(* Define the header operations.

   Arithmetic ops carry a single [CrIntType] [ty]: both operands are read at
   [ty] and the result is produced at [ty] (akin to the b/w/l/q suffix on a
   single instruction). Cast ops convert an operand from one int type to
   another ([from] tells the cast which bits are meaningful / how to extend,
   [to] the target); both widths are explicit because the value itself no
   longer records one.  (See the [prog_cast_*] programs in [TestPrograms.v] for
   worked examples.) *)
Inductive HdrOp :=
  | StatefulOp   (f : BinaryOp) (ty : CrIntType) (arg1 : Operand) (arg2 : Operand) (target : State)
  | StatelessOp  (f : BinaryOp) (ty : CrIntType) (arg1 : Operand) (arg2 : Operand) (target : Header)
  | CastStateOp  (from : CrIntType) (to : CrIntType) (arg : Operand) (target : State)
  | CastHeaderOp (from : CrIntType) (to : CrIntType) (arg : Operand) (target : Header).

(* Define MatchPattern as a list of header, pattern pairs.  Patterns and header
   values are both 64-bit [CrInt]s, compared full-width (a match carries no
   width of its own). TODO: Need to handle wildcards. *)
Inductive MatchValue :=
| MatchConst (k : CrInt_T)
| MatchHeader (h : Header).
Definition MatchPattern := list (Header * CmpOp * MatchValue).

Inductive SeqRule :=
  | SeqCtr (match_pattern : MatchPattern) (action : list HdrOp).

(* Extract targets out of a HdrOp *)
Definition extract_targets (op : HdrOp) : (list State) * (list Header) :=
  match op with
  | StatefulOp _ _ _ _ target => ([target], [])
  | StatelessOp _ _ _ _ target => ([], [target])
  | CastStateOp _ _ _ target => ([target], [])
  | CastHeaderOp _ _ _ target => ([], [target])
  end.

(* Extract all targets from a list of HdrOps *)
Definition extract_all_targets (ops : list HdrOp) : (list State) * (list Header) :=
  List.fold_left (fun acc op => 
    let (state_vars, headers) := extract_targets op in
    (state_vars ++ fst acc, headers ++ snd acc)) ops ([], []).

(* TODO: Add masks and don't care bits *)
Inductive ParRule :=
  | ParCtr (match_pattern : MatchPattern)
    (action : {l : list HdrOp | NoDup (fst (extract_all_targets l)) /\
                                NoDup (snd (extract_all_targets l))}).

Inductive MatchActionRule :=
  | Seq (s : SeqRule)
  | Par (p : ParRule).

Definition Transformer : Type := list MatchActionRule.