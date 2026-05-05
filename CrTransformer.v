(* Transformer section below *)

(* Import necessary modules *)
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.
From Stdlib Require Import Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import MyInts.
From MyProject Require Import CrVal.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

Inductive FunctionArgument :=
  | CtrlPlaneArg (c : Ctrl)
  | HeaderArg (h : Header)
  | ConstantArg (n : CrInt_T) (* TODO: Can have constant ptrs as well *)
  | StatefulArg (s : State).

(* A CmpOp is a comparison primitive used in Guards.
   Only Eq and Lt are exposed; Gt/Le/Ge/Ne are derived by swapping operands
   (and, when GNot/GOr land later, wrapping). *)
Inductive CmpOp :=
  | CmpEq
  | CmpLt.

(* A Guard is a per-rule conditional gate, conjoined with the rule's
   MatchPattern. GTrue is the no-op guard (preserves prior semantics). *)
Inductive Guard :=
  | GTrue
  | GCmp (op : CmpOp) (a1 a2 : FunctionArgument).

(* A BinaryOp takes two uint8 arguments and returns another uint8 *)
Inductive BinaryOp :=
  | AddOp
  | SubOp (* In modulo u8 *)
  | AndOp
  | OrOp
  | XorOp
  | MulOp 
  | DivOp 
  | ModOp.

(* Define the header operations *)
Inductive HdrOp :=
  | StatefulOp  (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : State)
  | StatelessOp (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : Header).

(* Define MatchPattern as a list of header, pattern pairs,
   where patterns are uint8 and headers contain uint8 values,
   hence both can be compared. TODO: Need to handle wildcards. *)
Definition MatchPattern := list (Header * CrInt_T). (* TODO: might have to change *)

Inductive SeqRule :=
  | SeqCtr (match_pattern : MatchPattern) (guard : Guard) (action : list HdrOp).

(* Extract targets out of a HdrOp *)
Definition extract_targets (op : HdrOp) : (list State) * (list Header) := 
  match op with
  | StatefulOp _ _ _ target => ([target], [])
  | StatelessOp _ _ _ target => ([], [target])
  end.

(* Extract all targets from a list of HdrOps *)
Definition extract_all_targets (ops : list HdrOp) : (list State) * (list Header) :=
  List.fold_left (fun acc op => 
    let (state_vars, headers) := extract_targets op in
    (state_vars ++ fst acc, headers ++ snd acc)) ops ([], []).

(* TODO: Add masks and don't care bits *)
Inductive ParRule :=
  | ParCtr (match_pattern : MatchPattern) (guard : Guard)
    (action : {l : list HdrOp | NoDup (fst (extract_all_targets l)) /\
                                NoDup (snd (extract_all_targets l))}).

Inductive MatchActionRule :=
  | Seq (s : SeqRule)
  | Par (p : ParRule).

Definition Transformer : Type := list MatchActionRule.