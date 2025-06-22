(* Transformer section below *)

(* Import necessary modules *)
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrProgramState.
From MyProject Require Export NoDupLists.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

Inductive FunctionArgument :=
  | CtrlPlaneArg (c : CtrlPlaneConfigName)
  | HeaderArg (h : Header)
  | ConstantArg (n : uint8)
  | StatefulArg (s : StateVar).

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
  | StatefulOp  (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : StateVar)
  | StatelessOp (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : Header).

Inductive SeqRule :=
  | SeqCtr (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool) (action : list HdrOp).


(* Extract targets out of a HdrOp *)
Definition extract_targets (op : HdrOp) : (list StateVar) * (list Header) := 
  match op with
  | StatefulOp _ _ _ target => ([target], [])
  | StatelessOp _ _ _ target => ([], [target])
  end.

(* Extract all targets from a list of HdrOps *)
Definition extract_all_targets (ops : list HdrOp) : (list StateVar) * (list Header) :=
  List.fold_left (fun acc op => 
    let (state_vars, headers) := extract_targets op in
    (state_vars ++ fst acc, headers ++ snd acc)) ops ([], []).

Inductive ParRule :=
  | ParCtr (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool)
    (action : {l : list HdrOp | NoDup (fst (extract_all_targets l)) /\
                                NoDup (snd (extract_all_targets l))}).

Inductive MatchActionRule :=
  | Seq (s : SeqRule)
  | Par (p : ParRule).

Definition Transformer : Type := list MatchActionRule.