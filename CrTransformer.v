(* Transformer section below *)

(* Import necessary modules *)
Require Import List.
Require Import ZArith.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrProgramState.

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

Inductive MatchActionRule :=
  | Seq (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool) (action : list HdrOp)
  | Par (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool) (action : list HdrOp).

Definition Transformer : Type := list MatchActionRule.