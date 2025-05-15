(* Transformer section below *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

Inductive FunctionArgument :=
  | CtrlPlaneArg (c : CtrlPlaneConfigName)
  | HeaderArg (h : Header)
  | ConstantArg (n : nat).

(* A BinaryFunction takes two nat arguments and returns another nat *)
Definition BinaryFunction : Type := (nat -> nat -> nat).

Inductive HdrOp :=
  | StatefulOp  (f : BinaryFunction) (s1 : StateVar) (arg2 : FunctionArgument)
  | StatelessOp (f : BinaryFunction) (h1 : Header)   (arg2 : FunctionArgument).

Inductive MatchActionRule :=
  | Seq (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp)
  | Par (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp).

Definition Transformer : Type := list MatchActionRule.