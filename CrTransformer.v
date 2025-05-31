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
  | StatefulOp  (f : BinaryFunction) (s1 : StateVar) (arg2 : FunctionArgument) (* Where is output of statefulop stored? *)
  | StatelessOp (f : BinaryFunction) (h1 : Header)   (arg2 : FunctionArgument).

Inductive MatchActionRule :=
  | Seq (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp)
  | Par (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp).

Definition Transformer : Type := list MatchActionRule.

(* Example header *)
Definition example_header1 : Header := HeaderCtr "hdr1"%string.

(* An example transformer *)
Definition example_transformer : Transformer :=
  [
    Seq (HeaderCtr ("hdr1")) 0 7 [true; false; true; false; true; false; true; false]
      [StatefulOp (fun x y => x + y) (StateVarCtr ("state1")) (CtrlPlaneArg (CtrlPlaneConfigNameCtr "ctrl1"));
       StatelessOp (fun x y => x * y) (HeaderCtr ("hdr2")) (ConstantArg 42)];
    Par (HeaderCtr ("hdr2")) 0 7 [false; true; false; true; false; true; false; true]
      [StatelessOp (fun x y => x - y) (HeaderCtr ("hdr3")) (CtrlPlaneArg (CtrlPlaneConfigNameCtr "ctrl2"))]
  ].