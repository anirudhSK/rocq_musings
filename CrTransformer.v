(* Transformer section below *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export Map.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

Inductive FunctionArgument :=
  | CtrlPlaneArg (c : CtrlPlaneConfigName)
  | HeaderArg (h : Header)
  | ConstantArg (n : nat)
  | StatefulArg (s : StateVar).

(* lookup a function's argument *)
Definition lookup_function_argument (arg : FunctionArgument) (valuation : Valuation) : option nat :=
  match arg with
  | CtrlPlaneArg c => lookup (valuation.(ctrl_plane_map)) c
  | HeaderArg h =>    lookup (valuation.(header_map)) h
  | ConstantArg n => Some n
  | StatefulArg s =>  lookup (valuation.(state_var_map)) s
  end.

Definition function_argument_to_nat (arg : FunctionArgument) (valuation : Valuation) : nat :=
  match lookup_function_argument arg valuation with
  | Some n => n
  | None => 0 (* TODO: or any default value or error handling as appropriate *)
  end.

(* A BinaryFunction takes two nat arguments and returns another nat *)
Definition BinaryFunction : Type := (nat -> nat -> nat).

Inductive HdrOp :=
  | StatefulOp  (f : BinaryFunction) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : StateVar)
  | StatelessOp (f : BinaryFunction) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : Header).

Inductive MatchActionRule :=
  | Seq (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp)
  | Par (h : Header) (start_index : nat) (end_index : nat) (pat : list bool) (action : list HdrOp).

Definition Transformer : Type := list MatchActionRule.

(* Example header *)
Definition example_header1 : Header := HeaderCtr "hdr1"%string.

(* An example transformer *)
Definition example_transformer : Transformer :=
  [
    Seq example_header1 0 10 [true; false; true] 
      [StatefulOp (fun x y => x + y) (HeaderArg example_header1) (ConstantArg 5) (StateVarCtr "state1"%string)];
    Par example_header1 0 10 [false; true; false] 
      [StatelessOp (fun x y => x * y) (HeaderArg example_header1) (ConstantArg 3) (HeaderCtr "hdr2"%string)]
  ].