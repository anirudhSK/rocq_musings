(* Transformer section below *)

(* Import necessary modules *)
Require Import List.
Require Import ZArith.
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
  | ConstantArg (n : uint8)
  | StatefulArg (s : StateVar).

(* lookup a function's argument *)
Definition lookup_function_argument (arg : FunctionArgument) (valuation : Valuation) : option uint8 :=
  match arg with
  | CtrlPlaneArg c => lookup (valuation.(ctrl_plane_map)) c
  | HeaderArg h =>    lookup (valuation.(header_map)) h
  | ConstantArg n => Some n
  | StatefulArg s =>  lookup (valuation.(state_var_map)) s
  end.

Definition function_argument_to_uint8 (arg : FunctionArgument) (valuation : Valuation) : uint8 :=
  match lookup_function_argument arg valuation with
  | Some n => n
  | None => zero (* TODO: or any default value or error handling as appropriate *)
  end.

(* A BinaryOp takes two uint8 arguments and returns another uint8 *)
Inductive BinaryOp :=
  | AddOp.

Definition apply_bin_op (f : BinaryOp) (arg1 : uint8) (arg2 : uint8) : uint8 :=
  match f with
  | AddOp => Integers.add arg1 arg2
  end.

(* Define the header operations *)
Inductive HdrOp :=
  | StatefulOp  (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : StateVar)
  | StatelessOp (f : BinaryOp) (arg1 : FunctionArgument) (arg2 : FunctionArgument) (target : Header).

Inductive MatchActionRule :=
  | Seq (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool) (action : list HdrOp)
  | Par (h : Header) (start_index : uint8) (end_index : uint8) (pat : list bool) (action : list HdrOp).

Definition Transformer : Type := list MatchActionRule.

(* Example header *)
Definition example_header1 : Header := HeaderCtr "hdr1"%string.

(* An example transformer *)
Definition example_transformer : Transformer :=
  [
    Seq example_header1 zero (repr 10%Z) [true; false; true] 
      [StatefulOp  AddOp (HeaderArg example_header1) (ConstantArg (repr 5%Z)) (StateVarCtr "state1"%string)];
    Par example_header1 zero (repr 10%Z) [false; true; false] 
      [StatelessOp AddOp (HeaderArg example_header1) (ConstantArg (repr 3%Z)) (HeaderCtr "hdr2"%string)]
  ].