Require Import Strings.String.
From MyProject Require Export Map.
From MyProject Require Export Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8 := @bit_int 8.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (name : string).
Inductive Header : Type := HeaderCtr (name : string).
Inductive StateVar : Type := StateVarCtr (name : string).
Inductive ModuleName : Type := ModuleNameCtr (name : string).
Inductive FunctionName : Type := FunctionNameCtr (name : string).
Inductive ConnectionName : Type := ConnectionNameCtr (name : string).
Inductive CtrlPlaneConfigName : Type := CtrlPlaneConfigNameCtr (name : string).

(* Current values for each of these identifiers as a map *)
Definition HeaderMap := fmap Header uint8.
Definition StateVarMap := fmap StateVar uint8.
Definition CtrlPlaneConfigNameMap := fmap CtrlPlaneConfigName uint8.

(* The valuation is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record Valuation := {
  ctrl_plane_map : CtrlPlaneConfigNameMap;
  header_map : HeaderMap;
  state_var_map : StateVarMap
}.

(* Empty valuation *)
Example empty_valuation : Valuation := {|
  ctrl_plane_map := empty CtrlPlaneConfigName uint8;
  header_map := empty Header uint8;
  state_var_map := empty StateVar uint8
|}.

(* example of parser state *)
Definition example_parser_state := ParserStateCtr "example_parser_state".

(* example of header *)
Definition example_header := HeaderCtr "example_header".