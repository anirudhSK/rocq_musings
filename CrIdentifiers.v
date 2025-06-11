Require Import Strings.String.
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
Definition HeaderMap := Header -> uint8.
Definition StateVarMap := StateVar -> uint8.
Definition CtrlPlaneConfigNameMap := CtrlPlaneConfigName -> uint8.

(* Borrowed from https://xavierleroy.org/courses/EUTypes-2019/html/EUTypes2019.CompilerVerification.IMP.html *)
(* Can make this less boilerplate, but this will do for now *)
(* (Definition update_h_map (h : Header) (v: uint8) (s: (Header->uint8)) : Header->uint8 :=
  fun y => if string_dec h y then v else s y.) *)

(* The valuation is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record Valuation := {
  ctrl_plane_map : CtrlPlaneConfigNameMap;
  header_map : HeaderMap;
  state_var_map : StateVarMap
}.