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
Definition HeaderMap (T : Type) := Header -> T.
Definition StateVarMap (T : Type) := StateVar -> T.
Definition CtrlPlaneConfigNameMap (T : Type) := CtrlPlaneConfigName -> T.

Definition update_hdr_map (s: HeaderMap uint8) (x: Header) (v: uint8) : (HeaderMap uint8) :=
  fun y => match x, y with
            | HeaderCtr x_name, HeaderCtr y_name => if string_dec x_name y_name then v else s y
           end.

Definition update_state_map (s: StateVarMap uint8) (x: StateVar) (v: uint8) : (StateVarMap uint8) :=
  fun y => match x, y with
            | StateVarCtr x_name, StateVarCtr y_name => if string_dec x_name y_name then v else s y
           end.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState := {
  ctrl_plane_map : CtrlPlaneConfigNameMap uint8;
  header_map : HeaderMap uint8;
  state_var_map : StateVarMap uint8
}.