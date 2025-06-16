From MyProject Require Export CrIdentifiers.
Require Import Strings.String.

(* Current values for each of these identifiers as a map *)
Definition HeaderMap (T : Type) := Header -> T.
Definition StateVarMap (T : Type) := StateVar -> T.
Definition CtrlPlaneConfigNameMap (T : Type) := CtrlPlaneConfigName -> T.

Definition update_hdr_map {T : Type} (s: HeaderMap T) (x: Header) (v: T) : (HeaderMap T) :=
  fun y => match x, y with
            | HeaderCtr x_name, HeaderCtr y_name => if string_dec x_name y_name then v else s y
           end.

Definition update_state_map {T : Type} (s: StateVarMap T) (x: StateVar) (v: T) : (StateVarMap T) :=
  fun y => match x, y with
            | StateVarCtr x_name, StateVarCtr y_name => if string_dec x_name y_name then v else s y
           end.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_plane_map : CtrlPlaneConfigNameMap T;
  header_map : HeaderMap T;
  state_var_map : StateVarMap T
}.