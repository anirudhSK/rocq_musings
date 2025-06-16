From MyProject Require Export CrIdentifiers.
Require Import Strings.String.

(* Current values for each of these identifiers as a map *)
Definition HeaderMap (T : Type) := Header -> T.
Definition StateVarMap (T : Type) := StateVar -> T.
Definition CtrlPlaneConfigNameMap (T : Type) := CtrlPlaneConfigName -> T.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_plane_map : CtrlPlaneConfigNameMap T;
  header_map : HeaderMap T;
  state_var_map : StateVarMap T
}.

Definition update_hdr {T : Type} (s: ProgramState T) (x: Header) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map T s;
     header_map :=  fun y => match x, y with
            | HeaderCtr x_name, HeaderCtr y_name => if string_dec x_name y_name then v else header_map T s y
           end;
     state_var_map := state_var_map T s|}.

Definition update_state {T : Type} (s: ProgramState T) (x: StateVar) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map T s;
     header_map := header_map T s;
     state_var_map := fun y => match x, y with
            | StateVarCtr x_name, StateVarCtr y_name => if string_dec x_name y_name then v else state_var_map T s y
           end |}.