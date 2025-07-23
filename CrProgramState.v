From MyProject Require Export CrIdentifiers.
Require Import Strings.String.
Require Import ZArith.

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

Arguments header_map {T} _ _.
Arguments state_var_map {T} _ _.  
Arguments ctrl_plane_map {T} _ _.

Definition lookup_hdr {T : Type} (s: ProgramState T) (x: Header) : T :=
  header_map s x.

Definition lookup_state {T : Type} (s: ProgramState T) (x: StateVar) : T :=
  state_var_map s x.

Definition lookup_ctrl {T : Type} (s: ProgramState T) (x: CtrlPlaneConfigName) : T :=
  ctrl_plane_map s x.

Definition update_hdr {T : Type} (s: ProgramState T) (x: Header) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map :=  fun y => match x, y with
            | HeaderCtr x_id, HeaderCtr y_id => if Pos.eqb x_id y_id then v else lookup_hdr s y
           end;
     state_var_map := state_var_map s|}.

Definition update_state {T : Type} (s: ProgramState T) (x: StateVar) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := fun y => match x, y with
            | StateVarCtr x_id, StateVarCtr y_id => if Pos.eqb x_id y_id then v else lookup_state s y
           end |}.