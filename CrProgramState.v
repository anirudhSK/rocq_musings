From MyProject Require Export CrIdentifiers.
From MyProject Require Export Maps.
Require Import Strings.String.
Require Import ZArith.

(* Current values for each of these identifiers as a map *)
Definition HeaderMap (T : Type) := Header -> T.
Definition StateVarMap (T : Type) := StateVar -> T.
Definition CtrlPlaneConfigNameMap (T : Type) := PMap.t T.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_plane_map : CtrlPlaneConfigNameMap T;
  header_map : HeaderMap T;
  state_var_map : StateVarMap T;
}.

Arguments header_map {T} _ _.
Arguments state_var_map {T} _ _.  
Arguments ctrl_plane_map {T} _.

Definition lookup_hdr {T : Type} (s: ProgramState T) (x: Header) : T :=
  header_map s x.
Opaque lookup_hdr.

Definition lookup_state {T : Type} (s: ProgramState T) (x: StateVar) : T :=
  state_var_map s x.
Opaque lookup_state.

Definition lookup_ctrl {T : Type} (s: ProgramState T) (x: CtrlPlaneConfigName) : T :=
  PMap.get (match x with | CtrlPlaneConfigNameCtr id => id end) (ctrl_plane_map s).
Opaque lookup_ctrl.

Definition program_state_mapper {T1 T2 : Type} (fc: T1 -> T2) (fh : T1 -> T2) (fs : T1 -> T2) (s: ProgramState T1) : ProgramState T2 :=
  {| ctrl_plane_map := PMap.map fc (ctrl_plane_map s);
     header_map := fun x => fh (lookup_hdr s x);
     state_var_map := fun x => fs (lookup_state s x) |}.
Opaque program_state_mapper.

Definition update_all_hdrs {T : Type} (s: ProgramState T) (fh: Header -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := fun h => fh h;
     state_var_map := state_var_map s |}.

Definition update_all_states {T : Type} (s: ProgramState T) (fs: StateVar -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := fun sv => fs sv |}.

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
Opaque update_state.

Lemma ctrl_plane_invariant_update_hdr:
  forall {T} (s: ProgramState T) (x: Header) (v: T),
    ctrl_plane_map (update_hdr s x v) = ctrl_plane_map s.
Proof.
  intros.
  unfold update_hdr.
  destruct x; simpl; try reflexivity.
Qed.

Lemma ctrl_plane_invariant_update_hdrs:
  forall {T} (s: ProgramState T) (f: Header -> T),
    ctrl_plane_map (update_all_hdrs s f) = ctrl_plane_map s.
Proof.
  intros.
  unfold update_all_hdrs.
  simpl.
  reflexivity.
Qed.

(* Same as above but for state vars *)

Lemma ctrl_plane_invariant_update_states:
  forall {T} (s: ProgramState T) (f: StateVar -> T),
    ctrl_plane_map (update_all_states s f) = ctrl_plane_map s.
Proof.
  intros.
  unfold update_all_states.
  simpl.
  reflexivity.
Qed.

Opaque update_hdr.
Opaque update_all_hdrs.
Opaque update_all_states.