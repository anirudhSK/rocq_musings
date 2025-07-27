From MyProject Require Export CrIdentifiers.
From MyProject Require Export Maps.
Require Import Strings.String.
Require Import ZArith.
From Coq Require Import FunctionalExtensionality.

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

Definition lookup_hdr_map {T : Type} (m: HeaderMap T) (x: Header) : T :=
  m x.

Definition lookup_state_map {T : Type} (m: StateVarMap T) (x: StateVar) : T :=
  m x.

Definition lookup_hdr {T : Type} (s: ProgramState T) (x: Header) : T :=
  lookup_hdr_map (header_map s) x.

Definition lookup_state {T : Type} (s: ProgramState T) (x: StateVar) : T :=
  lookup_state_map (state_var_map s) x.

Definition lookup_ctrl {T : Type} (s: ProgramState T) (x: CtrlPlaneConfigName) : T :=
  PMap.get (match x with | CtrlPlaneConfigNameCtr id => id end) (ctrl_plane_map s).

Lemma program_state_equality:
      forall (ps1 ps2: ProgramState uint8),
        ctrl_plane_map ps1 = ctrl_plane_map ps2 ->
        header_map ps1 = header_map ps2 ->
        state_var_map  ps1 = state_var_map ps2 ->
        ps1 = ps2.
Proof.
  intros ps1 ps2 Hctrl Hhdr Hstate.
  destruct ps1 as [ctrl1 hdr1 state1].
  destruct ps2 as [ctrl2 hdr2 state2].
  simpl in *.
  f_equal; try assumption.
Qed.

Definition program_state_mapper {T1 T2 : Type} (fc: T1 -> T2) (fh : T1 -> T2) (fs : T1 -> T2) (s: ProgramState T1) : ProgramState T2 :=
  {| ctrl_plane_map := PMap.map fc (ctrl_plane_map s);
     header_map := fun x => fh (lookup_hdr s x);
     state_var_map := fun x => fs (lookup_state s x) |}.

Definition update_all_hdrs {T : Type} (s: ProgramState T) (fh: Header -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := fun h => fh h;
     state_var_map := state_var_map s |}.

Definition update_all_states {T : Type} (s: ProgramState T) (fs: StateVar -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := fun sv => fs sv |}.

(* Update the header map with a new value for a specific header *)
Definition update_hdr_map {T : Type} (m: HeaderMap T) (x: Header) (v: T) : HeaderMap T :=
  fun y => match x, y with | HeaderCtr x_id, HeaderCtr y_id => if Pos.eqb x_id y_id then v else m y end.

(* Same as above, but for state variables *)
Definition update_state_map {T : Type} (m: StateVarMap T) (x: StateVar) (v: T) : StateVarMap T :=
  fun y => match x, y with | StateVarCtr x_id, StateVarCtr y_id => if Pos.eqb x_id y_id then v else m y end.

Definition update_hdr {T : Type} (s: ProgramState T) (x: Header) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map :=  update_hdr_map (header_map s) x v;
     state_var_map := state_var_map s|}.

Definition update_state {T : Type} (s: ProgramState T) (x: StateVar) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := update_state_map (state_var_map s) x v |}.

Lemma commute_mapper_lookup_state:
  forall {T1} {T2} ps sv (func : T1 -> T2),
  lookup_state (program_state_mapper func func func ps) sv =
  func (lookup_state ps sv).
Proof.
  reflexivity.
Qed.

Lemma commute_mapper_lookup_hdr:
  forall {T1} {T2} ps hv (func : T1 -> T2),
  lookup_hdr (program_state_mapper func func func ps) hv =
  func (lookup_hdr ps hv).
Proof.
  reflexivity.
Qed.

Lemma commute_mapper_update_hdr:
  forall {T1} {T2} ps h v (func : T1 -> T2),
  program_state_mapper func func func (update_hdr ps h v) =
  update_hdr (program_state_mapper func func func ps) h (func v).
Proof.
  intros.
  simpl.
  unfold program_state_mapper.
  unfold update_hdr.
  f_equal.
  simpl.
  unfold lookup_hdr.
  simpl.
  apply functional_extensionality.
  intros.
  unfold update_hdr_map.
  destruct h, x.
  destruct (uid =? uid0)%positive eqn:des.
  - reflexivity.
  - reflexivity.
Qed.

Lemma commute_mapper_update_state:
  forall {T1} {T2} ps sv v (func : T1 -> T2),
  program_state_mapper func func func (update_state ps sv v) =
  update_state (program_state_mapper func func func ps) sv (func v).
Proof.
  intros.
  simpl.
  unfold program_state_mapper.
  unfold update_state.
  f_equal.
  simpl.
  unfold lookup_state.
  simpl.
  apply functional_extensionality.
  intros.
  unfold update_state_map.
  destruct sv, x.
  destruct (uid =? uid0)%positive eqn:des.
  - reflexivity.
  - reflexivity.
Qed.

Lemma update_lookup_inverses_state_map:
  forall {T} (m : StateVarMap T) (target : StateVar),
    (update_state_map m target (lookup_state_map m target)) = m.
Proof.
  intros.
  unfold update_state_map.
  unfold lookup_state_map.
  simpl.
  destruct target.
  apply functional_extensionality.
  intros.
  destruct x.
  destruct (uid =? uid0)%positive eqn:des.
  - apply Pos.eqb_eq in des. rewrite des. reflexivity.
  - reflexivity.
Qed.

Lemma update_lookup_inverses_state:
  forall {T} (s : ProgramState T) (target : StateVar),
    (update_state s target (lookup_state s target)) = s.
Proof.
  intros.
  simpl.
  unfold update_state.
  unfold lookup_state.
  simpl.
  rewrite update_lookup_inverses_state_map.
  simpl.
  destruct s.
  simpl. 
  reflexivity.
Qed.

(* Do the same thing as state for hdrs: replicate both lemmas above *)
Lemma update_lookup_inverses_hdr_map:
  forall {T} (m : HeaderMap T) (target : Header),
    (update_hdr_map m target (lookup_hdr_map m target)) = m.
Proof.
  intros.
  unfold update_hdr_map.
  unfold lookup_hdr_map.
  simpl.
  destruct target.
  apply functional_extensionality.
  intros.
  destruct x.
  destruct (uid =? uid0)%positive eqn:des.
  - apply Pos.eqb_eq in des. rewrite des. reflexivity.
  - reflexivity.
Qed.

Lemma update_lookup_inverses_hdr:
  forall {T} (s : ProgramState T) (target : Header),
    (update_hdr s target (lookup_hdr s target)) = s.
Proof.
  intros.
  simpl.
  unfold update_hdr.
  unfold lookup_hdr.
  simpl.
  rewrite update_lookup_inverses_hdr_map.
  simpl.
  destruct s.
  simpl.
  reflexivity.
Qed.

Lemma lookup_hdr_unchanged_by_update_all_states:
  forall {T} fs (s1 : ProgramState T) (h : Header),
    lookup_hdr s1 h = lookup_hdr (update_all_states s1 fs) h.
Proof.
  reflexivity.
Qed.

Lemma lookup_hdr_after_update_all_hdrs:
  forall {T} (s1 : ProgramState T) (h : Header) (fh : Header -> T),
    lookup_hdr (update_all_hdrs s1 fh) h = fh h.
Proof.
  reflexivity.
Qed.

(* Create mirror image versions of the two lemmas above with state and hdr interchanged *)
Lemma lookup_state_unchanged_by_update_all_hdrs:
  forall {T} fh (s1 : ProgramState T) (sv : StateVar),
    lookup_state s1 sv = lookup_state (update_all_hdrs s1 fh) sv.
Proof.
  reflexivity.
Qed.

Lemma lookup_state_after_update_all_states:
  forall {T} (s1 : ProgramState T) (sv : StateVar) (fs : StateVar -> T),
    lookup_state (update_all_states s1 fs) sv = fs sv.
Proof.
  reflexivity.
Qed.

Lemma commute_state_hdr_updates:
  forall {T} (s1 : ProgramState T) (fh : Header -> T) (fs : StateVar -> T),
    update_all_hdrs (update_all_states s1 fs) fh =
    update_all_states (update_all_hdrs s1 fh) fs.
Proof.
  reflexivity.
Qed.

Lemma header_map_lookup_hdr:
  forall {T} (s : ProgramState T) (h : Header),
    lookup_hdr s h = header_map s h.
Proof.
  intros.
  reflexivity.
Qed.

(* Same as above, but for state_var *)
Lemma state_var_map_lookup_state:
  forall {T} (s : ProgramState T) (sv : StateVar),
    lookup_state s sv = state_var_map s sv.
Proof.
  intros.
  reflexivity.
Qed.

(* Mark definitions globally opaque below *)
Global Opaque lookup_ctrl.
Global Opaque update_hdr_map.
Global Opaque update_state_map.
Global Opaque update_hdr.
Global Opaque update_state.
Global Opaque lookup_hdr.
Global Opaque lookup_state.
Global Opaque lookup_hdr_map.
Global Opaque lookup_state_map.
Global Opaque program_state_mapper.
Global Opaque update_all_hdrs.
Global Opaque update_all_states.