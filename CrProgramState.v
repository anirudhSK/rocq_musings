From MyProject Require Export CrIdentifiers.
From MyProject Require Export Maps.
Require Import Strings.String.
Require Import ZArith.
From Coq Require Import FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

(* Current values for each of these identifiers as a map *)
Definition HeaderMap (T : Type) := PMap.t T. (* Maybe replace these with a generic Map type from Maps.v? *)
Definition StateVarMap (T : Type) := PMap.t T.
Definition CtrlPlaneConfigNameMap (T : Type) := PMap.t T.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_plane_map : CtrlPlaneConfigNameMap T;
  header_map : HeaderMap T;
  state_var_map : StateVarMap T;
}.

Arguments header_map {T} _.
Arguments state_var_map {T} _.  
Arguments ctrl_plane_map {T} _.

(* TODO: lookup_hdr/state_map could be rolled into lookup_hdr/state. *)
(* TODO: It is used in a proof with a giant remember expression. *)
Definition lookup_hdr_map {T : Type} (m: HeaderMap T) (x: Header) : T :=
  PMap.get (match x with | HeaderCtr id => id end) m.

Definition lookup_state_map {T : Type} (m: StateVarMap T) (x: StateVar) : T :=
  PMap.get (match x with | StateVarCtr id => id end) m.

Definition lookup_hdr {T : Type} (s: ProgramState T) (x: Header) : T :=
  lookup_hdr_map (header_map s) x.

Definition lookup_state {T : Type} (s: ProgramState T) (x: StateVar) : T :=
  lookup_state_map (state_var_map s) x.

Definition lookup_ctrl {T : Type} (s: ProgramState T) (x: CtrlPlaneConfigName) : T :=
  PMap.get (match x with | CtrlPlaneConfigNameCtr id => id end) (ctrl_plane_map s).


(* Some lemmas for convenience *)
(* TODO: try to replace this with the extensionality lemma/theorem from the Maps.v library *)
Lemma header_map_extensionality: forall {T} (map1 map2 : HeaderMap T),
  (forall x, lookup_hdr_map map1 x = lookup_hdr_map map2 x) -> map1 = map2.
Admitted.

Lemma state_var_map_extensionality: forall {T} (map1 map2 : StateVarMap T),
  (forall x, lookup_state_map map1 x = lookup_state_map map2 x) -> map1 = map2.
Admitted.

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
     header_map := PMap.map fh (header_map s);
     state_var_map := PMap.map fs (state_var_map s) |}.

(* Function to go through all keys in a PMap, and set them to new values. *)
Definition new_pmap_from_old {T: Type} (old_pmap : PMap.t T) (f : positive -> T): PMap.t T :=
  (fst old_pmap, (* The old default value *)
   PTree.map (fun x _ => f x) (snd old_pmap) (* Take old tree (snd old_pmap) and map elements from it (x) via function (f) *)
  ).

Definition update_all_hdrs {T : Type} (s: ProgramState T) (fh: Header -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := new_pmap_from_old (header_map s) (fun pos => fh (HeaderCtr pos));
     state_var_map := state_var_map s |}.

Definition update_all_states {T : Type} (s: ProgramState T) (fs: StateVar -> T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := new_pmap_from_old (state_var_map s) (fun pos => fs (StateVarCtr pos))|}.

(* Update the header map with a new value for a specific header *)
Definition update_hdr_map {T : Type} (m: HeaderMap T) (x: Header) (v: T) : HeaderMap T :=
  PMap.set (match x with | HeaderCtr x_id => x_id end) v m.

(* Same as above, but for state variables *)
Definition update_state_map {T : Type} (m: StateVarMap T) (x: StateVar) (v: T) : StateVarMap T :=
  PMap.set (match x with | StateVarCtr x_id => x_id end) v m.

Definition update_hdr {T : Type} (s: ProgramState T) (x: Header) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map :=  update_hdr_map (header_map s) x v;
     state_var_map := state_var_map s|}.

Definition update_state {T : Type} (s: ProgramState T) (x: StateVar) (v: T) : ProgramState T :=
  {| ctrl_plane_map := ctrl_plane_map s;
     header_map := header_map s;
     state_var_map := update_state_map (state_var_map s) x v |}.

Lemma cons_not_nil : forall A (x : A) (xs : list A),
  ~ ((x :: xs) = nil).
Proof.
  intros.
  simpl.
  unfold "<>".
  intros.
  discriminate H.
Qed.

Lemma update_all_hdrs_lookup_unchanged:
  forall {T} (s1 : ProgramState T),
   update_all_hdrs s1 (fun h : Header => lookup_hdr s1 h) = s1.
Proof.
  intros.
  destruct s1 as [ctrl hdr state].
  unfold update_all_hdrs.
  simpl.
  f_equal; try reflexivity.
  unfold lookup_hdr.
  simpl.
  unfold lookup_hdr_map.
  unfold new_pmap_from_old.
  simpl.
  destruct hdr.
  simpl.
  f_equal.
  apply PTree.extensionality.
  intros.
  rewrite PTree.gmap.
  unfold Coqlib.option_map.
  unfold PMap.get.
  simpl.
  destruct (t0 ! i) eqn:des; auto.
Qed.

(* Same lemma as above but for state *)
Lemma update_all_states_lookup_unchanged:
  forall {T} (s1 : ProgramState T),
   update_all_states s1 (fun sv : StateVar => lookup_state s1 sv) = s1.
Proof.
  intros.
  destruct s1 as [ctrl hdr state].
  unfold update_all_states.
  simpl.
  f_equal; try reflexivity.
  unfold lookup_state.
  simpl.
  unfold lookup_state_map.
  unfold new_pmap_from_old.
  simpl.
  destruct state.
  simpl.
  f_equal.
  apply PTree.extensionality.
  intros.
  rewrite PTree.gmap.
  unfold Coqlib.option_map.
  unfold PMap.get.
  simpl.
  destruct (t0 ! i) eqn:des; auto.
Qed.

Lemma program_state_unchanged:
  forall {T} (s1 : ProgramState T),
  update_all_states (update_all_hdrs s1 (fun h : Header => lookup_hdr s1 h))
                    (fun s : StateVar => lookup_state s1 s) = s1.
Proof.
  intros.
  rewrite update_all_hdrs_lookup_unchanged.
  rewrite update_all_states_lookup_unchanged.
  reflexivity.
Qed.        

Lemma commute_mapper_lookup_ctrl:
  forall {T1} {T2} ps c (func : T1 -> T2),
  lookup_ctrl (program_state_mapper func func func ps) c =
  func (lookup_ctrl ps c).
Proof.
  intros.
  apply PMap.gmap.
Qed.

Lemma commute_mapper_lookup_state:
  forall {T1} {T2} ps sv (func : T1 -> T2),
  lookup_state (program_state_mapper func func func ps) sv =
  func (lookup_state ps sv).
Proof.
  intros.
  apply PMap.gmap.
Qed.

Lemma commute_mapper_lookup_hdr:
  forall {T1} {T2} ps hv (func : T1 -> T2),
  lookup_hdr (program_state_mapper func func func ps) hv =
  func (lookup_hdr ps hv).
Proof.
  intros.
  apply PMap.gmap.
Qed.

Lemma commute_mapper_update_hdr:
  forall {T1} {T2} ps h v (func : T1 -> T2),
  program_state_mapper func func func (update_hdr ps h v) =
  update_hdr (program_state_mapper func func func ps) h (func v).
Proof.
  intros.
  unfold program_state_mapper.
  unfold update_hdr.
  f_equal.
  simpl.
  unfold update_hdr_map.
  destruct ps.
  simpl.
  destruct h. simpl.
  unfold PMap.set.
  unfold PMap.map.
  simpl.
  f_equal.
  apply PTree.extensionality.
  intros.
  simpl.
  rewrite PTree.gsspec.
  rewrite PTree.gmap1.
  rewrite PTree.gsspec.
  destruct (Coqlib.peq i uid).
  - subst. reflexivity.
  - rewrite PTree.gmap1.
    reflexivity.
Qed.

Lemma commute_mapper_update_state:
  forall {T1} {T2} ps sv v (func : T1 -> T2),
  program_state_mapper func func func (update_state ps sv v) =
  update_state (program_state_mapper func func func ps) sv (func v).
Proof.
  intros.
  unfold program_state_mapper.
  unfold update_state.
  f_equal.
  simpl.
  unfold update_state_map.
  destruct ps.
  simpl.
  destruct sv. simpl.
  unfold PMap.set.
  unfold PMap.map.
  simpl.
  f_equal.
  apply PTree.extensionality.
  intros.
  simpl.
  rewrite PTree.gsspec.
  rewrite PTree.gmap1.
  rewrite PTree.gsspec.
  destruct (Coqlib.peq i uid).
  - subst. reflexivity.
  - rewrite PTree.gmap1.
    reflexivity.
Qed.

Lemma lookup_hdr_unchanged_by_update_all_states:
  forall {T} fs (s1 : ProgramState T) (h : Header),
    lookup_hdr s1 h = lookup_hdr (update_all_states s1 fs) h.
Proof.
  reflexivity.
Qed.

Definition is_header_in_map {T} (s1 : ProgramState T) (h : Header) :=
  PTree.get (match h with | HeaderCtr id => id end) (snd (header_map s1)).

Lemma lookup_hdr_after_update_all_hdrs:
  forall {T} (s1 : ProgramState T) (h : Header) (fh : Header -> T),
    is_header_in_map s1 h <> None ->
    lookup_hdr (update_all_hdrs s1 fh) h = fh h.
Proof.
  intros.
  unfold lookup_hdr.
  unfold update_all_hdrs.
  simpl.
  unfold lookup_hdr_map.
  unfold new_pmap_from_old.
  simpl.
  unfold is_header_in_map in H.
  destruct (header_map s1) as [default hdr].
  simpl.
  f_equal.
  unfold PMap.get.
  simpl.
  rewrite PTree.gmap.
  unfold Coqlib.option_map.
  destruct h.
  simpl.
  simpl in H.
  destruct (hdr ! uid) eqn:des; auto.
  congruence.
Qed.

(* Create mirror image versions of the two lemmas above with state and hdr interchanged *)
Lemma lookup_state_unchanged_by_update_all_hdrs:
  forall {T} fh (s1 : ProgramState T) (sv : StateVar),
    lookup_state s1 sv = lookup_state (update_all_hdrs s1 fh) sv.
Proof.
  reflexivity.
Qed.

Definition is_state_in_map {T} (s1 : ProgramState T) (sv : StateVar) :=
  PTree.get (match sv with | StateVarCtr id => id end) (snd (state_var_map s1)).

Lemma lookup_state_after_update_all_states:
  forall {T} (s1 : ProgramState T) (sv : StateVar) (fs : StateVar -> T),
    is_state_in_map s1 sv <> None ->
    lookup_state (update_all_states s1 fs) sv = fs sv.
Proof.
  intros.
  unfold lookup_state.
  unfold update_all_states.
  simpl.
  unfold lookup_state_map.
  unfold new_pmap_from_old.
  simpl.
  unfold is_state_in_map in H.
  destruct (state_var_map s1) as [default sv_map].
  simpl.
  f_equal.
  unfold PMap.get.
  simpl.
  rewrite PTree.gmap.
  unfold Coqlib.option_map.
  destruct sv.
  simpl.
  simpl in H.
  destruct (sv_map ! uid) eqn:des; auto.
  congruence.
Qed.

Lemma commute_state_hdr_updates:
  forall {T} (s1 : ProgramState T) (fh : Header -> T) (fs : StateVar -> T),
    update_all_hdrs (update_all_states s1 fs) fh =
    update_all_states (update_all_hdrs s1 fh) fs.
Proof.
  reflexivity.
Qed.

Lemma lookup_hdr_trivial:
  forall {T} (s : ProgramState T) (h : Header),
    lookup_hdr s h = lookup_hdr_map (header_map s) h.
Proof.
  intros.
  reflexivity.
Qed.

Lemma lookup_state_trivial:
  forall {T} (s : ProgramState T) (sv : StateVar),
    lookup_state s sv = lookup_state_map (state_var_map s) sv.
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
Global Opaque HeaderMap.
Global Opaque StateVarMap.
Global Opaque CtrlPlaneConfigNameMap.