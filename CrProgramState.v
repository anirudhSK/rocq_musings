From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import CrDsl.
From MyProject Require Import UtilLemmas.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
Require Import Strings.String.
Require Import ZArith.
From Coq Require Import FunctionalExtensionality.
Require Import Coq.Lists.List.
Import ListNotations.

(* Current values for each of these identifiers as a map *)
Definition HeaderMap (T : Type) := PMap.t T. (* Maybe replace these with a generic Map type from Maps.v? *)
Definition StateMap (T : Type) := PMap.t T.
Definition CtrlMap (T : Type) := PMap.t T.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_map : CtrlMap T;
  header_map : HeaderMap T;
  state_map : StateMap T;
}.

Arguments header_map {T} _.
Arguments state_map {T} _.  
Arguments ctrl_map {T} _.

Definition ConcreteState := ProgramState uint8.
Definition SymbolicState := ProgramState SmtArithExpr.

Inductive PSField :=
| PSCtrl
| PSHeader
| PSState.

Definition map_from_ps {T : Type} (field : PSField) (ps : ProgramState T) : PMap.t T :=
  match field with
  | PSCtrl => ctrl_map ps
  | PSHeader => header_map ps
  | PSState => state_map ps
  end.

Definition program_state_mapper {T1 T2 : Type} (fc: T1 -> T2) (fh : T1 -> T2) (fs : T1 -> T2) (s: ProgramState T1) : ProgramState T2 :=
  {| ctrl_map := PMap.map fc (ctrl_map s);
     header_map := PMap.map fh (header_map s);
     state_map := PMap.map fs (state_map s) |}.

(* Function to go through all keys in a PMap, and set them to new values. *)
Definition new_pmap_from_old {T: Type} (old_pmap : PMap.t T) (f : positive -> T): PMap.t T :=
  (fst old_pmap, (* The old default value *)
   PTree.map (fun x _ => f x) (snd old_pmap) (* Take old tree (snd old_pmap) and map elements from it (x) via function (f) *)
  ).

Definition lookup_varlike_map {T A : Type} `{CrVarLike A} (m : PMap.t T) (x : A) : T :=
  PMap.get (get_key x) m.

Definition lookup_varlike {T A : Type} `{CrVarLike A} (f: PSField) (s: ProgramState T) (x : A) : T :=
  lookup_varlike_map (map_from_ps f s) x.

Definition update_all_varlike {T A : Type} `{CrVarLike A} (f: PSField) (s: ProgramState T) (fh: A -> T) : ProgramState T :=
  let new_map := new_pmap_from_old (map_from_ps f s) (fun pos => fh (make_item pos)) in
  match f with
  | PSCtrl =>   {| ctrl_map := new_map;
                   header_map := header_map s;
                   state_map := state_map s |}
  | PSHeader => {| ctrl_map := ctrl_map s;
                   header_map := new_map;
                   state_map := state_map s |}
  | PSState =>  {| ctrl_map := ctrl_map s;
                   header_map := header_map s;
                   state_map := new_map |}
  end.

Definition update_varlike_map {T A : Type} `{CrVarLike A} (m: PMap.t T) (x: A) (v: T) : PMap.t T :=
  PMap.set (get_key x) v m.
  
Definition update_varlike {T A : Type} `{CrVarLike A} (f: PSField) (s: ProgramState T) (x: A) (v: T) : ProgramState T :=
  let new_map := update_varlike_map (map_from_ps f s) x v in
  match f with
  | PSCtrl =>   {| ctrl_map := new_map;
                   header_map := header_map s;
                   state_map := state_map s |}
  | PSHeader => {| ctrl_map := ctrl_map s;
                   header_map := new_map;
                   state_map := state_map s |}
  | PSState =>  {| ctrl_map := ctrl_map s;
                   header_map := header_map s;
                   state_map := new_map |}
  end.

Lemma update_all_varlike_lookup_unchanged:
  forall {T A} `{CrVarLike A} (s1 : ProgramState T) (f : PSField),
   update_all_varlike f s1 (fun v : A => lookup_varlike_map (map_from_ps f s1) v) = s1.
Proof.
  intros.
  destruct s1 as [ctrl hdr state].
  unfold update_all_varlike.
  destruct f;
  simpl;
  f_equal; try reflexivity;
  unfold lookup_varlike_map;
  unfold new_pmap_from_old;
  simpl;
  try destruct ctrl; try destruct hdr; try destruct state;
  simpl;
  f_equal;
  apply PTree.extensionality;
  intros;
  rewrite PTree.gmap;
  unfold Coqlib.option_map;
  unfold PMap.get;
  simpl;
  rewrite inverses'.
  - destruct (t0 ! i) eqn:des; auto.
  - destruct (t2 ! i) eqn:des; auto.
  - destruct (t4 ! i) eqn:des; auto.
Qed.

Lemma commute_mapper_lookup_varlike:
  forall {T1 T2 A} `{CrVarLike A} ps v (func : T1 -> T2) f,
  lookup_varlike_map (map_from_ps f (program_state_mapper func func func ps)) v =
  func (lookup_varlike_map (map_from_ps f ps) v).
Proof.
  intros.
  destruct f;
  apply PMap.gmap.
Qed.

Lemma commute_mapper_update_varlike:
  forall {T1 T2 A} `{CrVarLike A} ps x v (func : T1 -> T2) f,
  program_state_mapper func func func (update_varlike f ps x v) =
  update_varlike f (program_state_mapper func func func ps) x (func v).
Proof.
  intros.
  unfold program_state_mapper.
  unfold update_varlike.
  destruct f;
  f_equal;
  simpl;
  unfold update_varlike_map;
  destruct ps;
  simpl;
  unfold PMap.set;
  unfold PMap.map;
  simpl;
  f_equal;
  apply PTree.extensionality;
  intros;
  simpl;
  rewrite PTree.gsspec;
  rewrite PTree.gmap1;
  rewrite PTree.gsspec.
  1-3: destruct (Coqlib.peq i (get_key x));
  try subst; try reflexivity;
  try rewrite PTree.gmap1; try reflexivity.
Qed.

Lemma lookup_f1_unchanged_by_update_all_f2:
  forall {T A} `{CrVarLike A} fs (s1 : ProgramState T) (h : A) f1 f2,
  f1 <> f2 ->
    lookup_varlike_map (map_from_ps f1 s1) h =
    lookup_varlike_map (map_from_ps f1 (update_all_varlike f2 s1 fs)) h.
Proof.
  intros.
  destruct f1, f2;
  try reflexivity;
  try congruence.
Qed.

Definition is_varlike_in_ps {T A} `{CrVarLike A} (f : PSField) (s1 : ProgramState T) (v : A) :=
  PTree.get (get_key v) (snd (map_from_ps f s1)).

Lemma lookup_varlike_after_update_all_varlike:
  forall {T A} `{CrVarLike A} (s1 : ProgramState T) (v : A) (fv : A -> T) field,
    is_varlike_in_ps field s1 v <> None ->
    lookup_varlike_map (map_from_ps field (update_all_varlike field s1 fv)) v = fv v.
Proof.
  intros.
  unfold lookup_varlike_map.
  unfold update_all_varlike.
  destruct field;
  simpl;
  unfold lookup_varlike_map;
  unfold new_pmap_from_old;
  simpl;
  unfold is_varlike_in_ps in H0; simpl in H0;
  try destruct (map_from_ps PSCtrl s1) as [default ctrl];
  try destruct (map_from_ps PSHeader s1) as [default header];
  try destruct (map_from_ps PSState s1) as [default state];
  unfold PMap.get;
  simpl;
  rewrite PTree.gmap;
  unfold Coqlib.option_map;
  rewrite inverses;
  simpl;
  simpl in H.
  - destruct (snd (ctrl_map s1)) ! (get_key v) eqn:des. auto. congruence.
  - destruct (snd (header_map s1)) ! (get_key v) eqn:des. try auto. congruence.
  - destruct (snd (state_map s1)) ! (get_key v) eqn:des. try auto. congruence.
Qed.

Lemma commute_varlike_updates:
  forall {T A A'}
    `{CrVarLike A}
    `{CrVarLike A'}
    (s1 : ProgramState T)
    (f f' : PSField)
    (fv : A -> T) (fv' : A' -> T),
  f <> f' ->
    update_all_varlike f (update_all_varlike f' s1 fv') fv =
    update_all_varlike f' (update_all_varlike f s1 fv) fv'.
Proof.
  intros.
  destruct f, f';
  try congruence;
  try unfold update_all_varlike; f_equal.
Qed.

(* TODO: lookup_hdr/state_map could be rolled into lookup_hdr/state. *)
(* TODO: It is used in a proof with a giant remember expression. *)
Definition lookup_hdr {T : Type} (s: ProgramState T) (x: Header) : T :=
  lookup_varlike_map (map_from_ps PSHeader s) x.

Definition lookup_state {T : Type} (s: ProgramState T) (x: State) : T :=
  lookup_varlike_map (map_from_ps PSState s) x.

Definition lookup_ctrl {T : Type} (s: ProgramState T) (x: Ctrl) : T :=
  lookup_varlike_map (map_from_ps PSCtrl s) x.

Lemma program_state_equality:
      forall (ps1 ps2: ConcreteState),
        ctrl_map ps1 = ctrl_map ps2 ->
        header_map ps1 = header_map ps2 ->
        state_map  ps1 = state_map ps2 ->
        ps1 = ps2.
Proof.
  intros ps1 ps2 Hctrl Hhdr Hstate.
  destruct ps1 as [ctrl1 hdr1 state1].
  destruct ps2 as [ctrl2 hdr2 state2].
  simpl in *.
  f_equal; try assumption.
Qed.

Definition update_all_hdrs {T : Type} (s: ProgramState T) (fh: Header -> T) : ProgramState T :=
  update_all_varlike PSHeader s fh.

Definition update_all_states {T : Type} (s: ProgramState T) (fs: State -> T) : ProgramState T :=
  update_all_varlike PSState s fs.

(* Update the header map with a new value for a specific header *)
Definition update_hdr {T : Type} (s: ProgramState T) (x: Header) (v: T) : ProgramState T :=
  update_varlike PSHeader s x v.

Definition update_state {T : Type} (s: ProgramState T) (x: State) (v: T) : ProgramState T :=
  update_varlike PSState s x v.

Lemma cons_not_nil : forall A (x : A) (xs : list A),
  ~ ((x :: xs) = nil).
Proof.
  intros.
  simpl.
  unfold "<>".
  intros.
  discriminate H.
Qed.

Lemma program_state_unchanged:
  forall {T} (s1 : ProgramState T),
  update_all_varlike PSState (update_all_varlike PSHeader s1 (fun h : Header => lookup_varlike_map (map_from_ps PSHeader s1) h))
                    (fun s : State => lookup_varlike_map (map_from_ps PSState s1) s) = s1.
Proof.
  intros.
  repeat rewrite update_all_varlike_lookup_unchanged.
  reflexivity.
Qed.

Definition is_header_in_ps {T} (s1 : ProgramState T) (h : Header) :=
  PTree.get (match h with | HeaderCtr id => id end) (snd (header_map s1)).

Definition is_state_var_in_ps {T} (s1 : ProgramState T) (sv : State) :=
  PTree.get (match sv with | StateCtr id => id end) (snd (state_map s1)).

Lemma commute_state_hdr_updates:
  forall {T} (s1 : ProgramState T) (fh : Header -> T) (fs : State -> T),
    update_all_varlike PSHeader (update_all_varlike PSState s1 fs) fh =
    update_all_varlike PSState (update_all_varlike PSHeader s1 fh) fs.
Proof.
  reflexivity.
Qed.

Lemma lookup_hdr_trivial:
  forall {T} (s : ProgramState T) (h : Header),
    lookup_varlike_map (map_from_ps PSHeader s) h =
    lookup_varlike_map (header_map s) h.
Proof.
  intros.
  reflexivity.
Qed.

Lemma lookup_state_trivial:
  forall {T} (s : ProgramState T) (sv : State),
    lookup_varlike_map (map_from_ps PSState s) sv =
    lookup_varlike_map (state_map s) sv.
Proof.
  intros.
  reflexivity.
Qed.

(* is_header_in_ps is preserved across update_all_states *)
Lemma is_header_in_ps_after_update_all_states:
  forall {T} (s1 : ProgramState T) (h : Header) (fs : State -> T),
    is_header_in_ps (update_all_varlike PSState s1 fs) h = is_header_in_ps s1 h.
Proof.
  intros.
  reflexivity.
Qed.

(* is_state_var_in_ps is preserved across update_all_hdrs *)
Lemma is_state_var_in_ps_after_update_all_hdrs:
  forall {T} (s1 : ProgramState T) (sv : State) (fh : Header -> T),
    is_state_var_in_ps (update_all_varlike PSHeader s1 fh) sv = is_state_var_in_ps s1 sv.
Proof.
  intros.
  reflexivity.
Qed.

Definition get_all_headers_from_ps {T : Type} (s: ProgramState T) : list Header :=
  List.map (fun '(key, value) => HeaderCtr key)
           (PTree.elements (snd (header_map s))).

Definition get_all_states_from_ps {T : Type} (s: ProgramState T) : list State :=
  List.map (fun '(key, value) => StateCtr key)
           (PTree.elements (snd (state_map s))).

Definition get_all_ctrls_from_ps {T : Type} (s: ProgramState T) : list Ctrl :=
  List.map (fun '(key, value) => CtrlCtr key)
           (PTree.elements (snd (ctrl_map s))).

Lemma is_header_in_ps_lemma :
  forall {T} (s1 : ProgramState T) (h : Header),
    In h (get_all_headers_from_ps s1) ->
    is_header_in_ps s1 h <> None.
    (* TODO: Need to ask Joe about <> None *)
Proof.
  intros.
  destruct s1 as [ctrl hdr state].
  unfold get_all_headers_from_ps in H.
  unfold is_header_in_ps.
  simpl in *.
  destruct hdr as [default hdr_map].
  simpl in *.
  apply in_map_iff in H.
  simpl in H.
  destruct H. (* TODO: ask Joe, seems to extract witness *)
  destruct x.
  destruct h.
  destruct H.
  injection H as H_eq.
  rewrite <- H_eq.
  apply some_is_not_none with (x := t).
  apply PTree.elements_complete.
  assumption.
Qed.

(* Same as above lemma, but for state *)
Lemma is_state_in_ps_lemma :
  forall {T} (s1 : ProgramState T) (sv : State),
    In sv (get_all_states_from_ps s1) ->
    is_state_var_in_ps s1 sv <> None.
Proof.
  intros.
  destruct s1 as [ctrl hdr state].
  unfold get_all_states_from_ps in H.
  unfold is_state_var_in_ps.
  simpl in *.
  destruct state as [default state_map].
  simpl in *.
  apply in_map_iff in H.
  simpl in H.
  destruct H. (* TODO: ask Joe, seems to extract witness *)
  destruct x.
  destruct sv.
  destruct H.
  injection H as H_eq.
  rewrite <- H_eq.
  apply some_is_not_none with (x := t).
  apply PTree.elements_complete.
  assumption.
Qed.

Definition init_concrete_state (p : CaracaraProgram) : ConcreteState :=
  let h := get_headers_from_prog p in
  let s := get_states_from_prog p in
  let c := get_ctrls_from_prog p in
  {|ctrl_map    :=  (repr 0, (* TODO: Need better default, but think this doesn't matter *)
                    PTree_Properties.of_list
                    (List.map (fun x => (match x with | CtrlCtr x_id => x_id end, repr 0)) c));
     header_map :=  (repr 0, (* TODO: Need better default, but think this doesn't matter *)
                    PTree_Properties.of_list
                    (List.map (fun x => (match x with | HeaderCtr x_id => x_id end, repr 0)) h));
     state_map  :=  (repr 0,
                    PTree_Properties.of_list
                    (List.map (fun x => (match x with | StateCtr x_id => x_id end, repr 0)) s));|}.

(* Convert positive to string *)
Fixpoint pos_to_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => String.append (pos_to_string p') "0"
  | xI p' => String.append (pos_to_string p') "1"
  end.

Definition init_symbolic_state (p: CaracaraProgram) : SymbolicState :=
  let h := get_headers_from_prog p in
  let s := get_states_from_prog p in
  let c := get_ctrls_from_prog p in
  {|ctrl_map :=  (SmtArithVar "rndstring", (*TODO: Need better default, but think this doesn't matter *)
                        PTree_Properties.of_list
                        (List.map (fun x => let var := match x with | CtrlCtr x_id => x_id end in (var,  SmtArithVar (pos_to_string var))) c));
     header_map     :=  (SmtArithVar "rndstring", (*TODO: Need better default, but think this doesn't matter *)
                        PTree_Properties.of_list
                        (List.map (fun x => let var := match x with | HeaderCtr x_id => x_id end in (var, SmtArithVar (pos_to_string var))) h));
     state_map  :=  (SmtArithVar "rndstring", (*TODO: Need better default, but think this doesn't matter *)
                        PTree_Properties.of_list
                        (List.map (fun x => let var := match x with | StateCtr x_id => x_id end in (var, SmtArithVar (pos_to_string var))) s));|}.

Definition is_init_state {T} (p : CaracaraProgram) (ps : ProgramState T) : Prop :=
  forall h sv c,
    (In h (get_headers_from_prog p) <-> In h (get_all_headers_from_ps ps)) /\
    (In sv (get_states_from_prog p) <-> In sv (get_all_states_from_ps ps)) /\
    (In c (get_ctrls_from_prog p) <-> In c (get_all_ctrls_from_ps ps)).

(* Mark definitions globally opaque below *)
Global Opaque lookup_ctrl.
Global Opaque update_varlike_map.
Global Opaque update_hdr.
Global Opaque update_state.
Global Opaque lookup_hdr.
Global Opaque lookup_state.
Global Opaque lookup_varlike_map.
Global Opaque program_state_mapper.
Global Opaque update_all_hdrs.
Global Opaque update_all_states.
Global Opaque HeaderMap.
Global Opaque StateMap.
Global Opaque CtrlMap.
Global Opaque new_pmap_from_old.
Global Opaque is_header_in_ps.
Global Opaque is_state_var_in_ps.
Global Opaque get_all_headers_from_ps.
Global Opaque get_all_states_from_ps.
Global Opaque map_from_ps.