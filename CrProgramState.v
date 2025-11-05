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

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_map : PMap.t T;
  header_map : PMap.t T;
  state_map : PMap.t T;
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

Lemma commute_lookup_varlike:
  forall {T1 T2 A} `{CrVarLike A} ps v (func : T1 -> T2) f,
  lookup_varlike f (program_state_mapper func func func ps) v =
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

Lemma program_state_unchanged:
  forall {T} (s1 : ProgramState T),
  update_all_varlike PSState (update_all_varlike PSHeader s1 (fun h : Header => lookup_varlike_map (map_from_ps PSHeader s1) h))
                    (fun s : State => lookup_varlike_map (map_from_ps PSState s1) s) = s1.
Proof.
  intros.
  repeat rewrite update_all_varlike_lookup_unchanged.
  reflexivity.
Qed.

Lemma is_v1_in_ps_after_update_all_v2:
  forall {T A A'} `{CrVarLike A} `{CrVarLike A'} (s1 : ProgramState T)
    f1 f2 (h : A) (fs : A' -> T),
    f1 <> f2 ->
    is_varlike_in_ps f1 (update_all_varlike f2 s1 fs) h = is_varlike_in_ps f1 s1 h.
Proof.
  intros.
  destruct f1, f2; try congruence;
  reflexivity.
Qed.

Definition get_all_varlike_from_ps {T A : Type} `{CrVarLike A} (f : PSField) (s: ProgramState T) : list A :=
  List.map (fun '(key, value) => make_item key)
           (PTree.elements (snd (map_from_ps f s))).

Lemma is_varlike_in_ps_lemma :
  forall {T A} `{CrVarLike A} (f : PSField) (s1 : ProgramState T) (v : A),
    In v (get_all_varlike_from_ps f s1) ->
    is_varlike_in_ps f s1 v <> None.
Proof.
  intros T A HA f s1 v H.
  destruct s1 as [ctrl hdr state].
  destruct f;
  unfold get_all_varlike_from_ps in H;
  unfold is_varlike_in_ps;
  simpl in *;
  destruct ctrl as [c0 ctrl_map];
  destruct hdr as [h0 hdr_map];
  destruct state as [s0 state_map];
  simpl in *;
  apply in_map_iff in H;
  destruct H; (* TODO: ask Joe, seems to extract witness *)
  destruct x;
  destruct H;
  rewrite <- H; rewrite inverses';
  apply some_is_not_none with (x := t);
  apply PTree.elements_complete;
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
    (In h (get_headers_from_prog p) <-> In h (get_all_varlike_from_ps PSHeader ps)) /\
    (In sv (get_states_from_prog p) <-> In sv (get_all_varlike_from_ps PSState ps)) /\
    (In c (get_ctrls_from_prog p) <-> In c (get_all_varlike_from_ps PSCtrl ps)).

(* Mark definitions globally opaque below *)
Global Opaque update_varlike_map.
Global Opaque lookup_varlike_map.
Global Opaque program_state_mapper.
Global Opaque new_pmap_from_old.
Global Opaque get_all_varlike_from_ps.
Global Opaque map_from_ps.