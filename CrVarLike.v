Require Import Strings.String.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import InitStatus.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrDsl.
From MyProject Require Import Maps.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

Definition injective_contravariant {A B} (f : A -> B) : Prop :=
  forall x y, x <> y -> f x <> f y.

Definition program_state_mapper {T1 T2 : Type} (fc: T1 -> T2) (fh : T1 -> T2) (fs : T1 -> T2) (s: ProgramState T1) : ProgramState T2 :=
  {| ctrl_map := PMap.map fc (ctrl_map s);
     header_map := PMap.map fh (header_map s);
     state_map := PMap.map fs (state_map s) |}.

Class CrVarLike (A : Type) := {
  make_item : positive -> A;
  get_key   : A -> positive;
  map_from_ps : forall {T}, (ProgramState T) -> PMap.t T;
  lookup_varlike_map : forall {T}, PMap.t T -> A -> T := fun {T} m x => PMap.get (get_key x) m;
  lookup_varlike : forall {T}, (ProgramState T) -> A -> T := fun {T} s x => lookup_varlike_map (map_from_ps s) x;
  update_all_varlike : forall {T}, (ProgramState T) -> (A -> T) -> ProgramState T;
  update_varlike : forall {T}, (ProgramState T) -> A -> T -> ProgramState T;
  is_varlike_in_ps : forall {T}, (ProgramState T) -> A -> option T := fun {T} s v => PTree.get (get_key v) (snd (map_from_ps s));

  (* Simple Lemmas *)
  inverses : forall (x : A), make_item (get_key x) = x;
  inverses' : forall (i : positive), get_key (make_item i) = i;
  inj : injective_contravariant get_key;

  (* Harder lemmas *)
  update_all_varlike_lookup_unchanged :
  forall {T} (s1 : ProgramState T),
  update_all_varlike s1 (fun v : A => lookup_varlike_map (map_from_ps s1) v) = s1;

  commute_lookup_varlike:
  forall {T1 T2} ps v (func : T1 -> T2),
  lookup_varlike (program_state_mapper func func func ps) v = func (lookup_varlike_map (map_from_ps ps) v);

  commute_mapper_update_varlike:
  forall {T1 T2} ps x v (func : T1 -> T2),
  program_state_mapper func func func (update_varlike ps x v) = update_varlike (program_state_mapper func func func ps) x (func v);

  lookup_varlike_after_update_all_varlike:
  forall {T} (s1 : ProgramState T) (v : A) (fv : A -> T),
    is_varlike_in_ps s1 v <> None ->
    lookup_varlike_map (map_from_ps (update_all_varlike s1 fv)) v = fv v;
}.

Class CrVarLikePairLemmas (A A' : Type) `(CrVarLike A) `(CrVarLike A') := {
  test : A; (*TODO: doesn't compile without this. FIX *)
  commute_varlike_updates:
  forall {T} (s1 : ProgramState T)
    (fv : A -> T) (fv' : A' -> T),
    update_all_varlike (update_all_varlike s1 fv') fv =
    update_all_varlike (update_all_varlike s1 fv) fv';
}.

Ltac prove_inj :=
  intros x y Hxy Heq;
  destruct x as [uid1], y as [uid2]; simpl in Heq;
  rewrite Heq in Hxy;
  congruence.

(* Function to go through all keys in a PMap, and set them to new values. *)
Definition new_pmap_from_old {T: Type} (old_pmap : PMap.t T) (f : positive -> T): PMap.t T :=
  (fst old_pmap, (* The old default value *)
   PTree.map (fun x _ => f x) (snd old_pmap) (* Take old tree (snd old_pmap) and map elements from it (x) via function (f) *)
  ).

Ltac prove_update_all_varlike_lookup_unchanged arg :=
  intros T s1;
  destruct s1 as [ctrl hdr state];
  unfold new_pmap_from_old;
  destruct arg as [t t0]; simpl;
  f_equal; f_equal;
  apply PTree.extensionality;
  intros i;
  rewrite PTree.gmap;
  destruct (t0 ! i) eqn:des; auto;
  simpl;
  unfold PMap.get;
  simpl;
  rewrite des;
  reflexivity.

Ltac prove_commute_mapper_update_varlike :=
  intros T1 T2 ps x v func;
  destruct ps;
  unfold program_state_mapper;
  f_equal;
  simpl;
  unfold PMap.set;
  unfold PMap.map;
  simpl;
  f_equal;
  apply PTree.extensionality;
  intros i;
  rewrite PTree.gsspec;
  rewrite PTree.gmap1;
  rewrite PTree.gsspec;
  destruct (Coqlib.peq i _);
  try subst; try reflexivity;
  try rewrite PTree.gmap1; try reflexivity.

Ltac prove_lookup_varlike_after_update_all_varlike :=
  intros T s1 v fv;
  unfold new_pmap_from_old, PMap.get;
  simpl;
  destruct v eqn:des;
  rewrite PTree.gmap;
  unfold Coqlib.option_map;
  lazymatch goal with
  | |- context[match match ?e with _ => _ end with _ => _ end] =>
      let He := fresh "He" in destruct e eqn:He
  end; congruence.

Instance CrVarLike_Header : CrVarLike Header.
Proof.
  refine {| make_item := fun uid => HeaderCtr uid;
            get_key := fun h => match h with HeaderCtr uid => uid end;
            map_from_ps := fun (T : Type) (ps : ProgramState T) => header_map ps;
            update_all_varlike := fun (T : Type) (ps : ProgramState T) (fh : Header -> T) =>
              let new_map := new_pmap_from_old (header_map ps) (fun pos => fh (HeaderCtr pos)) in
              {| ctrl_map := ctrl_map ps;
                 header_map := new_map;
                 state_map := state_map ps |};
            update_varlike := fun (T : Type) (ps : ProgramState T) (h : Header) (v : T) =>
              let new_map := PMap.set (match h with HeaderCtr uid => uid end) v (header_map ps) in
              {| ctrl_map := ctrl_map ps;
                 header_map := new_map;
                 state_map := state_map ps |}; |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [uid]. simpl. reflexivity.
  - (* inverses' : forall i, get_key (make_item i) = i *)
    reflexivity.
  - (* inj : injective_contravariant get_key *)
    prove_inj.
  - (* update_all_varlike_lookup_unchanged : forall {T} (s1 : ProgramState T), update_all_varlike s1 (fun v : A => lookup_varlike_map (map_from_ps s1) v) = s1; *)
    prove_update_all_varlike_lookup_unchanged hdr.
  - (* commute_lookup_varlike:
      forall {T1 T2} (ps : ProgramState T1) (v : A) (func : T1 -> T2), lookup_varlike (program_state_mapper func func func ps) v = func (lookup_varlike_map (map_from_ps ps) v); *)
    intros. apply PMap.gmap.
  - (* commute_mapper_update_varlike:
      forall {T1 T2} (ps : ProgramState T1) (x : A) (v : T1) (func : T1 -> T2),
      program_state_mapper func func func (update_varlike ps x v) = update_varlike (program_state_mapper func func func ps) x (func v) *)
    prove_commute_mapper_update_varlike.
  - (* lookup_varlike_after_update_all_varlike:
      forall {T} (s1 : ProgramState T) (v : A) (fv : A -> T),
        is_varlike_in_ps s1 v <> None ->
        lookup_varlike_map (map_from_ps (update_all_varlike s1 fv)) v = fv v; *)
    prove_lookup_varlike_after_update_all_varlike.
Defined.

Instance CrVarLike_State : CrVarLike State.
Proof.
  refine {| make_item := fun uid => StateCtr uid;
            get_key := fun s => match s with StateCtr uid => uid end;
            map_from_ps := fun (T : Type) (ps : ProgramState T) => state_map ps;
            update_all_varlike := fun (T : Type) (ps : ProgramState T) (fs : State -> T) =>
              let new_map := new_pmap_from_old (state_map ps) (fun pos => fs (StateCtr pos)) in
              {| ctrl_map := ctrl_map ps;
                 header_map := header_map ps;
                 state_map := new_map |};
            update_varlike := fun (T : Type) (ps : ProgramState T) (h : State) (v : T) =>
              let new_map := PMap.set (match h with StateCtr uid => uid end) v (state_map ps) in
              {| ctrl_map := ctrl_map ps;
                 header_map := header_map ps;
                 state_map := new_map |}; |}.
  - intros [uid]. simpl. reflexivity.
  - reflexivity.
  - prove_inj.
  - prove_update_all_varlike_lookup_unchanged state.
  - intros. apply PMap.gmap.
  - prove_commute_mapper_update_varlike.
  - prove_lookup_varlike_after_update_all_varlike.
Defined.

Instance CrVarLike_Ctrl : CrVarLike Ctrl.
Proof.
  refine {| make_item := fun uid => CtrlCtr uid;
            get_key := fun s => match s with CtrlCtr uid => uid end;
            map_from_ps := fun (T : Type) (ps : ProgramState T) => ctrl_map ps;
            update_all_varlike := fun (T : Type) (ps : ProgramState T) (fs : Ctrl -> T) =>
              let new_map := new_pmap_from_old (ctrl_map ps) (fun pos => fs (CtrlCtr pos)) in
              {| ctrl_map := new_map;
                 header_map := header_map ps;
                 state_map := state_map ps |};
            update_varlike := fun (T : Type) (ps : ProgramState T) (h : Ctrl) (v : T) =>
              let new_map := PMap.set (match h with CtrlCtr uid => uid end) v (ctrl_map ps) in
              {| ctrl_map := new_map;
                 header_map := header_map ps;
                 state_map := state_map ps |}; |}.
  - intros [uid]. simpl. reflexivity.
  - reflexivity.
  - prove_inj.
  - prove_update_all_varlike_lookup_unchanged ctrl.
  - intros. apply PMap.gmap.
  - prove_commute_mapper_update_varlike.
  - prove_lookup_varlike_after_update_all_varlike.
Defined.

Section CrVarLikeEqual.

Context {A : Type} `{CrVarLike A}.

Definition varlike_equal (v1 v2 : A) :=
  Pos.eqb (get_key v1) (get_key v2).

Lemma varlike_equal_lemma :
  forall v1 v2,
  varlike_equal v1 v2 = true ->
  v2 = v1.
Proof.
  intros.
  unfold varlike_equal in H0.
  apply Pos.eqb_eq in H0.
  rewrite <- inverses.
  rewrite H0.
  rewrite inverses.
  reflexivity.
Qed.

Fixpoint varlike_list_equal (v1 v2 : list A) :=
  match v1, v2 with
  | nil, nil => true
  | v::y, v'::y' => andb (varlike_equal v v') (varlike_list_equal y y')
  | _, _ => false
  end.

Lemma varlike_list_equal_lemma :
  forall v1 v2,
  varlike_list_equal v1 v2 = true ->
  v1 = v2.
Proof.
  intros.
  revert v2 H0.
  induction v1 as [|v1' v1''].
  - destruct v2.
    + reflexivity.
    + discriminate.
  - destruct v2 as [|v2' v2''].
    + intros. simpl in *. congruence.
    + intros. simpl in *.
      rewrite andb_true_iff in H0. destruct H0.
      apply varlike_equal_lemma in H0.
      apply IHv1'' in H1.
      rewrite H0. rewrite <- H1. reflexivity.
Qed.

End CrVarLikeEqual.

Instance CrVarLikePairLemmas_Header_State : CrVarLikePairLemmas Header State CrVarLike_Header CrVarLike_State.
Proof.
  refine {| test := HeaderCtr xH;|}.
  - intros.
    simpl.
    f_equal.
Defined.

Instance CrVarLikePairLemmas_State_Header : CrVarLikePairLemmas State Header CrVarLike_State CrVarLike_Header.
Proof.
  refine {| test := StateCtr xH;|}.
  - intros.
    simpl.
    f_equal.
Defined.

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
  update_all_varlike (update_all_varlike s1 (fun h : Header => lookup_varlike_map ((@map_from_ps Header CrVarLike_Header T) s1) h))
                    (fun s : State => lookup_varlike_map ((@map_from_ps State CrVarLike_State T) s1) s) = s1.
Proof.
  intros.
  repeat rewrite update_all_varlike_lookup_unchanged.
  reflexivity.
Qed.

(* TODO: Does this hold if A = A'? Similar to lemma before. *)
Lemma is_v1_in_ps_after_update_all_v2:
  forall {T A A'} `{CrVarLike A} `{CrVarLike A'} (s1 : ProgramState T)
    (h : A) (fs : A' -> T),
    is_varlike_in_ps (update_all_varlike s1 fs) h = is_varlike_in_ps s1 h.
Admitted.
(*
Proof.
  intros.
  destruct f1, f2; try congruence;
  reflexivity.
Qed.
*)

Definition get_all_varlike_from_ps {T A : Type} `{CrVarLike A} (s: ProgramState T) : list A :=
  List.map (fun '(key, value) => make_item key)
           (PTree.elements (snd (map_from_ps s))).

Lemma is_varlike_in_ps_lemma :
  forall {T A} `{CrVarLike A} (s1 : ProgramState T) (v : A),
    In v (get_all_varlike_from_ps s1) ->
    is_varlike_in_ps s1 v <> None.
Admitted.
(*
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
*)

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
    (In h (get_headers_from_prog p) <-> In h (get_all_varlike_from_ps ps)) /\
    (In sv (get_states_from_prog p) <-> In sv (get_all_varlike_from_ps ps)) /\
    (In c (get_ctrls_from_prog p) <-> In c (get_all_varlike_from_ps ps)).

(* Mark definitions globally opaque below *)
Global Opaque lookup_varlike_map.
Global Opaque program_state_mapper.
Global Opaque new_pmap_from_old.
Global Opaque get_all_varlike_from_ps.
Global Opaque map_from_ps.