From Stdlib Require Import Strings.String.
From Stdlib Require Import Strings.Ascii.
From Stdlib Require Import micromega.Lia.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrModule.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrTransformer.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrDsl.
From MyProject Require Import Maps.
From MyProject Require Import UtilLemmas.
From MyProject Require Import CrVal.
From Stdlib Require Import ZArith.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

Definition injective_contravariant {A B} (f : A -> B) : Prop :=
  forall x y, x <> y -> f x <> f y.

Definition program_state_mapper {T1 T2 : Type} (fc: T1 -> T2) (fh : T1 -> T2) (fs : T1 -> T2) (s: TransformerState T1) : TransformerState T2 :=
  {| t_ctrl_map := PMap.map fc (t_ctrl_map s);
     t_header_map := PMap.map fh (t_header_map s);
     t_state_map := PMap.map fs (t_state_map s) |}.

Class CrVarLike (A : Type) := {
  make_item : positive -> A;
  get_key   : A -> positive;
  map_from_ps : forall {T}, (TransformerState T) -> PMap.t T;
  lookup_varlike_map : forall {T}, PMap.t T -> A -> T := fun {T} m x => PMap.get (get_key x) m;
  lookup_varlike : forall {T}, (TransformerState T) -> A -> T := fun {T} s x => lookup_varlike_map (map_from_ps s) x;
  update_all_varlike : forall {T}, (TransformerState T) -> (A -> T) -> TransformerState T;
  update_varlike : forall {T}, (TransformerState T) -> A -> T -> TransformerState T;
  is_varlike_in_ps : forall {T}, (TransformerState T) -> A -> option T := fun {T} s v => PTree.get (get_key v) (snd (map_from_ps s));

  (* Simple Lemmas *)
  inverses : forall (x : A), make_item (get_key x) = x;
  inverses' : forall (i : positive), get_key (make_item i) = i;
  inj : injective_contravariant get_key;

  (* Harder lemmas *)
  update_all_varlike_lookup_unchanged :
  forall {T} (s1 : TransformerState T),
  update_all_varlike s1 (fun v : A => lookup_varlike_map (map_from_ps s1) v) = s1;

  commute_lookup_varlike:
  forall {T1 T2} ps v (func : T1 -> T2),
  lookup_varlike (program_state_mapper func func func ps) v = func (lookup_varlike_map (map_from_ps ps) v);

  commute_mapper_update_varlike:
  forall {T1 T2} ps x v (func : T1 -> T2),
  program_state_mapper func func func (update_varlike ps x v) = update_varlike (program_state_mapper func func func ps) x (func v);

  lookup_varlike_after_update_all_varlike:
  forall {T} (s1 : TransformerState T) (v : A) (fv : A -> T),
    is_varlike_in_ps s1 v <> None ->
    lookup_varlike_map (map_from_ps (update_all_varlike s1 fv)) v = fv v;
}.

Class CrVarLikePairLemmas (A A' : Type) `(CrVarLike A) `(CrVarLike A') := {
  commute_varlike_updates:
  forall {T} (s1 : TransformerState T)
    (fv : A -> T) (fv' : A' -> T),
    update_all_varlike (update_all_varlike s1 fv') fv =
    update_all_varlike (update_all_varlike s1 fv) fv';

  is_v1_in_ps_after_update_all_v2:
  forall {T} (s1 : TransformerState T)
    (h : A) (fs : A' -> T),
    is_varlike_in_ps (update_all_varlike s1 fs) h = is_varlike_in_ps s1 h;
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
            map_from_ps := fun (T : Type) (ps : TransformerState T) => t_header_map ps;
            update_all_varlike := fun (T : Type) (ps : TransformerState T) (fh : Header -> T) =>
              let new_map := new_pmap_from_old (t_header_map ps) (fun pos => fh (HeaderCtr pos)) in
              {| t_ctrl_map := t_ctrl_map ps;
                 t_header_map := new_map;
                 t_state_map := t_state_map ps |};
            update_varlike := fun (T : Type) (ps : TransformerState T) (h : Header) (v : T) =>
              let new_map := PMap.set (match h with HeaderCtr uid => uid end) v (t_header_map ps) in
              {| t_ctrl_map := t_ctrl_map ps;
                 t_header_map := new_map;
                 t_state_map := t_state_map ps |}; |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [uid]. simpl. reflexivity.
  - (* inverses' : forall i, get_key (make_item i) = i *)
    reflexivity.
  - (* inj : injective_contravariant get_key *)
    prove_inj.
  - (* update_all_varlike_lookup_unchanged : forall {T} (s1 : TransformerState T), update_all_varlike s1 (fun v : A => lookup_varlike_map (map_from_ps s1) v) = s1; *)
    prove_update_all_varlike_lookup_unchanged hdr.
  - (* commute_lookup_varlike:
      forall {T1 T2} (ps : TransformerState T1) (v : A) (func : T1 -> T2), lookup_varlike (program_state_mapper func func func ps) v = func (lookup_varlike_map (map_from_ps ps) v); *)
    intros. apply PMap.gmap.
  - (* commute_mapper_update_varlike:
      forall {T1 T2} (ps : TransformerState T1) (x : A) (v : T1) (func : T1 -> T2),
      program_state_mapper func func func (update_varlike ps x v) = update_varlike (program_state_mapper func func func ps) x (func v) *)
    prove_commute_mapper_update_varlike.
  - (* lookup_varlike_after_update_all_varlike:
      forall {T} (s1 : TransformerState T) (v : A) (fv : A -> T),
        is_varlike_in_ps s1 v <> None ->
        lookup_varlike_map (map_from_ps (update_all_varlike s1 fv)) v = fv v; *)
    prove_lookup_varlike_after_update_all_varlike.
Defined.

Instance CrVarLike_State : CrVarLike State.
Proof.
  refine {| make_item := fun uid => StateCtr uid;
            get_key := fun s => match s with StateCtr uid => uid end;
            map_from_ps := fun (T : Type) (ps : TransformerState T) => t_state_map ps;
            update_all_varlike := fun (T : Type) (ps : TransformerState T) (fs : State -> T) =>
              let new_map := new_pmap_from_old (t_state_map ps) (fun pos => fs (StateCtr pos)) in
              {| t_ctrl_map := t_ctrl_map ps;
                 t_header_map := t_header_map ps;
                 t_state_map := new_map |};
            update_varlike := fun (T : Type) (ps : TransformerState T) (h : State) (v : T) =>
              let new_map := PMap.set (match h with StateCtr uid => uid end) v (t_state_map ps) in
              {| t_ctrl_map := t_ctrl_map ps;
                 t_header_map := t_header_map ps;
                 t_state_map := new_map |}; |}.
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
            map_from_ps := fun (T : Type) (ps : TransformerState T) => t_ctrl_map ps;
            update_all_varlike := fun (T : Type) (ps : TransformerState T) (fs : Ctrl -> T) =>
              let new_map := new_pmap_from_old (t_ctrl_map ps) (fun pos => fs (CtrlCtr pos)) in
              {| t_ctrl_map := new_map;
                 t_header_map := t_header_map ps;
                 t_state_map := t_state_map ps |};
            update_varlike := fun (T : Type) (ps : TransformerState T) (h : Ctrl) (v : T) =>
              let new_map := PMap.set (match h with CtrlCtr uid => uid end) v (t_ctrl_map ps) in
              {| t_ctrl_map := new_map;
                 t_header_map := t_header_map ps;
                 t_state_map := t_state_map ps |}; |}.
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
  constructor.
  - intros.
    simpl.
    f_equal.
  - intros.
    reflexivity.
Defined.

Instance CrVarLikePairLemmas_State_Header : CrVarLikePairLemmas State Header CrVarLike_State CrVarLike_Header.
Proof.
  constructor.
  - intros.
    simpl.
    f_equal.
  - intros.
    reflexivity.
Defined.

Lemma program_state_equality:
      forall (ps1 ps2: ConcreteTransformerState),
        t_ctrl_map ps1 = t_ctrl_map ps2 ->
        t_header_map ps1 = t_header_map ps2 ->
        t_state_map  ps1 = t_state_map ps2 ->
        ps1 = ps2.
Proof.
  intros ps1 ps2 Hctrl Hhdr Hstate.
  destruct ps1 as [ctrl1 hdr1 state1].
  destruct ps2 as [ctrl2 hdr2 state2].
  simpl in *.
  f_equal; try assumption.
Qed.

Lemma program_state_unchanged:
  forall {T} (s1 : TransformerState T),
  update_all_varlike (update_all_varlike s1 (fun h : Header => lookup_varlike_map ((@map_from_ps Header CrVarLike_Header T) s1) h))
                    (fun s : State => lookup_varlike_map ((@map_from_ps State CrVarLike_State T) s1) s) = s1.
Proof.
  intros.
  repeat rewrite update_all_varlike_lookup_unchanged.
  reflexivity.
Qed.

(* Convert list_norepet of a list of varlikes to list_norepet of their inner ids. *)
Lemma list_norepet_header_inner :
  forall l : list Header,
    Coqlib.list_norepet l ->
    Coqlib.list_norepet (List.map (fun h : Header => match h with HeaderCtr i => i end) l).
Proof.
  intros l Hno.
  apply Coqlib.list_map_norepet; auto.
  intros [i] [j] _ _ Hneq Heq. simpl in Heq. subst. apply Hneq. reflexivity.
Qed.

Lemma list_norepet_state_inner :
  forall l : list State,
    Coqlib.list_norepet l ->
    Coqlib.list_norepet (List.map (fun s : State => match s with StateCtr i => i end) l).
Proof.
  intros l Hno.
  apply Coqlib.list_map_norepet; auto.
  intros [i] [j] _ _ Hneq Heq. simpl in Heq. subst. apply Hneq. reflexivity.
Qed.

Lemma list_norepet_ctrl_inner :
  forall l : list Ctrl,
    Coqlib.list_norepet l ->
    Coqlib.list_norepet (List.map (fun c : Ctrl => match c with CtrlCtr i => i end) l).
Proof.
  intros l Hno.
  apply Coqlib.list_map_norepet; auto.
  intros [i] [j] _ _ Hneq Heq. simpl in Heq. subst. apply Hneq. reflexivity.
Qed.

Definition get_all_varlike_from_ps {T A : Type} `{CrVarLike A} (s: TransformerState T) : list A :=
  List.map (fun '(key, value) => make_item key)
           (PTree.elements (snd (map_from_ps s))).

Lemma is_varlike_in_ps_lemma :
  forall {T A} `{CrVarLike A} (s1 : TransformerState T) (v : A),
    In v (get_all_varlike_from_ps s1) ->
    is_varlike_in_ps s1 v <> None.
Proof.
  intros T A HA s1 v H.
  destruct s1 as [ctrl hdr state].
  unfold get_all_varlike_from_ps in H.
  unfold is_varlike_in_ps.
  simpl in *.
  destruct ctrl as [c0 t_ctrl_map].
  destruct hdr as [h0 hdr_map].
  destruct state as [s0 t_state_map].
  simpl in *.
  apply in_map_iff in H.
  destruct H. (* TODO: ask Joe, seems to extract witness *)
  destruct x.
  destruct H.
  rewrite <- H. rewrite inverses'.
  apply some_is_not_none with (x := t);
  apply PTree.elements_complete;
  assumption.
Qed.

Definition init_concrete_transformer_state (p : CaracaraProgram) : ConcreteTransformerState :=
  let h := get_headers_from_prog p in
  let s := get_states_from_prog p in
  let c := get_ctrls_from_prog p in
  {|t_ctrl_map    :=  PMap.init (UninitVal);
     t_header_map :=  PMap.init (UninitVal);
     t_state_map  :=  PMap.init (UninitVal);|}.

(* Concrete initial state for a parser module: an empty header map and an
   empty input packet (the packet bits are injected at run time).  Mirrors
   [init_concrete_transformer_state]. *)
Definition init_concrete_parser_state : ModuleState CrVal bool :=
  ParserMod {| p_header_map := PMap.init (UninitVal);
               p_packet     := @nil bool;
               p_cursor     := 0 |}.

(* Concrete initial state for a deparser module: an empty header map (filled by
   the upstream module) and an empty output packet. *)
Definition init_concrete_deparser_state : ModuleState CrVal bool :=
  DeparserMod {| p_header_map := PMap.init (UninitVal);
                 p_packet     := @nil bool;
                 p_cursor     := 0 |}.

(* Convert positive to string *)
Fixpoint pos_to_string (p : positive) : string :=
  match p with
  | xH => "1"
  | xO p' => String.append (pos_to_string p') "0"
  | xI p' => String.append (pos_to_string p') "1"
  end.

(* pos_to_string is injective. *)
Lemma pos_to_string_length_ge_1 :
  forall p, (String.length (pos_to_string p) >= 1)%nat.
Proof.
  induction p; simpl; try (rewrite string_length_append; simpl; lia); lia.
Qed.

Local Ltac pos_to_string_inj_same Heq :=
  f_equal;
  match goal with
  | [ IH : forall q : positive, pos_to_string _ = pos_to_string q -> _ = q |- _ ] =>
    apply IH
  end;
  eapply string_append_inj_r_char; exact Heq.
Local Ltac pos_to_string_inj_diff Heq :=
  exfalso; revert Heq;
  apply string_append_neq_r_diff_char;
  intro Hc; inversion Hc.
Local Ltac pos_to_string_inj_length :=
  exfalso;
  match goal with
  | [ Heq : (pos_to_string ?p ++ _)%string = _ |- _ ] =>
    pose proof (pos_to_string_length_ge_1 p);
    apply (f_equal String.length) in Heq;
    rewrite string_length_append in Heq;
    simpl in Heq; lia
  | [ Heq : _ = (pos_to_string ?p ++ _)%string |- _ ] =>
    pose proof (pos_to_string_length_ge_1 p);
    apply (f_equal String.length) in Heq;
    rewrite string_length_append in Heq;
    simpl in Heq; lia
  end.
Lemma pos_to_string_inj :
  forall p1 p2, pos_to_string p1 = pos_to_string p2 -> p1 = p2.
Proof.
  induction p1; intros p2 Heq; destruct p2; simpl in Heq;
    first [ reflexivity
          | pos_to_string_inj_same Heq
          | pos_to_string_inj_diff Heq
          | pos_to_string_inj_length ].
Qed.

Local Open Scope string_scope.
Definition init_symbolic_transformer_state (prefix: string) (p: CaracaraProgram) : SymbolicTransformerState :=
  let h := get_headers_from_prog p in
  let s := get_states_from_prog p in
  let c := get_ctrls_from_prog p in
  {| t_ctrl_map   :=  (SmtUninit,
                      PTree_Properties.of_list
                      (List.map (fun x => let x' := unwrap x in (x', SmtArithVar (prefix ++ "ctrl_" ++ pos_to_string x'))) c));
     t_header_map :=  (SmtUninit,
                      PTree_Properties.of_list
                      (List.map (fun x => let x' := unwrap x in (x', SmtArithVar ("hdr_" ++ pos_to_string x'))) h));
     t_state_map  :=  (SmtUninit,
                      PTree_Properties.of_list
                      (List.map (fun x => let x' := unwrap x in (x', SmtArithVar (prefix ++ "state_" ++ pos_to_string x'))) s));|}.
Definition init_symbolic_transformer_state' (p : CaracaraProgram) : SymbolicTransformerState :=
  init_symbolic_transformer_state "" p.

Definition init_symbolic_parser_state (prefix : string) (h : list Header) : SymbolicParserState :=
  {| p_header_map := (SmtUninit,
                     PTree_Properties.of_list
                     (List.map (fun x => let x' := unwrap x in (x', SmtArithVar ("hdr_" ++ pos_to_string x'))) h));
     p_packet := @nil SmtBoolExpr;
     p_cursor := 0 |}.

(* Symbolic parser start state over a packet of exactly [n] unknown bits: each
   bit is a free [SmtBoolVar "pkt_i"].  Two parsers seeded this way share the
   same bit variables, so the solver quantifies over one common input packet. *)
Definition init_symbolic_parser_state_n (h : list Header) (n : nat) : SymbolicParserState :=
  {| p_header_map := (SmtUninit,
                     PTree_Properties.of_list
                     (List.map (fun x => let x' := unwrap x in (x', SmtArithVar ("hdr_" ++ pos_to_string x'))) h));
     p_packet := List.map
                   (fun i => SmtBoolVar ("pkt_" ++ pos_to_string (Pos.of_succ_nat i)))
                   (List.seq 0 n);
     p_cursor := 0 |}.

Definition init_sym_t_state (prog_prefix : string) (m_id : ModuleName) (p : CaracaraProgram)
  : SymbolicTransformerState :=
  let prefix := prog_prefix ++ "_m" ++ pos_to_string (unwrap m_id) ++ "_" in
  init_symbolic_transformer_state prefix p.

Definition init_sym_p_state (prog_prefix : string) (m_id : ModuleName) (h : list Header)
  : SymbolicParserState :=
  let prefix := prog_prefix ++ "_m" ++ pos_to_string (unwrap m_id) ++ "_" in
  init_symbolic_parser_state prefix h.

Definition collect_write_headers (mods : list CrModule) : list Header :=
  List.flat_map (fun m =>
    match m with
    | ParserModule _ _ => []
    | DeparserModule _ _ => []
    | TransformerModule _ _ _ t =>
      List.flat_map (fun rule =>
        match rule with
        | Seq (SeqCtr _ ops) => snd (extract_all_targets ops)
        | Par (ParCtr _ ops) => snd (extract_all_targets (proj1_sig ops))
        end) t
    end) mods.

Definition init_general_symbolic_state
    (prog_prefix : string)
    (p : GeneralCaracaraProgram)
    : GeneralSymbolicState :=
  let net := get_network_from_general p in
  let mods := net_modules net in
  let h := get_headers_from_general p in
  let write_hdrs := collect_write_headers mods in
  let ms := List.fold_left
    (fun acc m =>
      match m with
      | ParserModule m_id _ =>
        let base := init_sym_p_state prog_prefix m_id h in
        PMap.set (unwrap m_id) (ParserMod base) acc
      | DeparserModule m_id _ =>
        (* A deparser reads the same header interface as a parser; seed its
           header map with the shared symbolic header variables. *)
        let base := init_sym_p_state prog_prefix m_id h in
        PMap.set (unwrap m_id) (DeparserMod base) acc
      | TransformerModule m_id s c t =>
        let local_program := CaracaraProgramDef h s c [] in
        let base := init_sym_t_state prog_prefix m_id local_program in
        (* Seed each write-target header explicitly in the PTree so that
          update_all_varlike will track it after eval_transformer_smt runs.
          For input headers already present this is a no-op; for output-only
          headers it installs their PMap default (CrNilInt) as an explicit entry. *)
        let seeded := List.fold_left
          (fun st wh => update_varlike st wh (lookup_varlike st wh))
          write_hdrs base in
        PMap.set (unwrap m_id) (TransformerMod seeded) acc
      end)
    mods
    (PMap.init (TransformerMod {|
      t_ctrl_map := PMap.init (SmtUninit);
      t_header_map := PMap.init (SmtUninit);
      t_state_map := PMap.init (SmtUninit);
    |})) in
  (* Shared global header channel: seed with the un-prefixed input header
     symbolic variables (the shared cross-module/cross-program interface). *)
  let sh_hdr := p_header_map (init_symbolic_parser_state "" h) in
  {| sh_hdr_map := sh_hdr;
     sh_bit_map := @nil SmtBoolExpr;
     mod_states := ms |}.

(* The [n]-bit shared symbolic input packet [pkt_1 .. pkt_n]: the free bit
   variables that both programs range over.  Un-prefixed (like the shared
   header channel), so seeding two programs with these makes the solver
   quantify over one common input bitstream.  Mirrors the packet seeding in
   [init_symbolic_parser_state_n]. *)
Definition symbolic_input_bits (n : nat) : list SmtBoolExpr :=
  List.map (fun i => SmtBoolVar ("pkt_" ++ pos_to_string (Pos.of_succ_nat i)))
           (List.seq 0 n).

(* [init_general_symbolic_state] with the shared bit channel seeded by an
   [n]-bit symbolic input packet.  Used for bitstream-input / bitstream-output
   equivalence: the network's source consumes these bits and its sink emits an
   output bitstream over them. *)
Definition init_general_symbolic_state_n
    (prog_prefix : string) (p : GeneralCaracaraProgram) (n : nat)
    : GeneralSymbolicState :=
  set_gps_shared_bits (init_general_symbolic_state prog_prefix p)
                      (symbolic_input_bits n).

Definition init_general_concrete_state (p : GeneralCaracaraProgram)
    : GeneralConcreteState :=
  let net := get_network_from_general p in
  let ms := List.fold_left
    (fun acc m =>
      match m with
      | ParserModule m_id _ =>
          PMap.set (unwrap m_id) init_concrete_parser_state acc
      | DeparserModule m_id _ =>
          PMap.set (unwrap m_id) init_concrete_deparser_state acc
      | TransformerModule m_id s c _ =>
          PMap.set (unwrap m_id)
            (TransformerMod (init_concrete_transformer_state (CaracaraProgramDef [] s c []))) acc
      end)
    (net_modules net)
    (PMap.init (TransformerMod (init_concrete_transformer_state (CaracaraProgramDef [] [] [] [])))) in
  {| sh_hdr_map := PMap.init (UninitVal);
     sh_bit_map := @nil bool;
     mod_states := ms |}.

Definition is_init_state {T} (p : CaracaraProgram) (ps : TransformerState T) : Prop :=
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
