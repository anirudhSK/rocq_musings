From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import Maps.
From MyProject Require Import UtilLemmas.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrVal.
From MyProject Require Import CrDsl.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Strings.String.
Import ListNotations.

Transparent map_from_ps.
Transparent lookup_varlike_map.

Class CrVarLikeEval (A: Type) `(CrVarLike A) := {
  commute_lookup_eval_generic:
  forall (v : A) f ps,
  lookup_varlike_map (map_from_ps (eval_sym_state ps f)) v =
  eval_smt_arith (lookup_varlike_map (map_from_ps ps) v) f;
}.

Instance CrVarLikeEval_Header : CrVarLikeEval Header CrVarLike_Header.
Proof.
  constructor.
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

Instance CrVarLikeEval_State : CrVarLikeEval State CrVarLike_State.
Proof.
  constructor.
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

Instance CrVarLikeEval_Ctrl : CrVarLikeEval Ctrl CrVarLike_Ctrl.
Proof.
  constructor.
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

(* Same as the above lemma for hdr and state *)
Lemma ptree_of_list_lemma_generic:
    forall (X : Type) `(CrVarLike X)
    (l : list X) (val_fn : X -> SmtArithExpr)
    (x : X),
    Coqlib.list_norepet l ->
    In x l ->
    In x (map (fun '(key, _) => make_item key)
    (PTree.elements (PTree_Properties.of_list (combine (map get_key l) (map val_fn l))))).
Proof.
  intros X crvarlike l val_fn x H' H.
  generalize H as H_in.
  apply functional_list_helper with (key_fn := get_key) (val_fn := val_fn) in H.
  intros.
  remember (fun '(key, _) => make_item key) as f.
  assert(H_tmp: x =
          f (get_key x, val_fn (x))). {
  rewrite Heqf.
  rewrite (inverses x).
  reflexivity. }
  rewrite H_tmp.
  apply in_map with (f := f) (x := (get_key x, val_fn x)) (l := (PTree.elements
  (PTree_Properties.of_list (combine (map get_key l) (map val_fn l))))).
  remember (get_key x, val_fn x) as pair_val.
  remember (combine (map get_key l) (map val_fn l)) as l_combined.
  rewrite Heqpair_val in *.
  apply PTree.elements_correct with (m := PTree_Properties.of_list l_combined).
  apply PTree_Properties.of_list_norepet.
  - rewrite Heql_combined.
    simpl.
    rewrite map_combine2.
    apply Coqlib.list_map_norepet.
    -- assumption.
    -- intros.
       apply (inj x0 y).
       assumption.
  - simpl in H. rewrite Heqf in H_tmp.
    rewrite H_tmp.
    rewrite inverses.
    assumption.
Qed.

(* ============================================================ *)
(*  Bridge: lookup_varlike <-> PMap.get                          *)
(* ============================================================ *)
(* These are essentially definitional, but stating them as       *)
(* lemmas makes them easy to use with `rewrite`.                  *)

Lemma lookup_varlike_header_PMap :
  forall (s : SymbolicTransformerState) (id : positive),
    lookup_varlike s (HeaderCtr id) = PMap.get id (t_header_map s).
Proof.
  intros. reflexivity.
Qed.

Lemma lookup_varlike_state_PMap :
  forall (s : SymbolicTransformerState) (id : positive),
    lookup_varlike s (StateCtr id) = PMap.get id (t_state_map s).
Proof.
  intros. reflexivity.
Qed.

Lemma lookup_varlike_ctrl_PMap :
  forall (s : SymbolicTransformerState) (id : positive),
    lookup_varlike s (CtrlCtr id) = PMap.get id (t_ctrl_map s).
Proof.
  intros. reflexivity.
Qed.

Lemma lookup_varlike_header_PMap_concrete :
  forall (s : ConcreteTransformerState) (id : positive),
    lookup_varlike s (HeaderCtr id) = PMap.get id (t_header_map s).
Proof.
  intros. reflexivity.
Qed.

Lemma lookup_varlike_state_PMap_concrete :
  forall (s : ConcreteTransformerState) (id : positive),
    lookup_varlike s (StateCtr id) = PMap.get id (t_state_map s).
Proof.
  intros. reflexivity.
Qed.

Lemma lookup_varlike_ctrl_PMap_concrete :
  forall (s : ConcreteTransformerState) (id : positive),
    lookup_varlike s (CtrlCtr id) = PMap.get id (t_ctrl_map s).
Proof.
  intros. reflexivity.
Qed.

(* ============================================================ *)
(*  When the PMap default is (UninitVal), every non-default        *)
(*  lookup result must come from an entry in the underlying      *)
(*  PTree.                                                        *)
(* ============================================================ *)

Lemma cs_initialized_in_tree_header :
  forall (cs : ConcreteTransformerState) id w,
    fst (t_header_map cs) = (UninitVal) ->
    PMap.get id (t_header_map cs) = w ->
    w <> (UninitVal) ->
    (snd (t_header_map cs)) ! id = Some w.
Proof.
  intros cs id w Hdef Heq Hneq.
  unfold PMap.get in Heq.
  destruct ((snd (t_header_map cs)) ! id) eqn:Hget.
  - subst. reflexivity.
  - subst. contradiction.
Qed.

Lemma cs_initialized_in_tree_state :
  forall (cs : ConcreteTransformerState) id w,
    fst (t_state_map cs) = (UninitVal) ->
    PMap.get id (t_state_map cs) = w ->
    w <> (UninitVal) ->
    (snd (t_state_map cs)) ! id = Some w.
Proof.
  intros cs id w Hdef Heq Hneq.
  unfold PMap.get in Heq.
  destruct ((snd (t_state_map cs)) ! id) eqn:Hget.
  - subst. reflexivity.
  - subst. contradiction.
Qed.

Lemma cs_initialized_in_tree_ctrl :
  forall (cs : ConcreteTransformerState) id w,
    fst (t_ctrl_map cs) = (UninitVal) ->
    PMap.get id (t_ctrl_map cs) = w ->
    w <> (UninitVal) ->
    (snd (t_ctrl_map cs)) ! id = Some w.
Proof.
  intros cs id w Hdef Heq Hneq.
  unfold PMap.get in Heq.
  destruct ((snd (t_ctrl_map cs)) ! id) eqn:Hget.
  - subst. reflexivity.
  - subst. contradiction.
Qed.

(* ============================================================ *)
(*  Lookup of init_symbolic_state for keys present in the lists  *)
(* ============================================================ *)

Lemma init_sym_header_lookup :
  forall hlist slist clist (id : positive),
    Coqlib.list_norepet (List.map (fun (h : Header) => match h with HeaderCtr i => i end) hlist) ->
    In (HeaderCtr id) hlist ->
    PMap.get id (t_header_map (init_symbolic_transformer_state' (CaracaraProgramDef hlist slist clist []))) =
      SmtArithVar ("hdr_" ++ pos_to_string id)%string.
Proof.
  intros hlist slist clist id Hno Hin.
  unfold init_symbolic_transformer_state', PMap.get. simpl.
  set (l := List.map (fun x : Header =>
              let var := match x with HeaderCtr x_id => x_id end in
              (var, SmtArithVar ("hdr_" ++ pos_to_string var))) hlist).
  assert (Hl_nrep : Coqlib.list_norepet (List.map fst l)).
  { subst l. rewrite map_map. simpl.
    erewrite map_ext.
    - exact Hno.
    - intros [i]. reflexivity. }
  assert (Hl_in : In (id, SmtArithVar ("hdr_" ++ pos_to_string id)%string) l).
  { subst l. apply in_map_iff. exists (HeaderCtr id). split; auto. }
  pose proof (PTree_Properties.of_list_norepet l id _ Hl_nrep Hl_in) as Hget.
  change (match (PTree_Properties.of_list l) ! id with
          | Some x => x
          | None => SmtUninit
          end = SmtArithVar ("hdr_" ++ pos_to_string id)%string).
  rewrite Hget. reflexivity.
Qed.

Lemma init_sym_state_lookup :
  forall hlist slist clist (id : positive),
    Coqlib.list_norepet (List.map (fun (s : State) => match s with StateCtr i => i end) slist) ->
    In (StateCtr id) slist ->
    PMap.get id (t_state_map (init_symbolic_transformer_state' (CaracaraProgramDef hlist slist clist []))) =
      SmtArithVar ("state_" ++ pos_to_string id)%string.
Proof.
  intros hlist slist clist id Hno Hin.
  unfold init_symbolic_transformer_state', PMap.get. simpl.
  set (l := List.map (fun x : State =>
              let var := match x with StateCtr x_id => x_id end in
              (var, SmtArithVar ("state_" ++ pos_to_string var))) slist).
  assert (Hl_nrep : Coqlib.list_norepet (List.map fst l)).
  { subst l. rewrite map_map. simpl.
    erewrite map_ext.
    - exact Hno.
    - intros [i]. reflexivity. }
  assert (Hl_in : In (id, SmtArithVar ("state_" ++ pos_to_string id)%string) l).
  { subst l. apply in_map_iff. exists (StateCtr id). split; auto. }
  pose proof (PTree_Properties.of_list_norepet l id _ Hl_nrep Hl_in) as Hget.
  change (match (PTree_Properties.of_list l) ! id with
          | Some x => x
          | None => SmtUninit
          end = SmtArithVar ("state_" ++ pos_to_string id)%string).
  rewrite Hget. reflexivity.
Qed.

Lemma init_sym_ctrl_lookup :
  forall hlist slist clist (id : positive),
    Coqlib.list_norepet (List.map (fun (c : Ctrl) => match c with CtrlCtr i => i end) clist) ->
    In (CtrlCtr id) clist ->
    PMap.get id (t_ctrl_map (init_symbolic_transformer_state' (CaracaraProgramDef hlist slist clist []))) =
      SmtArithVar ("ctrl_" ++ pos_to_string id)%string.
Proof.
  intros hlist slist clist id Hno Hin.
  unfold init_symbolic_transformer_state', PMap.get. simpl.
  set (l := List.map (fun x : Ctrl =>
              let var := match x with CtrlCtr x_id => x_id end in
              (var, SmtArithVar ("ctrl_" ++ pos_to_string var))) clist).
  assert (Hl_nrep : Coqlib.list_norepet (List.map fst l)).
  { subst l. rewrite map_map. simpl.
    erewrite map_ext.
    - exact Hno.
    - intros [i]. reflexivity. }
  assert (Hl_in : In (id, SmtArithVar ("ctrl_" ++ pos_to_string id)%string) l).
  { subst l. apply in_map_iff. exists (CtrlCtr id). split; auto. }
  pose proof (PTree_Properties.of_list_norepet l id _ Hl_nrep Hl_in) as Hget.
  change (match (PTree_Properties.of_list l) ! id with
          | Some x => x
          | None => SmtUninit
          end = SmtArithVar ("ctrl_" ++ pos_to_string id)%string).
  rewrite Hget. reflexivity.
Qed.

(* ============================================================ *)
(*  init_symbolic_state lookup default for keys NOT in the list  *)
(* ============================================================ *)

Lemma init_sym_header_lookup_default :
  forall (p : CaracaraProgram) (id : positive),
    ~ In (HeaderCtr id) (get_headers_from_prog p) ->
    PMap.get id (t_header_map (init_symbolic_transformer_state' p)) = SmtUninit.
Proof.
  intros p id Hnin.
  unfold init_symbolic_transformer_state',
         init_symbolic_transformer_state,
         PMap.get.
  cbn [snd fst t_header_map].
  match goal with
  | |- match (PTree_Properties.of_list ?L) ! id with _ => _ end = _ =>
      destruct ((PTree_Properties.of_list L) ! id) eqn:Hget; [exfalso | reflexivity];
      apply PTree_Properties.in_of_list in Hget;
      apply in_map_iff in Hget; destruct Hget as [[i] [Hpair Hin']];
      inversion Hpair; subst i; apply Hnin; assumption
  end.
Qed.

Lemma init_sym_state_lookup_default :
  forall (p : CaracaraProgram) (id : positive),
    ~ In (StateCtr id) (get_states_from_prog p) ->
    PMap.get id (t_state_map (init_symbolic_transformer_state' p)) = SmtUninit.
Proof.
  intros p id Hnin.
  unfold init_symbolic_transformer_state',
         init_symbolic_transformer_state,
         PMap.get.
  cbn [snd fst t_state_map].
  match goal with
  | |- match (PTree_Properties.of_list ?L) ! id with _ => _ end = _ =>
      destruct ((PTree_Properties.of_list L) ! id) eqn:Hget; [exfalso | reflexivity];
      apply PTree_Properties.in_of_list in Hget;
      apply in_map_iff in Hget; destruct Hget as [[i] [Hpair Hin']];
      inversion Hpair; subst i; apply Hnin; assumption
  end.
Qed.

Lemma init_sym_ctrl_lookup_default :
  forall (p : CaracaraProgram) (id : positive),
    ~ In (CtrlCtr id) (get_ctrls_from_prog p) ->
    PMap.get id (t_ctrl_map (init_symbolic_transformer_state' p)) = SmtUninit.
Proof.
  intros p id Hnin.
  unfold init_symbolic_transformer_state',
         init_symbolic_transformer_state,
         PMap.get.
  cbn [snd fst t_ctrl_map].
  match goal with
  | |- match (PTree_Properties.of_list ?L) ! id with _ => _ end = _ =>
      destruct ((PTree_Properties.of_list L) ! id) eqn:Hget; [exfalso | reflexivity];
      apply PTree_Properties.in_of_list in Hget;
      apply in_map_iff in Hget; destruct Hget as [[i] [Hpair Hin']];
      inversion Hpair; subst i; apply Hnin; assumption
  end.
Qed.

(* ============================================================ *)
(*  lookup_varlike after update_varlike                          *)
(* ============================================================ *)
(* Same-type updates: lookup at the same id returns the new      *)
(* value; lookup at a different id returns the original.         *)
(* Cross-type updates do not affect the other map.               *)

Lemma lookup_update_header_header :
  forall (ps : ConcreteTransformerState) (h h' : Header) (x : CrVal),
  lookup_varlike (update_varlike ps h x) h' =
    match h, h' with
    | HeaderCtr hid, HeaderCtr hid' =>
      if Coqlib.peq hid' hid then x else lookup_varlike ps h'
    end.
Proof.
  intros ps [hid] [hid'] x.
  unfold update_varlike, lookup_varlike, lookup_varlike_map, map_from_ps, get_key.
  simpl. rewrite PMap.gsspec. destruct (Coqlib.peq hid' hid); reflexivity.
Qed.

Lemma lookup_update_state_state :
  forall (ps : ConcreteTransformerState) (s s' : State) (x : CrVal),
  lookup_varlike (update_varlike ps s x) s' =
    match s, s' with
    | StateCtr sid, StateCtr sid' =>
      if Coqlib.peq sid' sid then x else lookup_varlike ps s'
    end.
Proof.
  intros ps [sid] [sid'] x.
  unfold update_varlike, lookup_varlike, lookup_varlike_map, map_from_ps, get_key.
  simpl. rewrite PMap.gsspec. destruct (Coqlib.peq sid' sid); reflexivity.
Qed.

Lemma lookup_update_ctrl_ctrl :
  forall (ps : ConcreteTransformerState) (c c' : Ctrl) (x : CrVal),
  lookup_varlike (update_varlike ps c x) c' =
    match c, c' with
    | CtrlCtr cid, CtrlCtr cid' =>
      if Coqlib.peq cid' cid then x else lookup_varlike ps c'
    end.
Proof.
  intros ps [cid] [cid'] x.
  unfold update_varlike, lookup_varlike, lookup_varlike_map, map_from_ps, get_key.
  simpl. rewrite PMap.gsspec. destruct (Coqlib.peq cid' cid); reflexivity.
Qed.

(* Cross-type updates (e.g. update on Header doesn't affect State / Ctrl maps)
   are definitional, so [reflexivity] / direct application discharges them
   without an intermediate lemma. *)

(* [PMap.map] commutes with [PMap.set]. *)
Lemma pmap_map_set : forall (A B : Type) (g : A -> B) (k : positive) (v : A) (m : PMap.t A),
  PMap.map g (PMap.set k v m) = PMap.set k (g v) (PMap.map g m).
Proof.
  intros A B g k v m. unfold PMap.map, PMap.set. simpl. f_equal.
  apply PTree.extensionality. intro i.
  rewrite PTree.gmap1, !PTree.gsspec, PTree.gmap1.
  destruct (Coqlib.peq i k); reflexivity.
Qed.

Global Opaque lookup_varlike_map.
