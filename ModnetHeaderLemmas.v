(* ================================================================== *)
(* Network-level commutation for TRANSFORMER-ONLY linear chains.        *)
(*                                                                     *)
(* Goal: discharge [modnet_header_equivalence_checker_sound/_complete]  *)
(* (in SmtModuleQuery.v) for networks whose modules are all transformers.*)
(*                                                                     *)
(* Strategy (see the session notes): run the concrete and symbolic       *)
(* network semantics in LOCKSTEP.  Transformer-only means every module    *)
(* eval returns [Some], so both runs have identical control flow; we      *)
(* thread a per-slot agreement [ts_agree] (each concrete transformer      *)
(* state agrees, at every variable lookup, with the [f]-concretization of  *)
(* the symbolic one).  The single-transformer step reuses the existing     *)
(* [eval_transformer_concrete_preserves_eq] (congruence) +                 *)
(* [commute_sym_vs_conc_transformer_*] (commute).  Sink extraction then     *)
(* falls out of the checker's [Some [TransformerMod sym]] hypothesis, so no *)
(* graph-reachability reasoning is needed.                                  *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrTransformer.
From MyProject Require Import ListUtils.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrVarLike.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import ConcreteToSymbolicLemmas.
From MyProject Require Import ConcreteTransformerLemmas.
From MyProject Require Import Maps.

(* A concrete transformer state agrees with the [f]-concretization of a
   symbolic one at every program-variable lookup. *)
Definition ts_agree (cs : ConcreteTransformerState)
                    (ss : SymbolicTransformerState) (f : SmtValuation) : Prop :=
  cs_lookup_eq cs (eval_sym_state ss f).

(* Header-map agreement: a concrete header map is the [f]-concretization of a
   symbolic one at every header lookup. *)
Definition hm_agree (hmc : PMap.t CrVal) (hms : PMap.t SmtArithExpr)
                    (f : SmtValuation) : Prop :=
  forall h : Header,
    lookup_varlike_map hmc h = eval_smt_arith (lookup_varlike_map hms h) f.

Transparent lookup_varlike_map map_from_ps lookup_varlike.

(* A header lookup on a transformer state reads exactly its header map. *)
Lemma lookup_varlike_hdr_is_map :
  forall {T} (ts : TransformerState T) (h : Header),
    lookup_varlike ts h = lookup_varlike_map (t_header_map ts) h.
Proof. reflexivity. Qed.

(* [ts_agree] projects to header-map agreement. *)
Lemma ts_agree_hm :
  forall cs ss f,
    ts_agree cs ss f ->
    hm_agree (t_header_map cs) (t_header_map ss) f.
Proof.
  intros cs ss f [Hh _] h.
  specialize (Hh h).
  rewrite lookup_varlike_hdr_is_map in Hh.
  rewrite Hh.
  (* lookup on eval_sym_state = eval_smt of the symbolic lookup *)
  unfold eval_sym_state.
  rewrite commute_lookup_varlike.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The per-module step, present-variable case.  Given input agreement    *)
(* [ts_agree] (concrete input = f-concretization of symbolic input at      *)
(* every lookup) and that [h] is present in the symbolic input, the         *)
(* concrete transformer output at [h] is the f-concretization of the         *)
(* symbolic transformer output at [h].  Combines the existing congruence      *)
(* ([eval_transformer_concrete_preserves_eq]) with the commute lemma.         *)
Lemma transformer_step_hdr_present :
  forall t f IN_c IN_s (h : Header),
    ts_agree IN_c IN_s f ->
    is_varlike_in_ps IN_s h <> None ->
    lookup_varlike (eval_transformer_concrete t IN_c) h
      = eval_smt_arith (lookup_varlike (eval_transformer_smt t IN_s) h) f.
Proof.
  intros t f IN_c IN_s h Hag Hpres.
  unfold ts_agree in Hag.
  (* Congruence: concrete eval respects lookup-agreement of its input. *)
  pose proof (eval_transformer_concrete_preserves_eq _ _ t Hag) as [Hh _].
  specialize (Hh h).
  rewrite Hh.
  (* Commute: at a present header, concrete-of-concretized = concretize-of-symbolic. *)
  rewrite (commute_sym_vs_conc_transformer_header_map t f IN_s h Hpres).
  unfold eval_sym_state at 1.
  rewrite commute_lookup_varlike.
  reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Absent-header handling.  A header that no operation writes is left       *)
(* unchanged by a transformer (concrete side); a header absent from the      *)
(* symbolic state is left at its default (symbolic side).  Together these     *)
(* discharge the [ts_agree] step at headers NOT present in the input.         *)

Transparent update_varlike.
Transparent new_pmap_from_old.

Definition rule_ops (r : MatchActionRule) : list HdrOp :=
  match r with
  | Seq (SeqCtr _ ops) => ops
  | Par (ParCtr _ ops) => proj1_sig ops
  end.

(* [find_first_match] returns a rule drawn from the underlying list. *)
Lemma find_first_match_in :
  forall {T : Set} (bs : list bool) (l : list T) r,
    find_first_match (combine bs l) = Some r -> In r l.
Proof.
  induction bs as [|b bs IH]; intros l r H.
  - destruct l; simpl in H; discriminate.
  - destruct l as [|x xs]; simpl in H.
    + discriminate.
    + destruct b.
      * inversion H; subst. left. reflexivity.
      * right. eapply IH. exact H.
Qed.

(* One op writes only its own header target: a header lookup at [h] is
   unchanged when [h] is not the op's header target. *)
Lemma eval_hdr_op_assign_concrete_absent_hdr :
  forall op c (h : Header),
    ~ In h (snd (extract_targets op)) ->
    lookup_varlike (eval_hdr_op_assign_concrete op c) h = lookup_varlike c h.
Proof.
  intros op c h Hni.
  destruct op as [f ty a1 a2 tgt | f ty a1 a2 tgt | from to a tgt | from to a tgt];
    unfold eval_hdr_op_assign_concrete.
  - (* StatefulOp: State target; header lookup unaffected (cross-type). *)
    reflexivity.
  - (* StatelessOp: Header target [tgt]. *)
    rewrite lookup_update_header_header.
    destruct h as [hid], tgt as [tid].
    destruct (Coqlib.peq hid tid) as [He|Hne]; [| reflexivity].
    exfalso. apply Hni. cbn. left. congruence.
  - reflexivity.
  - rewrite lookup_update_header_header.
    destruct h as [hid], tgt as [tid].
    destruct (Coqlib.peq hid tid) as [He|Hne]; [| reflexivity].
    exfalso. apply Hni. cbn. left. congruence.
Qed.

Lemma eval_hdr_op_list_concrete_absent_hdr :
  forall hol c (h : Header),
    (forall op, In op hol -> ~ In h (snd (extract_targets op))) ->
    lookup_varlike (eval_hdr_op_list_concrete hol c) h = lookup_varlike c h.
Proof.
  induction hol as [|op rest IH]; intros c h Hall.
  - reflexivity.
  - simpl.
    rewrite IH by (intros op' Hin'; apply Hall; right; exact Hin').
    apply eval_hdr_op_assign_concrete_absent_hdr. apply Hall. left. reflexivity.
Qed.

Lemma eval_match_action_rule_concrete_absent_hdr :
  forall r c (h : Header),
    (forall op, In op (rule_ops r) -> ~ In h (snd (extract_targets op))) ->
    lookup_varlike (eval_match_action_rule_concrete r c) h = lookup_varlike c h.
Proof.
  intros [ [mp action] | [mp action] ] c h Hops; simpl;
    destruct (eval_match_concrete mp c);
    solve [ apply eval_hdr_op_list_concrete_absent_hdr; exact Hops | reflexivity ].
Qed.

Lemma eval_transformer_concrete_absent_hdr :
  forall t c (h : Header),
    (forall r, In r t ->
       forall op, In op (rule_ops r) -> ~ In h (snd (extract_targets op))) ->
    lookup_varlike (eval_transformer_concrete t c) h = lookup_varlike c h.
Proof.
  intros t c h Ht. unfold eval_transformer_concrete.
  destruct (find_first_match (combine (get_match_results t c) t)) as [r|] eqn:Hf.
  - apply eval_match_action_rule_concrete_absent_hdr.
    intros op Hop. apply (Ht r).
    + eapply find_first_match_in. exact Hf.
    + exact Hop.
  - reflexivity.
Qed.

(* [new_pmap_from_old] only rewrites existing keys, so an absent key keeps
   the map's default (i.e. its old [PMap.get]). *)
Lemma new_pmap_from_old_absent :
  forall {T} (m : PMap.t T) (g : positive -> T) i,
    PTree.get i (snd m) = None ->
    PMap.get i (new_pmap_from_old m g) = PMap.get i m.
Proof.
  intros T m g i H.
  unfold PMap.get, new_pmap_from_old. cbn [fst snd].
  rewrite PTree.gmap, H. cbn. reflexivity.
Qed.

(* Symbolic side: [update_all_varlike] (Header) rewrites existing keys only,
   so a header absent from the state keeps its default value. *)
Lemma update_all_varlike_hdr_absent :
  forall {T} (ps : TransformerState T) (fh : Header -> T) (h : Header),
    is_varlike_in_ps ps h = None ->
    lookup_varlike (@update_all_varlike Header _ T ps fh) h = lookup_varlike ps h.
Proof.
  intros T ps fh [hid] Habs.
  unfold is_varlike_in_ps in Habs.
  cbn [map_from_ps CrVarLike_Header get_key] in Habs.
  unfold lookup_varlike, lookup_varlike_map.
  cbn [update_all_varlike CrVarLike_Header map_from_ps get_key].
  apply new_pmap_from_old_absent. exact Habs.
Qed.

(* Cross-type: a State [update_all_varlike] leaves header lookups alone. *)
Lemma update_all_varlike_state_hdr :
  forall {T} (ps : TransformerState T) (fs : State -> T) (h : Header),
    lookup_varlike (@update_all_varlike State _ T ps fs) h = lookup_varlike ps h.
Proof.
  intros T ps fs [hid].
  unfold lookup_varlike, lookup_varlike_map.
  cbn [update_all_varlike CrVarLike_State map_from_ps CrVarLike_Header get_key].
  reflexivity.
Qed.

Lemma eval_transformer_smt_absent_hdr :
  forall t s (h : Header),
    is_varlike_in_ps s h = None ->
    lookup_varlike (eval_transformer_smt t s) h = lookup_varlike s h.
Proof.
  intros t s h Habs.
  unfold eval_transformer_smt.
  rewrite update_all_varlike_state_hdr.
  rewrite update_all_varlike_hdr_absent by exact Habs.
  reflexivity.
Qed.

(* The set of headers a transformer may write. *)
Definition t_write_hdrs (t : Transformer) : list Header :=
  List.flat_map (fun r => snd (extract_all_targets (rule_ops r))) t.

(* [In h (snd acc)] is preserved by the [extract_all_targets] fold. *)
Lemma fold_eat_snd_mono :
  forall ops acc h,
    In h (snd acc) ->
    In h (snd (List.fold_left
                (fun a op => let (sv, hd) := extract_targets op in
                             (sv ++ fst a, hd ++ snd a)) ops acc)).
Proof.
  induction ops as [|op rest IH]; intros acc h Hin.
  - exact Hin.
  - simpl. apply IH. destruct (extract_targets op) as [sv hd]. simpl.
    apply in_or_app. right. exact Hin.
Qed.

Lemma fold_eat_snd_intro :
  forall ops acc op h,
    In op ops -> In h (snd (extract_targets op)) ->
    In h (snd (List.fold_left
                (fun a o => let (sv, hd) := extract_targets o in
                            (sv ++ fst a, hd ++ snd a)) ops acc)).
Proof.
  induction ops as [|op0 rest IH]; intros acc op h Hin Hh.
  - inversion Hin.
  - cbn [fold_left]. destruct Hin as [Heq|Hin].
    + subst op0.
      apply fold_eat_snd_mono.
      rewrite (surjective_pairing (extract_targets op)). cbn [fst snd].
      apply in_or_app. left. exact Hh.
    + eapply IH; eassumption.
Qed.

Lemma in_snd_extract_all_targets_intro :
  forall ops op h,
    In op ops -> In h (snd (extract_targets op)) ->
    In h (snd (extract_all_targets ops)).
Proof.
  intros ops op h. apply fold_eat_snd_intro.
Qed.

(* A header written by some rule of [t] is in [t_write_hdrs t]. *)
Lemma in_t_write_hdrs :
  forall t r op h,
    In r t -> In op (rule_ops r) -> In h (snd (extract_targets op)) ->
    In h (t_write_hdrs t).
Proof.
  intros t r op h Hr Hop Hh.
  unfold t_write_hdrs. apply in_flat_map. exists r. split; [exact Hr|].
  eapply in_snd_extract_all_targets_intro; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Full per-module HEADER step: given input agreement and that every       *)
(* write-target header is present in the symbolic input, the concrete and    *)
(* symbolic transformer OUTPUT header maps agree (present headers via the     *)
(* commute lemma; absent headers are written by neither side).               *)
Lemma transformer_step_hdr_agree :
  forall t f IN_c IN_s,
    ts_agree IN_c IN_s f ->
    (forall h : Header, In h (t_write_hdrs t) -> is_varlike_in_ps IN_s h <> None) ->
    hm_agree (t_header_map (eval_transformer_concrete t IN_c))
             (t_header_map (eval_transformer_smt t IN_s)) f.
Proof.
  intros t f IN_c IN_s Hag Hwp h.
  change (lookup_varlike (eval_transformer_concrete t IN_c) h
          = eval_smt_arith (lookup_varlike (eval_transformer_smt t IN_s) h) f).
  destruct (is_varlike_in_ps IN_s h) eqn:Epres.
  - (* present *)
    apply transformer_step_hdr_present; [exact Hag | rewrite Epres; discriminate].
  - (* absent: written by neither side *)
    assert (Hnw : forall r, In r t ->
              forall op, In op (rule_ops r) -> ~ In h (snd (extract_targets op))).
    { intros r Hr op Hop Hin.
      apply (Hwp h (in_t_write_hdrs t r op h Hr Hop Hin)). exact Epres. }
    (* concrete: congruence to eval_sym_state input, then unwritten-preserved *)
    unfold ts_agree in Hag.
    pose proof (eval_transformer_concrete_preserves_eq _ _ t Hag) as [Hh _].
    rewrite (Hh h).
    rewrite (eval_transformer_concrete_absent_hdr t (eval_sym_state IN_s f) h Hnw).
    (* symbolic: absent-preserved *)
    rewrite (eval_transformer_smt_absent_hdr t IN_s h Epres).
    unfold eval_sym_state at 1. rewrite commute_lookup_varlike. reflexivity.
Qed.

(* Input construction: the transformer input is [inject_headers] of the threaded
   header map over the (init) slot state; if the threaded maps agree ([hm_agree])
   and the slots coincide structurally, the inputs are [ts_agree]. *)
Lemma inject_headers_lookup_state :
  forall {T} (hm : PMap.t T) (X : TransformerState T) (s : State),
    lookup_varlike (inject_headers hm X) s = lookup_varlike X s.
Proof. reflexivity. Qed.

Lemma inject_headers_lookup_ctrl :
  forall {T} (hm : PMap.t T) (X : TransformerState T) (c : Ctrl),
    lookup_varlike (inject_headers hm X) c = lookup_varlike X c.
Proof. reflexivity. Qed.

Lemma inject_headers_ts_agree :
  forall (hmc : PMap.t CrVal) (hms : PMap.t SmtArithExpr)
         (ss : SymbolicTransformerState) (f : SmtValuation),
    hm_agree hmc hms f ->
    ts_agree (inject_headers hmc (eval_sym_state ss f))
             (inject_headers hms ss) f.
Proof.
  intros hmc hms ss f Hhm.
  unfold ts_agree, cs_lookup_eq. split; [| split].
  - (* headers: from hm_agree *)
    intro h. unfold eval_sym_state.
    rewrite commute_lookup_varlike.
    change (lookup_varlike_map hmc h = eval_smt_arith (lookup_varlike_map hms h) f).
    apply Hhm.
  - (* states: injected header map is irrelevant to state lookups *)
    intro s. rewrite inject_headers_lookup_state.
    unfold eval_sym_state. rewrite ! commute_lookup_varlike. reflexivity.
  - (* ctrls: likewise *)
    intro c. rewrite inject_headers_lookup_ctrl.
    unfold eval_sym_state. rewrite ! commute_lookup_varlike. reflexivity.
Qed.

(* State-variable analogue (needed to preserve full [ts_agree] across a step). *)
Lemma transformer_step_state_present :
  forall t f IN_c IN_s (sv : State),
    ts_agree IN_c IN_s f ->
    is_varlike_in_ps IN_s sv <> None ->
    lookup_varlike (eval_transformer_concrete t IN_c) sv
      = eval_smt_arith (lookup_varlike (eval_transformer_smt t IN_s) sv) f.
Proof.
  intros t f IN_c IN_s sv Hag Hpres.
  unfold ts_agree in Hag.
  pose proof (eval_transformer_concrete_preserves_eq _ _ t Hag) as [_ [Hs _]].
  specialize (Hs sv).
  rewrite Hs.
  rewrite (commute_sym_vs_conc_transformer_state_var_map t f IN_s sv Hpres).
  unfold eval_sym_state at 1.
  rewrite commute_lookup_varlike.
  reflexivity.
Qed.

(* Ctrl variables are read-only for a transformer, so a ctrl lookup on the
   output equals the f-concretization of the symbolic output ctrl lookup with
   NO presence hypothesis (the whole ctrl map is invariant on both sides). *)
Lemma transformer_step_ctrl :
  forall t f IN_c IN_s (c : Ctrl),
    ts_agree IN_c IN_s f ->
    lookup_varlike (eval_transformer_concrete t IN_c) c
      = eval_smt_arith (lookup_varlike (eval_transformer_smt t IN_s) c) f.
Proof.
  intros t f IN_c IN_s c Hag.
  unfold ts_agree in Hag.
  pose proof (eval_transformer_concrete_preserves_eq _ _ t Hag) as [_ [_ Hc]].
  specialize (Hc c).
  rewrite Hc.
  (* On the concretized-symbolic input, ctrl commutes unconditionally. *)
  assert (Hcm : t_ctrl_map (eval_transformer_concrete t (eval_sym_state IN_s f))
              = t_ctrl_map (eval_sym_state (eval_transformer_smt t IN_s) f)).
  { apply commute_sym_vs_conc_transformer_ctrl_map. }
  rewrite (lookup_varlike_ctrl_t_ctrl_map _ _ c Hcm).
  unfold eval_sym_state at 1.
  rewrite commute_lookup_varlike.
  reflexivity.
Qed.

(* ================================================================== *)
(* State-variable mirror of the header absent/step machinery, so that a  *)
(* transformer output is a FULL [ts_agree] of its symbolic counterpart     *)
(* (headers + states + ctrls), giving a uniform per-slot ledger invariant. *)

Definition t_write_states (t : Transformer) : list State :=
  List.flat_map (fun r => fst (extract_all_targets (rule_ops r))) t.

Lemma fold_eat_fst_mono :
  forall ops acc h,
    In h (fst acc) ->
    In h (fst (List.fold_left
                (fun a op => let (sv, hd) := extract_targets op in
                             (sv ++ fst a, hd ++ snd a)) ops acc)).
Proof.
  induction ops as [|op rest IH]; intros acc h Hin.
  - exact Hin.
  - simpl. apply IH. destruct (extract_targets op) as [sv hd]. simpl.
    apply in_or_app. right. exact Hin.
Qed.

Lemma fold_eat_fst_intro :
  forall ops acc op h,
    In op ops -> In h (fst (extract_targets op)) ->
    In h (fst (List.fold_left
                (fun a o => let (sv, hd) := extract_targets o in
                            (sv ++ fst a, hd ++ snd a)) ops acc)).
Proof.
  induction ops as [|op0 rest IH]; intros acc op h Hin Hh.
  - inversion Hin.
  - cbn [fold_left]. destruct Hin as [Heq|Hin].
    + subst op0.
      apply fold_eat_fst_mono.
      rewrite (surjective_pairing (extract_targets op)). cbn [fst snd].
      apply in_or_app. left. exact Hh.
    + eapply IH; eassumption.
Qed.

Lemma in_fst_extract_all_targets_intro :
  forall ops op h,
    In op ops -> In h (fst (extract_targets op)) ->
    In h (fst (extract_all_targets ops)).
Proof. intros ops op h. apply fold_eat_fst_intro. Qed.

Lemma in_t_write_states :
  forall t r op sv,
    In r t -> In op (rule_ops r) -> In sv (fst (extract_targets op)) ->
    In sv (t_write_states t).
Proof.
  intros t r op sv Hr Hop Hh.
  unfold t_write_states. apply in_flat_map. exists r. split; [exact Hr|].
  eapply in_fst_extract_all_targets_intro; eauto.
Qed.

Lemma eval_hdr_op_assign_concrete_absent_state :
  forall op c (sv : State),
    ~ In sv (fst (extract_targets op)) ->
    lookup_varlike (eval_hdr_op_assign_concrete op c) sv = lookup_varlike c sv.
Proof.
  intros op c sv Hni.
  destruct op as [f ty a1 a2 tgt | f ty a1 a2 tgt | from to a tgt | from to a tgt];
    unfold eval_hdr_op_assign_concrete.
  - rewrite lookup_update_state_state.
    destruct sv as [sid], tgt as [tid].
    destruct (Coqlib.peq sid tid) as [He|Hne]; [| reflexivity].
    exfalso. apply Hni. cbn. left. congruence.
  - reflexivity.
  - rewrite lookup_update_state_state.
    destruct sv as [sid], tgt as [tid].
    destruct (Coqlib.peq sid tid) as [He|Hne]; [| reflexivity].
    exfalso. apply Hni. cbn. left. congruence.
  - reflexivity.
Qed.

Lemma eval_hdr_op_list_concrete_absent_state :
  forall hol c (sv : State),
    (forall op, In op hol -> ~ In sv (fst (extract_targets op))) ->
    lookup_varlike (eval_hdr_op_list_concrete hol c) sv = lookup_varlike c sv.
Proof.
  induction hol as [|op rest IH]; intros c sv Hall.
  - reflexivity.
  - simpl.
    rewrite IH by (intros op' Hin'; apply Hall; right; exact Hin').
    apply eval_hdr_op_assign_concrete_absent_state. apply Hall. left. reflexivity.
Qed.

Lemma eval_match_action_rule_concrete_absent_state :
  forall r c (sv : State),
    (forall op, In op (rule_ops r) -> ~ In sv (fst (extract_targets op))) ->
    lookup_varlike (eval_match_action_rule_concrete r c) sv = lookup_varlike c sv.
Proof.
  intros [ [mp action] | [mp action] ] c sv Hops; simpl;
    destruct (eval_match_concrete mp c);
    solve [ apply eval_hdr_op_list_concrete_absent_state; exact Hops | reflexivity ].
Qed.

Lemma eval_transformer_concrete_absent_state :
  forall t c (sv : State),
    (forall r, In r t ->
       forall op, In op (rule_ops r) -> ~ In sv (fst (extract_targets op))) ->
    lookup_varlike (eval_transformer_concrete t c) sv = lookup_varlike c sv.
Proof.
  intros t c sv Ht. unfold eval_transformer_concrete.
  destruct (find_first_match (combine (get_match_results t c) t)) as [r|] eqn:Hf.
  - apply eval_match_action_rule_concrete_absent_state.
    intros op Hop. apply (Ht r).
    + eapply find_first_match_in. exact Hf.
    + exact Hop.
  - reflexivity.
Qed.

Lemma update_all_varlike_state_absent :
  forall {T} (ps : TransformerState T) (fs : State -> T) (sv : State),
    is_varlike_in_ps ps sv = None ->
    lookup_varlike (@update_all_varlike State _ T ps fs) sv = lookup_varlike ps sv.
Proof.
  intros T ps fs [sid] Habs.
  unfold is_varlike_in_ps in Habs.
  cbn [map_from_ps CrVarLike_State get_key] in Habs.
  unfold lookup_varlike, lookup_varlike_map.
  cbn [update_all_varlike CrVarLike_State map_from_ps get_key].
  apply new_pmap_from_old_absent. exact Habs.
Qed.

Lemma update_all_varlike_hdr_state :
  forall {T} (ps : TransformerState T) (fh : Header -> T) (sv : State),
    lookup_varlike (@update_all_varlike Header _ T ps fh) sv = lookup_varlike ps sv.
Proof.
  intros T ps fh [sid].
  unfold lookup_varlike, lookup_varlike_map.
  cbn [update_all_varlike CrVarLike_Header map_from_ps CrVarLike_State t_state_map get_key].
  reflexivity.
Qed.

Lemma eval_transformer_smt_absent_state :
  forall t s (sv : State),
    is_varlike_in_ps s sv = None ->
    lookup_varlike (eval_transformer_smt t s) sv = lookup_varlike s sv.
Proof.
  intros t s sv Habs. unfold eval_transformer_smt.
  rewrite update_all_varlike_state_absent.
  - apply update_all_varlike_hdr_state.
  - rewrite is_v1_in_ps_after_update_all_v2. exact Habs.
Qed.

Lemma transformer_step_state_agree :
  forall t f IN_c IN_s,
    ts_agree IN_c IN_s f ->
    (forall sv : State, In sv (t_write_states t) -> is_varlike_in_ps IN_s sv <> None) ->
    forall sv : State,
      lookup_varlike (eval_transformer_concrete t IN_c) sv
        = eval_smt_arith (lookup_varlike (eval_transformer_smt t IN_s) sv) f.
Proof.
  intros t f IN_c IN_s Hag Hws sv.
  destruct (is_varlike_in_ps IN_s sv) eqn:Epres.
  - apply transformer_step_state_present; [exact Hag | rewrite Epres; discriminate].
  - assert (Hnw : forall r, In r t ->
              forall op, In op (rule_ops r) -> ~ In sv (fst (extract_targets op))).
    { intros r Hr op Hop Hin.
      apply (Hws sv (in_t_write_states t r op sv Hr Hop Hin)). exact Epres. }
    unfold ts_agree in Hag.
    pose proof (eval_transformer_concrete_preserves_eq _ _ t Hag) as [_ [Hs _]].
    rewrite (Hs sv).
    rewrite (eval_transformer_concrete_absent_state t (eval_sym_state IN_s f) sv Hnw).
    rewrite (eval_transformer_smt_absent_state t IN_s sv Epres).
    unfold eval_sym_state at 1. rewrite commute_lookup_varlike. reflexivity.
Qed.

(* The full per-module step: a transformer output is a full [ts_agree] of its
   symbolic counterpart, provided every write-target (header and state) is
   present in the symbolic input. *)
Lemma transformer_step_agree :
  forall t f IN_c IN_s,
    ts_agree IN_c IN_s f ->
    (forall h : Header, In h (t_write_hdrs t) -> is_varlike_in_ps IN_s h <> None) ->
    (forall sv : State, In sv (t_write_states t) -> is_varlike_in_ps IN_s sv <> None) ->
    ts_agree (eval_transformer_concrete t IN_c) (eval_transformer_smt t IN_s) f.
Proof.
  intros t f IN_c IN_s Hag Hwh Hws.
  unfold ts_agree, cs_lookup_eq. split; [| split].
  - intro h.
    change (lookup_varlike_map (t_header_map (eval_transformer_concrete t IN_c)) h
            = lookup_varlike (eval_sym_state (eval_transformer_smt t IN_s) f) h).
    rewrite (transformer_step_hdr_agree t f IN_c IN_s Hag Hwh h).
    unfold eval_sym_state at 1. rewrite commute_lookup_varlike. reflexivity.
  - intro sv.
    rewrite (transformer_step_state_agree t f IN_c IN_s Hag Hws sv).
    unfold eval_sym_state at 1. rewrite commute_lookup_varlike. reflexivity.
  - intro c.
    rewrite (transformer_step_ctrl t f IN_c IN_s c Hag).
    unfold eval_sym_state at 1. rewrite commute_lookup_varlike. reflexivity.
Qed.

(* ================================================================== *)
(* Network-level lockstep fold: run concrete and symbolic network        *)
(* semantics side by side, threading a uniform per-slot ledger agreement. *)

From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrSymbolicSemanticsModule.

(* eval_transformer_smt preserves variable presence (its maps rewrite
   existing keys only), so slot/header domains are invariant along a run. *)
Lemma new_pmap_from_old_present :
  forall {T} (m : PMap.t T) (g : positive -> T) i,
    (snd m) ! i <> None -> (snd (new_pmap_from_old m g)) ! i <> None.
Proof.
  intros T m g i H. cbn [snd new_pmap_from_old].
  rewrite PTree.gmap. destruct ((snd m) ! i) eqn:E.
  - cbn. discriminate.
  - exfalso. apply H. reflexivity.
Qed.

Lemma is_varlike_update_all_hdr_present :
  forall {T} (s : TransformerState T) (fh : Header -> T) (h : Header),
    is_varlike_in_ps s h <> None ->
    is_varlike_in_ps (@update_all_varlike Header _ T s fh) h <> None.
Proof.
  intros T s fh [hid] H. unfold is_varlike_in_ps in *.
  cbn [update_all_varlike CrVarLike_Header map_from_ps get_key] in *.
  apply new_pmap_from_old_present. exact H.
Qed.

Lemma is_varlike_update_all_state_present :
  forall {T} (s : TransformerState T) (fs : State -> T) (sv : State),
    is_varlike_in_ps s sv <> None ->
    is_varlike_in_ps (@update_all_varlike State _ T s fs) sv <> None.
Proof.
  intros T s fs [sid] H. unfold is_varlike_in_ps in *.
  cbn [update_all_varlike CrVarLike_State map_from_ps get_key] in *.
  apply new_pmap_from_old_present. exact H.
Qed.

Lemma is_varlike_hdr_eval_transformer_smt :
  forall t s (h : Header),
    is_varlike_in_ps s h <> None ->
    is_varlike_in_ps (eval_transformer_smt t s) h <> None.
Proof.
  intros t s h H. unfold eval_transformer_smt.
  rewrite is_v1_in_ps_after_update_all_v2.
  apply is_varlike_update_all_hdr_present. exact H.
Qed.

Lemma is_varlike_state_eval_transformer_smt :
  forall t s (sv : State),
    is_varlike_in_ps s sv <> None ->
    is_varlike_in_ps (eval_transformer_smt t s) sv <> None.
Proof.
  intros t s sv H. unfold eval_transformer_smt.
  apply is_varlike_update_all_state_present.
  rewrite is_v1_in_ps_after_update_all_v2. exact H.
Qed.

(* Generalized input construction: [inject_headers] of agreeing header maps
   over agreeing slot states yields agreeing inputs. *)
Lemma inject_headers_ts_agree_gen :
  forall (hmc : PMap.t CrVal) (hms : PMap.t SmtArithExpr) cs ss f,
    ts_agree cs ss f -> hm_agree hmc hms f ->
    ts_agree (inject_headers hmc cs) (inject_headers hms ss) f.
Proof.
  intros hmc hms cs ss f Hts Hhm.
  unfold ts_agree, cs_lookup_eq in *. destruct Hts as [Hh [Hs Hc]].
  split; [| split].
  - intro h. unfold eval_sym_state. rewrite commute_lookup_varlike.
    change (lookup_varlike_map hmc h = eval_smt_arith (lookup_varlike_map hms h) f).
    apply Hhm.
  - intro s. rewrite inject_headers_lookup_state.
    specialize (Hs s). rewrite Hs.
    unfold eval_sym_state. rewrite ! commute_lookup_varlike. reflexivity.
  - intro c. rewrite inject_headers_lookup_ctrl.
    specialize (Hc c). rewrite Hc.
    unfold eval_sym_state. rewrite ! commute_lookup_varlike. reflexivity.
Qed.

Definition is_present_hdr {T} (hm : PMap.t T) (h : Header) : Prop :=
  (snd hm) ! (get_key h) <> None.

Definition slot_agree (mc : ModuleState CrVal bool)
                      (ms : ModuleState SmtArithExpr SmtBoolExpr)
                      (f : SmtValuation) : Prop :=
  match mc, ms with
  | TransformerMod cs, TransformerMod ss => ts_agree cs ss f
  | _, _ => False
  end.

Definition ledger_agree (gc : GeneralConcreteState) (gs : GeneralSymbolicState)
                        (f : SmtValuation) : Prop :=
  forall n, match (mod_states gc) ?? n, (mod_states gs) ?? n with
            | None, None => True
            | Some mc, Some ms => slot_agree mc ms f
            | _, _ => False
            end.

Definition get_transformer_m (m : CrModule) : Transformer :=
  match m with TransformerModule _ _ _ t => t | _ => [] end.

Definition all_transformers (net : ModuleNetwork) : Prop :=
  forall name m, lookup_module net name = Some m ->
    exists nm s c t, m = TransformerModule nm s c t.

Definition hdr_writes_present {T} (net : ModuleNetwork) (hm : PMap.t T) : Prop :=
  forall h, In h (collect_write_headers (net_modules net)) -> is_present_hdr hm h.

Definition state_writes_present (net : ModuleNetwork) (gs : GeneralSymbolicState) : Prop :=
  forall name m ss,
    lookup_module net name = Some m ->
    (mod_states gs) ?? (unwrap name) = Some (TransformerMod ss) ->
    forall sv, In sv (t_write_states (get_transformer_m m)) -> is_varlike_in_ps ss sv <> None.

(* [PMap.set] via the [??] (= snd . PTree.get) accessor. *)
Lemma pmap_set_qq :
  forall {T} (m : PMap.t T) k v n,
    (PMap.set k v m) ?? n = if Coqlib.peq n k then Some v else m ?? n.
Proof.
  intros T m k v n. unfold PMap.set. cbn [snd]. apply PTree.gsspec.
Qed.

(* A [None] accumulator is absorbing for the network fold. *)
Lemma fold_left_none_c :
  forall net f_hdrs_c f_pkt_c fuel' rest,
    List.fold_left
      (fun acc dst => match acc with
                      | None => None
                      | Some g => eval_network_from_concrete net dst f_hdrs_c f_pkt_c g fuel'
                      end) rest None = None.
Proof. intros. induction rest; simpl; auto. Qed.

Lemma fold_left_none_s :
  forall net f_hdrs_s f_pkt_s fuel' rest,
    List.fold_left
      (fun acc dst => match acc with
                      | None => None
                      | Some g => eval_network_from_symbolic net dst f_hdrs_s f_pkt_s g fuel'
                      end) rest None = None.
Proof. intros. induction rest; simpl; auto. Qed.

(* Lockstep over the downstream list: given a per-element step relation
   (the fuel' induction hypothesis), the two folds stay in lockstep. *)
Lemma fold_lockstep :
  forall net f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s fuel' f,
    (forall start gc gs,
       ledger_agree gc gs f -> state_writes_present net gs ->
       match eval_network_from_concrete net start f_hdrs_c f_pkt_c gc fuel',
             eval_network_from_symbolic net start f_hdrs_s f_pkt_s gs fuel' with
       | None, None => True
       | Some gc', Some gs' => ledger_agree gc' gs' f /\ state_writes_present net gs'
       | _, _ => False end) ->
    forall dsts gc gs,
      ledger_agree gc gs f -> state_writes_present net gs ->
      match List.fold_left
              (fun acc dst => match acc with None => None
                              | Some g => eval_network_from_concrete net dst f_hdrs_c f_pkt_c g fuel' end)
              dsts (Some gc),
            List.fold_left
              (fun acc dst => match acc with None => None
                              | Some g => eval_network_from_symbolic net dst f_hdrs_s f_pkt_s g fuel' end)
              dsts (Some gs) with
      | None, None => True
      | Some gc', Some gs' => ledger_agree gc' gs' f /\ state_writes_present net gs'
      | _, _ => False end.
Proof.
  intros net f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s fuel' f Hstep.
  induction dsts as [|dst rest IH]; intros gc gs Hled Hsw.
  - simpl. split; assumption.
  - simpl. specialize (Hstep dst gc gs Hled Hsw).
    destruct (eval_network_from_concrete net dst f_hdrs_c f_pkt_c gc fuel') as [gc1|] eqn:Ec;
    destruct (eval_network_from_symbolic net dst f_hdrs_s f_pkt_s gs fuel') as [gs1|] eqn:Es;
    try contradiction.
    + destruct Hstep as [Hled1 Hsw1]. apply IH; assumption.
    + rewrite fold_left_none_c, fold_left_none_s. exact I.
Qed.

Lemma lookup_module_in :
  forall net name m, lookup_module net name = Some m -> In m (net_modules net).
Proof.
  intros net name m H. unfold lookup_module in H.
  apply find_some in H. destruct H as [Hin _]. exact Hin.
Qed.

Lemma collect_write_headers_transformer :
  forall nm sts ctls t mods,
    In (TransformerModule nm sts ctls t) mods ->
    forall h, In h (t_write_hdrs t) -> In h (collect_write_headers mods).
Proof.
  intros nm sts ctls t mods Hin h Hh.
  unfold collect_write_headers. apply in_flat_map.
  exists (TransformerModule nm sts ctls t). split; [exact Hin|].
  unfold t_write_hdrs in Hh. apply in_flat_map in Hh. destruct Hh as [r [Hr Hhr]].
  apply in_flat_map. exists r. split; [exact Hr|].
  destruct r as [[mp ops]|[mp ops]]; cbn [rule_ops] in Hhr; exact Hhr.
Qed.

Lemma is_varlike_inject_hdr_present :
  forall {T} (hm : PMap.t T) (ss : TransformerState T) (h : Header),
    (snd hm) ! (get_key h) <> None ->
    is_varlike_in_ps (inject_headers hm ss) h <> None.
Proof.
  intros T hm ss h H. unfold is_varlike_in_ps.
  cbn [map_from_ps CrVarLike_Header inject_headers t_header_map]. exact H.
Qed.

Lemma is_varlike_inject_state_present :
  forall {T} (hm : PMap.t T) (ss : TransformerState T) (sv : State),
    is_varlike_in_ps ss sv <> None ->
    is_varlike_in_ps (inject_headers hm ss) sv <> None.
Proof.
  intros T hm ss sv H. unfold is_varlike_in_ps in *.
  cbn [map_from_ps CrVarLike_State inject_headers t_state_map] in *. exact H.
Qed.

(* The network lockstep keystone: for a transformer-only network, running the
   concrete and symbolic semantics from agreeing ledgers / header maps yields
   agreeing result ledgers (and preserves the write-presence invariants). *)
Lemma network_lockstep :
  forall fuel net start f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s f gc gs,
    all_transformers net ->
    hm_agree f_hdrs_c f_hdrs_s f ->
    hdr_writes_present net f_hdrs_s ->
    ledger_agree gc gs f ->
    state_writes_present net gs ->
    match eval_network_from_concrete net start f_hdrs_c f_pkt_c gc fuel,
          eval_network_from_symbolic net start f_hdrs_s f_pkt_s gs fuel with
    | None, None => True
    | Some gc', Some gs' => ledger_agree gc' gs' f /\ state_writes_present net gs'
    | _, _ => False end.
Proof.
  induction fuel as [|fuel' IH];
    intros net start f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s f gc gs Hall Hhm Hdom Hled Hsw.
  - exact I.
  - cbn [eval_network_from_concrete eval_network_from_symbolic].
    destruct (lookup_module net start) as [m|] eqn:Elk; [| exact I].
    pose proof (Hled (unwrap start)) as Hslot.
    destruct ((mod_states gc) ?? (unwrap start)) as [mc|] eqn:Egc;
    destruct ((mod_states gs) ?? (unwrap start)) as [ms|] eqn:Egs;
      cbn in Hslot; try contradiction; [| exact I].
    destruct (Hall start m Elk) as [nm [sts [ctls [t Hm]]]]. subst m.
    destruct mc as [cs| |]; destruct ms as [ss| |];
      unfold slot_agree in Hslot; try contradiction.
    cbn [set_module_packet set_module_header_map eval_module_concrete
         eval_module_symbolic module_header_map].
    (* The new agreeing slot. *)
    assert (Hin : In (TransformerModule nm sts ctls t) (net_modules net))
      by (eapply lookup_module_in; exact Elk).
    assert (Hnew : ts_agree (eval_transformer_concrete t (inject_headers f_hdrs_c cs))
                            (eval_transformer_smt t (inject_headers f_hdrs_s ss)) f).
    { apply transformer_step_agree.
      - apply inject_headers_ts_agree_gen; assumption.
      - intros h Hwh. apply is_varlike_inject_hdr_present. apply Hdom.
        eapply collect_write_headers_transformer; eassumption.
      - intros sv Hws. apply is_varlike_inject_state_present.
        eapply Hsw; [exact Elk | exact Egs | cbn [get_transformer_m]; exact Hws]. }
    (* Threaded header agreement / write-presence downstream. *)
    assert (Hnewhm : hm_agree (t_header_map (eval_transformer_concrete t (inject_headers f_hdrs_c cs)))
                              (t_header_map (eval_transformer_smt t (inject_headers f_hdrs_s ss))) f)
      by (apply ts_agree_hm; exact Hnew).
    assert (Hnewdom : hdr_writes_present net
                        (t_header_map (eval_transformer_smt t (inject_headers f_hdrs_s ss)))).
    { intros h Hh. unfold is_present_hdr.
      change (is_varlike_in_ps (eval_transformer_smt t (inject_headers f_hdrs_s ss)) h <> None).
      apply is_varlike_hdr_eval_transformer_smt.
      apply is_varlike_inject_hdr_present. apply Hdom. exact Hh. }
    (* Updated ledgers. *)
    set (nc := eval_transformer_concrete t (inject_headers f_hdrs_c cs)) in *.
    set (ns := eval_transformer_smt t (inject_headers f_hdrs_s ss)) in *.
    assert (Hnewled : ledger_agree
              (set_gps_mod_states gc (PMap.set (unwrap start) (TransformerMod nc) (mod_states gc)))
              (set_gps_mod_states gs (PMap.set (unwrap start) (TransformerMod ns) (mod_states gs))) f).
    { intro n. unfold set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
      destruct (Coqlib.peq n (unwrap start)) as [Eq|Ne].
      - cbn [slot_agree]. exact Hnew.
      - exact (Hled n). }
    assert (Hnewsw : state_writes_present net
              (set_gps_mod_states gs (PMap.set (unwrap start) (TransformerMod ns) (mod_states gs)))).
    { intros name m' ss' Hlk' Hslot' sv Hsv.
      unfold set_gps_mod_states in Hslot'. cbn [mod_states] in Hslot'.
      rewrite pmap_set_qq in Hslot'.
      destruct (Coqlib.peq (unwrap name) (unwrap start)) as [Eq|Ne].
      - inversion Hslot' as [Hss]. apply unwrap_inj in Eq. subst name.
        rewrite Elk in Hlk'. inversion Hlk'. subst m'. subst ss'.
        cbn [get_transformer_m] in Hsv.
        apply is_varlike_state_eval_transformer_smt.
        apply is_varlike_inject_state_present.
        eapply Hsw; [exact Elk | exact Egs | cbn [get_transformer_m]; exact Hsv].
      - eapply Hsw; [exact Hlk' | exact Hslot' | exact Hsv]. }
    (* Apply the fold lockstep with the fuel' induction hypothesis. *)
    apply (fold_lockstep net _ _ f_pkt_c f_pkt_s fuel' f
             (fun start' gc' gs' Hl Hs =>
                IH net start' _ _ f_pkt_c f_pkt_s f gc' gs' Hall Hnewhm Hnewdom Hl Hs));
      assumption.
Qed.

(* ------------------------------------------------------------------ *)
(* Lifting the lockstep to whole general programs, from the concretized  *)
(* initial ledger. *)

Lemma concretize_slot :
  forall gs f n,
    (mod_states (concretize_sym_modnet_state gs f)) ?? n
      = option_map (fun ms => concretize_sym_module_state ms f) ((mod_states gs) ?? n).
Proof.
  intros gs f n. unfold concretize_sym_modnet_state. cbn [mod_states].
  unfold PMap.map. cbn [snd]. apply PTree.gmap1.
Qed.

Lemma module_header_map_concretize :
  forall ms f,
    module_header_map (concretize_sym_module_state ms f)
      = PMap.map (fun e => eval_smt_arith e f) (module_header_map ms).
Proof. intros [ts|ps|ps] f; reflexivity. Qed.

Lemma hm_agree_concretize :
  forall hm f, hm_agree (PMap.map (fun e => eval_smt_arith e f) hm) hm f.
Proof.
  intros hm f h. unfold lookup_varlike_map. rewrite PMap.gmap. reflexivity.
Qed.

Lemma ledger_agree_concretize :
  forall gs f,
    (forall n ms, (mod_states gs) ?? n = Some ms -> exists ts, ms = TransformerMod ts) ->
    ledger_agree (concretize_sym_modnet_state gs f) gs f.
Proof.
  intros gs f Hall n. rewrite concretize_slot.
  destruct ((mod_states gs) ?? n) as [ms|] eqn:E; cbn [option_map]; [| exact I].
  destruct (Hall n ms E) as [ts ->].
  cbn [concretize_sym_module_state slot_agree].
  unfold ts_agree, cs_lookup_eq. split; [| split]; intros; reflexivity.
Qed.

Lemma eval_general_program_lockstep :
  forall p gs f,
    all_transformers (get_network_from_general p) ->
    (forall ss, (mod_states gs) ?? (unwrap (start_module (get_network_from_general p))) = Some ss ->
        hdr_writes_present (get_network_from_general p) (module_header_map ss)) ->
    state_writes_present (get_network_from_general p) gs ->
    ledger_agree (concretize_sym_modnet_state gs f) gs f ->
    match eval_general_program_concrete p (concretize_sym_modnet_state gs f),
          eval_general_program_symbolic p gs with
    | None, None => True
    | Some a, Some b => ledger_agree a b f /\ state_writes_present (get_network_from_general p) b
    | _, _ => False end.
Proof.
  intros p gs f Hall Hdom Hsw Hled.
  unfold eval_general_program_concrete, eval_general_program_symbolic.
  rewrite concretize_slot.
  destruct ((mod_states gs) ?? (unwrap (start_module (get_network_from_general p)))) as [ss0|] eqn:Es0;
    cbn [option_map]; [| exact I].
  rewrite module_header_map_concretize.
  apply network_lockstep; try assumption.
  - apply hm_agree_concretize.
  - apply (Hdom ss0 eq_refl).
Qed.

(* ------------------------------------------------------------------ *)
(* Sink extraction: agreeing ledgers have pointwise-agreeing sink lists. *)

Lemma get_sink_states_agree :
  forall net gc gs f,
    ledger_agree gc gs f ->
    Forall2 (fun mc ms => slot_agree mc ms f)
            (get_sink_states net (mod_states gc))
            (get_sink_states net (mod_states gs)).
Proof.
  intros net gc gs f Hled. unfold get_sink_states.
  induction (sink_modules net) as [|m rest IH]; [constructor|].
  cbn [fold_right]. pose proof (Hled (unwrap (get_mod_name m))) as Hm.
  destruct ((mod_states gc) ?? (unwrap (get_mod_name m))) as [mc|] eqn:Ec;
  destruct ((mod_states gs) ?? (unwrap (get_mod_name m))) as [ms|] eqn:Es;
  cbn in Hm; try contradiction.
  - constructor; assumption.
  - exact IH.
Qed.

(* Transformer-only well-formedness bundle, parametric in the initial symbolic
   state [gs]: every module is a transformer, every initial slot is a transformer
   slot, the start header map contains all write headers, and every slot's state
   map contains that module's write-target state variables.  (well_formed_module
   does NOT constrain write targets, so the last two are stated explicitly;
   header writes are in fact covered by [init_general_symbolic_state]'s
   [collect_write_headers] seeding.)  Every conjunct depends on [gs] only through
   [mod_states gs], so it is invariant under [set_gps_shared_bits] (the input
   packet threaded in for a source parser). *)
Definition transformer_ok_gs (net : ModuleNetwork) (gs : GeneralSymbolicState) : Prop :=
  all_transformers net /\
  (forall n ms, (mod_states gs) ?? n = Some ms -> exists ts, ms = TransformerMod ts) /\
  (forall ss, (mod_states gs) ?? (unwrap (start_module net)) = Some ss ->
      hdr_writes_present net (module_header_map ss)) /\
  state_writes_present net gs.

Definition transformer_ok (pre : String.string) (p : GeneralCaracaraProgram) : Prop :=
  transformer_ok_gs (get_network_from_general p) (init_general_symbolic_state pre p).

(* The single-sink header agreement used by the checker soundness/completeness,
   parametric in the initial symbolic state [gs]: if the symbolic run's sinks are
   a single transformer [sym], the concrete run from the concretized initial
   ledger yields a single transformer sink [cs] whose state agrees with [sym]
   under [f]. *)
Lemma header_sink_agree_gs :
  forall p gs f sym,
    transformer_ok_gs (get_network_from_general p) gs ->
    eval_general_program_symbolic_sinks p gs
      = Some [TransformerMod sym] ->
    forall l,
    eval_general_program_concrete_sinks p
      (concretize_sym_modnet_state gs f) = Some l ->
    exists cs, l = [TransformerMod cs] /\ ts_agree cs sym f.
Proof.
  intros p gs f sym Hok Hsym l Hconc.
  destruct Hok as [Hall [Hslots [Hdom Hsw]]].
  unfold eval_general_program_symbolic_sinks in Hsym.
  unfold eval_general_program_concrete_sinks in Hconc.
  destruct (eval_general_program_symbolic p gs)
    as [ls|] eqn:Es; [| discriminate].
  destruct (eval_general_program_concrete p
              (concretize_sym_modnet_state gs f))
    as [lc|] eqn:Ec; [| discriminate].
  (* lockstep: ledger_agree lc ls *)
  pose proof (eval_general_program_lockstep p gs f
                Hall Hdom Hsw
                (ledger_agree_concretize _ f Hslots)) as Hstep.
  rewrite Ec, Es in Hstep. destruct Hstep as [Hled _].
  (* sinks agree pointwise *)
  pose proof (get_sink_states_agree (get_network_from_general p) lc ls f Hled) as HF.
  injection Hsym as Hsym'. injection Hconc as Hconc'.
  rewrite Hconc' in HF. rewrite Hsym' in HF.
  inversion HF as [| mc ms lc' ls' Hslot HF' Elc Els]; subst.
  inversion HF'; subst.
  unfold slot_agree in Hslot.
  destruct mc as [cs| |]; try contradiction.
  exists cs. split; [reflexivity | exact Hslot].
Qed.

Corollary header_sink_agree :
  forall pre p f sym,
    transformer_ok pre p ->
    eval_general_program_symbolic_sinks p (init_general_symbolic_state pre p)
      = Some [TransformerMod sym] ->
    forall l,
    eval_general_program_concrete_sinks p
      (concretize_sym_modnet_state (init_general_symbolic_state pre p) f) = Some l ->
    exists cs, l = [TransformerMod cs] /\ ts_agree cs sym f.
Proof. intros pre p. apply header_sink_agree_gs. Qed.

(* [set_gps_shared_bits] (hence [init_general_symbolic_state_n]) leaves the module
   ledger untouched, so the transformer-only bundle transfers to the packet-seeded
   initial state used by the header checker with a genuine input packet. *)
Lemma transformer_ok_n :
  forall pre p n,
    transformer_ok pre p ->
    transformer_ok_gs (get_network_from_general p) (init_general_symbolic_state_n pre p n).
Proof.
  intros pre p n Hok. unfold init_general_symbolic_state_n, set_gps_shared_bits.
  exact Hok.
Qed.
