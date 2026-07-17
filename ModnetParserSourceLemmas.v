(* ================================================================== *)
(* Gap A, Phase 2: header-network soundness for a SOURCE PARSER feeding  *)
(* a transformer chain ([Parser] -> Transformer* -> transformer sink).   *)
(*                                                                       *)
(* Builds on the transformer-only development (ModnetHeaderLemmas.v).     *)
(* The source parser runs on the real input packet threaded in by the     *)
(* packet-seeded checker (init_general_symbolic_state_n); at the source    *)
(* the concrete parser input is exactly the f-concretization of the        *)
(* symbolic one, so eval_parser_commute (ParserCommuteLemmas.v) applies     *)
(* directly.  We generalize the per-slot ledger agreement to carry parser   *)
(* slots (header-map agreement), then run the downstream transformer chain  *)
(* with the existing lockstep.                                             *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrVarLike.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrParser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import ParserCommuteLemmas.
From MyProject Require Import ModnetHeaderLemmas.
From MyProject Require Import ConcreteTransformerLemmas.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import Maps.

(* ------------------------------------------------------------------ *)
(* Parser-aware per-slot agreement.  A transformer slot agrees via the    *)
(* existing [ts_agree]; a parser or deparser slot agrees when its header   *)
(* map is the f-concretization of the symbolic one at every lookup.        *)

Definition slot_agree_g (mc : ModuleState CrVal bool)
                        (ms : ModuleState SmtArithExpr SmtBoolExpr)
                        (f : SmtValuation) : Prop :=
  match mc, ms with
  | TransformerMod cs, TransformerMod ss => ts_agree cs ss f
  | ParserMod cps, ParserMod sps => hm_agree (p_header_map cps) (p_header_map sps) f
  | DeparserMod cps, DeparserMod sps => hm_agree (p_header_map cps) (p_header_map sps) f
  | _, _ => False
  end.

Definition ledger_agree_g (gc : GeneralConcreteState) (gs : GeneralSymbolicState)
                          (f : SmtValuation) : Prop :=
  forall n, match (mod_states gc) ?? n, (mod_states gs) ?? n with
            | None, None => True
            | Some mc, Some ms => slot_agree_g mc ms f
            | _, _ => False
            end.

(* A transformer-only ledger agreement is a fortiori a generalized one. *)
Lemma ledger_agree_to_g :
  forall gc gs f, ledger_agree gc gs f -> ledger_agree_g gc gs f.
Proof.
  intros gc gs f H n. specialize (H n).
  destruct ((mod_states gc) ?? n) as [mc|]; destruct ((mod_states gs) ?? n) as [ms|];
    try exact H.
  destruct mc as [cs| |]; destruct ms as [ss| |]; cbn [slot_agree slot_agree_g] in *;
    (exact H || contradiction).
Qed.

(* Concretizing the symbolic ledger yields a generalized-agreeing pair, with no
   transformer-only restriction: every slot (transformer/parser/deparser) agrees
   with its own f-concretization. *)
Lemma ledger_agree_g_concretize :
  forall gs f, ledger_agree_g (concretize_sym_modnet_state gs f) gs f.
Proof.
  intros gs f n. rewrite concretize_slot.
  destruct ((mod_states gs) ?? n) as [ms|] eqn:E; cbn [option_map]; [| exact I].
  destruct ms as [ts|ps|ps]; cbn [concretize_sym_module_state slot_agree_g].
  - unfold ts_agree, cs_lookup_eq. split; [| split]; intros; reflexivity.
  - apply hm_agree_concretize.
  - apply hm_agree_concretize.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 2: the source parser's output header map agrees (at every       *)
(* lookup) with the f-concretization of the symbolic one.               *)

(* A single extraction preserves the header map's default ([fst]). *)
Lemma apply_extract_fst : forall eo s s',
  apply_extract_symbolic eo s = Some s' -> fst (p_header_map s') = fst (p_header_map s).
Proof.
  intros [h w] s s'. unfold apply_extract_symbolic.
  destruct (Nat.leb (p_cursor s + w) (length (p_packet s))); [| discriminate].
  intro E. injection E as <-. reflexivity.
Qed.

(* A parser run preserves the header map's default ([fst]): every symbolic
   header op ([PMap.set] on extraction, [merge_header_maps] on a select) keeps
   [fst], so the merged result's default is the input's default. *)
Lemma run_parser_fst : forall fuel p lbl s,
  fst (spr_headers (run_parser_symbolic p lbl s fuel)) = fst (p_header_map s).
Proof.
  induction fuel as [| fuel' IH]; intros p lbl s.
  - reflexivity.
  - simpl. destruct (lookup_state p lbl) as [d|]; [| reflexivity ].
    (* the [run_tgt] continuation, at any post-extraction state [ps'], keeps
       [fst] = fst ps'; a [select] merge keeps the first branch's [fst]. *)
    assert (Hrt : forall ps' tgt,
      fst (spr_headers match tgt with
        | TargetState next => run_parser_symbolic p next ps' fuel'
        | Accept => mkSymParserResult SmtTrue (p_header_map ps')
        | Reject => mkSymParserResult SmtFalse (p_header_map ps')
        end) = fst (p_header_map ps')).
    { intros ps' tgt. destruct tgt as [next| |]; [ apply IH | reflexivity | reflexivity ]. }
    assert (Hresolve : forall ps' cases default,
      fst (spr_headers (resolve_select_symbolic
        (fun tgt => match tgt with
          | TargetState next => run_parser_symbolic p next ps' fuel'
          | Accept => mkSymParserResult SmtTrue (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end)
        ps' cases default)) = fst (p_header_map ps')).
    { intros ps' cases. induction cases as [|c rest IHc]; intro default.
      - cbn [resolve_select_symbolic]. apply Hrt.
      - cbn [resolve_select_symbolic]. unfold merge_results, merge_header_maps.
        cbn [spr_headers fst]. apply Hrt. }
    destruct (psd_extract d) as [eo|] eqn:Hex.
    + destruct (apply_extract_symbolic eo s) as [ps'|] eqn:He.
      * assert (Hf : fst (p_header_map ps') = fst (p_header_map s))
          by exact (apply_extract_fst eo s ps' He).
        cbn [spr_headers]. destruct (psd_trans d) as [tgt | cases default].
        -- rewrite Hrt. exact Hf.
        -- rewrite Hresolve. exact Hf.
      * reflexivity.
    + destruct (psd_trans d) as [tgt | cases default].
      * rewrite Hrt. reflexivity.
      * rewrite Hresolve. reflexivity.
Qed.

(* Every extract target of a parser lies in a reference header-map domain. *)
Definition extract_targets_in_dom (p : Parser) (m : PMap.t SmtArithExpr) : Prop :=
  forall lbl d h w,
    lookup_state p lbl = Some d ->
    psd_extract d = Some (ExtractOpConstructor h w) ->
    in_dom m (get_key h).

(* A [PMap.set] adds only its own key. *)
Lemma in_dom_set : forall k' v m k, in_dom (PMap.set k' v m) k -> k = k' \/ in_dom m k.
Proof.
  intros k' v m k. unfold in_dom, PMap.set. cbn [snd]. rewrite PTree.gsspec.
  destruct (Coqlib.peq k k'); [ left; assumption | right; assumption ].
Qed.

(* Domain upper bound: under [extract_targets_in_dom p (p_header_map s0)] and
   [dom s ⊆ dom s0], every key in the parser output is in [dom s0].  Combined
   with [run_dom_mono] this pins the output domain to the input domain, so the
   two [select] branches never diverge in domain. *)
Lemma run_dom_ub : forall fuel p (s0 : SymbolicParserState) lbl s k,
  extract_targets_in_dom p (p_header_map s0) ->
  (forall j, in_dom (p_header_map s) j -> in_dom (p_header_map s0) j) ->
  in_dom (spr_headers (run_parser_symbolic p lbl s fuel)) k ->
  in_dom (p_header_map s0) k.
Proof.
  induction fuel as [| fuel' IH]; intros p s0 lbl s k Hext Hsub Hk.
  - simpl in Hk. apply Hsub, Hk.
  - simpl in Hk. destruct (lookup_state p lbl) as [d|] eqn:Hlk;
      [| apply Hsub, Hk ].
    (* the [run_tgt] continuation from a post-extraction state [ps'] whose
       domain is within [dom s0] stays within [dom s0]. *)
    assert (Hrt : forall (ps' : SymbolicParserState),
      (forall j, in_dom (p_header_map ps') j -> in_dom (p_header_map s0) j) ->
      forall tgt,
      in_dom (spr_headers match tgt with
        | TargetState next => run_parser_symbolic p next ps' fuel'
        | Accept => mkSymParserResult SmtTrue (p_header_map ps')
        | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) k ->
      in_dom (p_header_map s0) k).
    { intros ps' Hps' tgt Hin. destruct tgt as [next| |].
      - apply (IH p s0 next ps' k Hext Hps' Hin).
      - cbn [spr_headers] in Hin. apply Hps', Hin.
      - cbn [spr_headers] in Hin. apply Hps', Hin. }
    assert (Hres : forall (ps' : SymbolicParserState),
      (forall j, in_dom (p_header_map ps') j -> in_dom (p_header_map s0) j) ->
      forall cases default,
      in_dom (spr_headers (resolve_select_symbolic
        (fun tgt => match tgt with
          | TargetState next => run_parser_symbolic p next ps' fuel'
          | Accept => mkSymParserResult SmtTrue (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) ps' cases default)) k ->
      in_dom (p_header_map s0) k).
    { intros ps' Hps' cases. induction cases as [|c rest IHc]; intros default Hin;
        cbn [resolve_select_symbolic] in Hin.
      - apply (Hrt ps' Hps' default Hin).
      - unfold merge_results in Hin. cbn [spr_headers] in Hin.
        apply merge_in_dom in Hin. apply (Hrt ps' Hps' (sc_target c) Hin). }
    destruct (psd_extract d) as [[h w]|] eqn:Hex.
    + destruct (apply_extract_symbolic (ExtractOpConstructor h w) s) as [ps'|] eqn:Happ;
        [| apply Hsub, Hk ].
      assert (Hps' : forall j, in_dom (p_header_map ps') j -> in_dom (p_header_map s0) j).
      { intros j Hj. unfold apply_extract_symbolic in Happ.
        destruct (Nat.leb (p_cursor s + w) (length (p_packet s))); [| discriminate].
        injection Happ as <-. cbn [p_header_map] in Hj. apply in_dom_set in Hj.
        destruct Hj as [->|Hj]; [ apply (Hext lbl d h w Hlk Hex) | apply Hsub, Hj ]. }
      destruct (psd_trans d) as [tgt | cases default].
      * apply (Hrt ps' Hps' tgt Hk).
      * apply (Hres ps' Hps' cases default Hk).
    + destruct (psd_trans d) as [tgt | cases default].
      * apply (Hrt s Hsub tgt Hk).
      * apply (Hres s Hsub cases default Hk).
Qed.

Transparent lookup_varlike_map.

(* A lookup at a key absent from the map returns the map's default ([fst]). *)
Lemma lookup_varlike_default : forall {T} (m : PMap.t T) (h : Header),
  PTree.get (get_key h) (snd m) = None -> lookup_varlike_map m h = fst m.
Proof.
  intros T m h H. unfold lookup_varlike_map, PMap.get. rewrite H. reflexivity.
Qed.

(* Concrete run preserves the value at any key that is never an extract target. *)
Lemma run_parser_concrete_preserves : forall fuel p lbl cs cps k,
  (forall lbl' d h w, lookup_state p lbl' = Some d ->
     psd_extract d = Some (ExtractOpConstructor h w) -> get_key h <> k) ->
  run_parser_concrete p lbl cs fuel = Some cps ->
  PMap.get k (p_header_map cps) = PMap.get k (p_header_map cs).
Proof.
  induction fuel as [|fuel' IH]; intros p lbl cs cps k Hk Hrun; [ discriminate |].
  simpl in Hrun. destruct (lookup_state p lbl) as [d|] eqn:Hlk; [| discriminate].
  assert (Hpres : forall ps',
      (match psd_extract d with None => Some cs | Some eo => apply_extract_concrete eo cs end) = Some ps' ->
      PMap.get k (p_header_map ps') = PMap.get k (p_header_map cs)).
  { intros ps' He. destruct (psd_extract d) as [[h w]|] eqn:Hex.
    - unfold apply_extract_concrete in He.
      destruct (Nat.leb (p_cursor cs + w) (length (p_packet cs))); [| discriminate].
      injection He as <-. cbn [p_header_map]. apply PMap.gso.
      apply not_eq_sym. exact (Hk lbl d h w Hlk Hex).
    - injection He as <-. reflexivity. }
  destruct (match psd_extract d with None => Some cs | Some eo => apply_extract_concrete eo cs end)
    as [ps'|] eqn:He; [| discriminate].
  specialize (Hpres ps' eq_refl).
  destruct (eval_transition_concrete ps' (psd_trans d)) as [next| |] eqn:Htr; simpl in Hrun.
  - rewrite (IH p next ps' cps k Hk Hrun). exact Hpres.
  - injection Hrun as <-. exact Hpres.
  - discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* The source-parser agreement keystone: when the concrete parser (run on the
   f-concretization of the symbolic input [s]) accepts, its output header map
   agrees at EVERY header with the f-concretization of the symbolic output.
   In-domain headers agree by [run_parser_commute]; out-of-domain headers agree
   because neither run touches them (extractions target in-domain headers, by
   [extract_targets_in_dom]) so both collapse to the (agreeing) map default. *)
Lemma source_parser_hm_agree : forall f p (s : SymbolicParserState) cps,
  extract_targets_in_dom p (p_header_map s) ->
  eval_parser_concrete p (eval_sym_parser_state s f) = Some cps ->
  hm_agree (p_header_map cps) (spr_headers (eval_parser_symbolic p s)) f.
Proof.
  intros f p s cps Hext Hrun h.
  unfold eval_parser_symbolic. unfold eval_parser_concrete in Hrun.
  replace (length (p_packet (eval_sym_parser_state s f))) with (length (p_packet s)) in Hrun
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  set (fuel := length (parser_states p) * S (length (p_packet s))) in *.
  destruct (PTree.get (get_key h) (snd (p_header_map s))) eqn:Hdom.
  - (* in-domain header: run_parser_commute *)
    assert (Hdh : forall h', In h' [h] -> in_dom (p_header_map s) (get_key h')).
    { intros h' [<-|[]]. unfold in_dom. rewrite Hdom. discriminate. }
    pose proof (run_parser_commute f [h] fuel p (parser_start p) s Hdh) as Hc.
    rewrite Hrun in Hc. destruct Hc as [_ Hag].
    apply (Hag h (or_introl eq_refl)).
  - (* out-of-domain header: both sides are the map default *)
    (* the key is never an extract target *)
    assert (Hne : forall lbl' d h' w, lookup_state p lbl' = Some d ->
                  psd_extract d = Some (ExtractOpConstructor h' w) -> get_key h' <> get_key h).
    { intros lbl' d h' w Hlk Hpe Heq. unfold extract_targets_in_dom in Hext.
      pose proof (Hext lbl' d h' w Hlk Hpe) as Ht. unfold in_dom in Ht.
      rewrite Heq, Hdom in Ht. apply Ht. reflexivity. }
    (* concrete side: value preserved from the concretized input, then default *)
    pose proof (run_parser_concrete_preserves fuel p (parser_start p)
                  (eval_sym_parser_state s f) cps (get_key h) Hne Hrun) as Hpres.
    unfold lookup_varlike_map. rewrite Hpres.
    change (PMap.get (get_key h) (p_header_map (eval_sym_parser_state s f)))
      with (lookup_varlike_map (p_header_map (eval_sym_parser_state s f)) h).
    rewrite eval_sym_lookup_header.
    rewrite (lookup_varlike_default (p_header_map s) h Hdom).
    (* symbolic side: out of domain -> default = fst (p_header_map s) *)
    assert (Hsdom : PTree.get (get_key h) (snd (spr_headers (run_parser_symbolic p (parser_start p) s fuel))) = None).
    { destruct (PTree.get (get_key h) (snd (spr_headers (run_parser_symbolic p (parser_start p) s fuel)))) eqn:E;
        [| reflexivity ].
      exfalso.
      assert (Hin : in_dom (spr_headers (run_parser_symbolic p (parser_start p) s fuel)) (get_key h))
        by (unfold in_dom; rewrite E; discriminate).
      pose proof (run_dom_ub fuel p s (parser_start p) s (get_key h) Hext
                    (fun j Hj => Hj) Hin) as Hbad.
      unfold in_dom in Hbad. rewrite Hdom in Hbad. apply Hbad. reflexivity. }
    change (PMap.get (get_key h) (spr_headers (run_parser_symbolic p (parser_start p) s fuel)))
      with (lookup_varlike_map (spr_headers (run_parser_symbolic p (parser_start p) s fuel)) h).
    rewrite (lookup_varlike_default _ h Hsdom).
    rewrite (run_parser_fst fuel p (parser_start p) s). reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 3: the per-module source-parser step. *)

(* When the concrete parser accepts, the symbolic accept condition is true at f. *)
Lemma source_parser_accept : forall f p (s : SymbolicParserState) cps,
  eval_parser_concrete p (eval_sym_parser_state s f) = Some cps ->
  eval_smt_bool (spr_accept (eval_parser_symbolic p s)) f = true.
Proof.
  intros f p s cps Hrun.
  unfold eval_parser_symbolic. unfold eval_parser_concrete in Hrun.
  replace (length (p_packet (eval_sym_parser_state s f))) with (length (p_packet s)) in Hrun
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  set (fuel := length (parser_states p) * S (length (p_packet s))) in *.
  assert (Hdh : forall h, In h (@nil Header) -> in_dom (p_header_map s) (get_key h))
    by (intros h []).
  pose proof (run_parser_commute f [] fuel p (parser_start p) s Hdh) as Hc.
  rewrite Hrun in Hc. destruct Hc as [Hacc _]. exact Hacc.
Qed.

(* The source-parser module step: when the concrete parser module accepts (its
   input being the f-concretization of the symbolic input [s]), the symbolic
   module step returns [Some (ParserMod sps)] and the two parser slots agree. *)
Lemma source_parser_module_step :
  forall f nm p (s : SymbolicParserState) cps,
    extract_targets_in_dom p (p_header_map s) ->
    eval_module_concrete (ParserModule nm p) (ParserMod (eval_sym_parser_state s f))
      = Some (ParserMod cps) ->
    eval_module_symbolic (ParserModule nm p) (ParserMod s)
      = Some (ParserMod {| p_header_map := spr_headers (eval_parser_symbolic p s);
                           p_packet := p_packet s; p_cursor := p_cursor s |}) /\
    hm_agree (p_header_map cps) (spr_headers (eval_parser_symbolic p s)) f.
Proof.
  intros f nm p s cps Hext Hrun.
  cbn [eval_module_concrete] in Hrun.
  destruct (eval_parser_concrete p (eval_sym_parser_state s f)) as [cps0|] eqn:Ec;
    [| discriminate ].
  injection Hrun as <-.
  pose proof (source_parser_accept f p s cps0 Ec) as Hacc.
  pose proof (source_parser_hm_agree f p s cps0 Hext Ec) as Hag.
  cbn [eval_module_symbolic].
  destruct (spr_accept (eval_parser_symbolic p s)) eqn:Ea;
    try (split; [ reflexivity | exact Hag ]);
    simpl in Hacc; discriminate Hacc.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 4: the generalized network lockstep.  Every module EXCEPT the
   source parser [psrc] is a transformer, and [psrc] is never a downstream
   target (in-degree 0), so the downstream recursion from a transformer never
   re-processes the parser.  The invariant is [ledger_agree_g] (the parser
   slot rides along, agreeing on its header map but untouched by transformers). *)

Definition all_transformers_except (net : ModuleNetwork) (psrc : ModuleName) : Prop :=
  forall name m, lookup_module net name = Some m -> name <> psrc ->
    exists nm sts ctls t, m = TransformerModule nm sts ctls t.

Lemma fold_lockstep_g :
  forall net psrc f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s fuel' f,
    (forall start gc gs, start <> psrc ->
       ledger_agree_g gc gs f -> state_writes_present net gs ->
       match eval_network_from_concrete net start f_hdrs_c f_pkt_c gc fuel',
             eval_network_from_symbolic net start f_hdrs_s f_pkt_s gs fuel' with
       | None, _ => True
       | Some gc', Some gs' => ledger_agree_g gc' gs' f /\ state_writes_present net gs'
       | Some _, None => False end) ->
    forall dsts gc gs,
      (forall dst, In dst dsts -> dst <> psrc) ->
      ledger_agree_g gc gs f -> state_writes_present net gs ->
      match List.fold_left
              (fun acc dst => match acc with None => None
                              | Some g => eval_network_from_concrete net dst f_hdrs_c f_pkt_c g fuel' end)
              dsts (Some gc),
            List.fold_left
              (fun acc dst => match acc with None => None
                              | Some g => eval_network_from_symbolic net dst f_hdrs_s f_pkt_s g fuel' end)
              dsts (Some gs) with
      | None, _ => True
      | Some gc', Some gs' => ledger_agree_g gc' gs' f /\ state_writes_present net gs'
      | Some _, None => False end.
Proof.
  intros net psrc f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s fuel' f Hstep.
  induction dsts as [|dst rest IH]; intros gc gs Hnd Hled Hsw.
  - simpl. split; assumption.
  - simpl. specialize (Hstep dst gc gs (Hnd dst (or_introl eq_refl)) Hled Hsw).
    destruct (eval_network_from_concrete net dst f_hdrs_c f_pkt_c gc fuel') as [gc1|] eqn:Ec;
    destruct (eval_network_from_symbolic net dst f_hdrs_s f_pkt_s gs fuel') as [gs1|] eqn:Es.
    + destruct Hstep as [Hled1 Hsw1].
      apply IH; [ intros d Hd; apply Hnd; right; exact Hd | assumption | assumption ].
    + contradiction Hstep.
    + rewrite fold_left_none_c. exact I.
    + rewrite fold_left_none_c. exact I.
Qed.

Lemma network_lockstep_g :
  forall fuel net psrc start f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s f gc gs,
    all_transformers_except net psrc ->
    start <> psrc ->
    (forall x, ~ In psrc (downstream_modules net x)) ->
    hm_agree f_hdrs_c f_hdrs_s f ->
    hdr_writes_present net f_hdrs_s ->
    ledger_agree_g gc gs f ->
    state_writes_present net gs ->
    match eval_network_from_concrete net start f_hdrs_c f_pkt_c gc fuel,
          eval_network_from_symbolic net start f_hdrs_s f_pkt_s gs fuel with
    | None, _ => True
    | Some gc', Some gs' => ledger_agree_g gc' gs' f /\ state_writes_present net gs'
    | Some _, None => False end.
Proof.
  induction fuel as [|fuel' IH];
    intros net psrc start f_hdrs_c f_hdrs_s f_pkt_c f_pkt_s f gc gs Hall Hns Hnd Hhm Hdom Hled Hsw.
  - exact I.
  - cbn [eval_network_from_concrete eval_network_from_symbolic].
    destruct (lookup_module net start) as [m|] eqn:Elk; [| exact I].
    pose proof (Hled (unwrap start)) as Hslot.
    destruct ((mod_states gc) ?? (unwrap start)) as [mc|] eqn:Egc;
    destruct ((mod_states gs) ?? (unwrap start)) as [ms|] eqn:Egs;
      cbn in Hslot; try contradiction; [| exact I].
    destruct (Hall start m Elk Hns) as [nm [sts [ctls [t Hm]]]]. subst m.
    destruct mc as [cs|pc|pc]; destruct ms as [ss|ps|ps];
      cbn [slot_agree_g] in Hslot; try contradiction.
    2:{ cbn [set_module_packet set_module_header_map eval_module_concrete eval_module_symbolic]. exact I. }
    2:{ cbn [set_module_packet set_module_header_map eval_module_concrete eval_module_symbolic]. exact I. }
    cbn [set_module_packet set_module_header_map eval_module_concrete
         eval_module_symbolic module_header_map].
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
    assert (Hnewhm : hm_agree (t_header_map (eval_transformer_concrete t (inject_headers f_hdrs_c cs)))
                              (t_header_map (eval_transformer_smt t (inject_headers f_hdrs_s ss))) f)
      by (apply ts_agree_hm; exact Hnew).
    assert (Hnewdom : hdr_writes_present net
                        (t_header_map (eval_transformer_smt t (inject_headers f_hdrs_s ss)))).
    { intros h Hh. unfold is_present_hdr.
      change (is_varlike_in_ps (eval_transformer_smt t (inject_headers f_hdrs_s ss)) h <> None).
      apply is_varlike_hdr_eval_transformer_smt.
      apply is_varlike_inject_hdr_present. apply Hdom. exact Hh. }
    set (nc := eval_transformer_concrete t (inject_headers f_hdrs_c cs)) in *.
    set (ns := eval_transformer_smt t (inject_headers f_hdrs_s ss)) in *.
    assert (Hnewled : ledger_agree_g
              (set_gps_mod_states gc (PMap.set (unwrap start) (TransformerMod nc) (mod_states gc)))
              (set_gps_mod_states gs (PMap.set (unwrap start) (TransformerMod ns) (mod_states gs))) f).
    { intro n. unfold set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
      destruct (Coqlib.peq n (unwrap start)) as [Eq|Ne].
      - cbn [slot_agree_g]. exact Hnew.
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
    apply (fold_lockstep_g net psrc _ _ f_pkt_c f_pkt_s fuel' f
             (fun start' gc' gs' Hns' Hl Hs =>
                IH net psrc start' _ _ f_pkt_c f_pkt_s f gc' gs' Hall Hns' Hnd Hnewhm Hnewdom Hl Hs));
      [ intros d Hd Heq; subst d; apply (Hnd start); exact Hd | assumption | assumption ].
Qed.

(* ------------------------------------------------------------------ *)
(* Part 5: the whole-program parser-source lockstep. *)

(* The parser output keeps every write header present (the run only grows the
   header domain), so write-presence transfers to the downstream chain. *)
Lemma parser_out_writes_present : forall net p s,
  hdr_writes_present net (p_header_map s) ->
  hdr_writes_present net (spr_headers (eval_parser_symbolic p s)).
Proof.
  intros net p s H h Hh. unfold is_present_hdr, eval_parser_symbolic in *.
  apply (run_dom_mono _ p (parser_start p) s (get_key h)). exact (H h Hh).
Qed.

(* Whole-program lockstep for a source parser feeding a transformer chain.
   Directional: if the concrete run produces sinks (the parser accepted), the
   symbolic run does too and the result ledgers agree at every slot. *)
Lemma parser_source_lockstep :
  forall p gs0 f nm pp,
    let net := get_network_from_general p in
    let psrc := start_module net in
    all_transformers_except net psrc ->
    (forall x, ~ In psrc (downstream_modules net x)) ->
    lookup_module net psrc = Some (ParserModule nm pp) ->
    (forall ss, (mod_states gs0) ?? (unwrap psrc) = Some ss ->
        exists ps, ss = ParserMod ps /\
                   extract_targets_in_dom pp (module_header_map ss) /\
                   hdr_writes_present net (module_header_map ss)) ->
    state_writes_present net gs0 ->
    match eval_general_program_concrete p (concretize_sym_modnet_state gs0 f),
          eval_general_program_symbolic p gs0 with
    | None, _ => True
    | Some gc', Some gs' => ledger_agree_g gc' gs' f /\ state_writes_present net gs'
    | Some _, None => False end.
Proof.
  intros p gs0 f nm pp net psrc Hall Hnd Hlk Hss Hsw.
  unfold eval_general_program_concrete, eval_general_program_symbolic. fold net psrc.
  rewrite (concretize_slot gs0 f (unwrap psrc)).
  destruct ((mod_states gs0) ?? (unwrap psrc)) as [ss|] eqn:Ess; cbn [option_map]; [| exact I].
  destruct (Hss ss eq_refl) as [ps [-> [Hext Hwp]]].
  rewrite module_header_map_concretize.
  assert (Hin : In (ParserModule nm pp) (net_modules net)) by (eapply lookup_module_in; exact Hlk).
  destruct (net_modules net) as [|m0 rest] eqn:Emods; [ destruct Hin |]. cbn [length].
  cbn [eval_network_from_concrete eval_network_from_symbolic]. fold net psrc.
  rewrite ! Hlk, (concretize_slot gs0 f (unwrap psrc)), ! Ess. cbn [option_map].
  set (pss := {| p_header_map := module_header_map (ParserMod ps);
                 p_packet := sh_bit_map gs0; p_cursor := 0 |} : SymbolicParserState).
  replace (set_module_packet (set_module_header_map (ParserMod ps) (module_header_map (ParserMod ps)))
             (sh_bit_map gs0)) with (ParserMod pss)
    by (subst pss; destruct ps; reflexivity).
  replace (set_module_packet (set_module_header_map (concretize_sym_module_state (ParserMod ps) f)
             (PMap.map (fun e => eval_smt_arith e f) (module_header_map (ParserMod ps))))
             (sh_bit_map (concretize_sym_modnet_state gs0 f)))
    with (ParserMod (eval_sym_parser_state pss f))
    by (subst pss; destruct ps;
        cbn [concretize_sym_module_state module_header_map set_module_header_map
             set_module_packet concretize_sym_modnet_state sh_bit_map eval_sym_parser_state];
        reflexivity).
  destruct (eval_module_concrete (ParserModule nm pp) (ParserMod (eval_sym_parser_state pss f)))
    as [ls_c|] eqn:Emc; [| exact I].
  destruct ls_c as [tc|cps|dc]; cbn [eval_module_concrete] in Emc;
    [ destruct (eval_parser_concrete pp (eval_sym_parser_state pss f)); discriminate Emc
    | | destruct (eval_parser_concrete pp (eval_sym_parser_state pss f)); discriminate Emc ].
  assert (Hextp : extract_targets_in_dom pp (p_header_map pss)) by (subst pss; exact Hext).
  destruct (source_parser_module_step f nm pp pss cps Hextp Emc) as [Emsym Hag].
  rewrite Emsym. cbn [module_header_map].
  (* ledgers after the parser step agree *)
  set (gc1 := set_gps_mod_states (concretize_sym_modnet_state gs0 f)
                (PMap.set (unwrap psrc) (ParserMod cps) (mod_states (concretize_sym_modnet_state gs0 f)))).
  set (gs1 := set_gps_mod_states gs0 (PMap.set (unwrap psrc)
                (ParserMod {| p_header_map := spr_headers (eval_parser_symbolic pp pss);
                              p_packet := p_packet pss; p_cursor := p_cursor pss |}) (mod_states gs0))).
  assert (Hled1 : ledger_agree_g gc1 gs1 f).
  { intro n. subst gc1 gs1. unfold set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
    destruct (Coqlib.peq n (unwrap psrc)) as [Eq|Ne].
    - cbn [slot_agree_g]. exact Hag.
    - exact (ledger_agree_g_concretize gs0 f n). }
  assert (Hsw1 : state_writes_present net gs1).
  { intros name m' ss' Hlk' Hslot' sv Hsv. subst gs1.
    unfold set_gps_mod_states in Hslot'. cbn [mod_states] in Hslot'. rewrite pmap_set_qq in Hslot'.
    destruct (Coqlib.peq (unwrap name) (unwrap psrc)) as [Eq|Ne].
    - inversion Hslot'. (* ParserMod = TransformerMod: impossible *)
    - eapply Hsw; [ exact Hlk' | exact Hslot' | exact Hsv ]. }
  assert (Hhm1 : hm_agree (p_header_map cps) (spr_headers (eval_parser_symbolic pp pss)) f) by exact Hag.
  assert (Hdom1 : hdr_writes_present net (spr_headers (eval_parser_symbolic pp pss)))
    by (apply parser_out_writes_present; subst pss; exact Hwp).
  (* downstream fold via the generalized lockstep *)
  apply (fold_lockstep_g net psrc _ _ _ _ (length rest) f
           (fun start' gc' gs' Hns' Hl Hs =>
              network_lockstep_g (length rest) net psrc start' _ _ _ _ f gc' gs'
                Hall Hns' Hnd Hhm1 Hdom1 Hl Hs)).
  - intros d Hd Heq. subst d. apply (Hnd psrc). exact Hd.
  - exact Hled1.
  - exact Hsw1.
Qed.

(* ------------------------------------------------------------------ *)
(* Part 6: sink extraction and the whole-checker soundness. *)

(* Generalized sink agreement: agreeing ledgers have pointwise slot_agree_g
   sink lists (the parser-aware analogue of get_sink_states_agree). *)
Lemma get_sink_states_agree_g :
  forall net gc gs f,
    ledger_agree_g gc gs f ->
    Forall2 (fun mc ms => slot_agree_g mc ms f)
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

(* The source-parser well-formedness bundle for the packet-seeded initial state:
   every non-source module is a transformer, the source is a parser with in-degree
   0 (never a downstream target) whose extractions target — and whose write
   headers lie in — its seeded header interface, and the state-write invariant. *)
Definition parser_source_ok (pre : String.string) (p : GeneralCaracaraProgram) (n : nat) : Prop :=
  let net := get_network_from_general p in
  let psrc := start_module net in
  let gs := init_general_symbolic_state_n pre p n in
  all_transformers_except net psrc /\
  (forall x, ~ In psrc (downstream_modules net x)) /\
  (exists nm pp, lookup_module net psrc = Some (ParserModule nm pp) /\
     (forall ss, (mod_states gs) ?? (unwrap psrc) = Some ss ->
        exists ps, ss = ParserMod ps /\
                   extract_targets_in_dom pp (module_header_map ss) /\
                   hdr_writes_present net (module_header_map ss))) /\
  state_writes_present net gs.

(* Single-sink header agreement for a source-parser pipeline: if the symbolic
   run's sinks are a single transformer [sym], the concrete run yields a single
   transformer sink [cs] agreeing with [sym] under [f]. *)
Lemma header_sink_agree_parser_source :
  forall pre p n f sym,
    parser_source_ok pre p n ->
    eval_general_program_symbolic_sinks p (init_general_symbolic_state_n pre p n)
      = Some [TransformerMod sym] ->
    forall l,
    eval_general_program_concrete_sinks p
      (concretize_sym_modnet_state (init_general_symbolic_state_n pre p n) f) = Some l ->
    exists cs, l = [TransformerMod cs] /\ ts_agree cs sym f.
Proof.
  intros pre p n f sym Hok Hsym l Hconc.
  destruct Hok as [Hall [Hnd [[nm [pp [Hlk Hss]]] Hsw]]].
  unfold eval_general_program_symbolic_sinks in Hsym.
  unfold eval_general_program_concrete_sinks in Hconc.
  destruct (eval_general_program_symbolic p (init_general_symbolic_state_n pre p n))
    as [ls|] eqn:Es; [| discriminate].
  destruct (eval_general_program_concrete p
              (concretize_sym_modnet_state (init_general_symbolic_state_n pre p n) f))
    as [lc|] eqn:Ec; [| discriminate].
  pose proof (parser_source_lockstep p (init_general_symbolic_state_n pre p n) f nm pp
                Hall Hnd Hlk Hss Hsw) as Hstep.
  rewrite Ec, Es in Hstep. destruct Hstep as [Hled _].
  pose proof (get_sink_states_agree_g (get_network_from_general p) lc ls f Hled) as HF.
  injection Hsym as Hsym'. injection Hconc as Hconc'.
  rewrite Hconc' in HF. rewrite Hsym' in HF.
  inversion HF as [| mc ms lc' ls' Hslot HF' Elc Els]; subst.
  inversion HF'; subst.
  unfold slot_agree_g in Hslot.
  destruct mc as [cs| |]; try contradiction.
  exists cs. split; [reflexivity | exact Hslot].
Qed.
