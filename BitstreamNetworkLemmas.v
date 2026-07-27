(* 

(* ================================================================== *)
(* Gap B, layer 2: deparser output commutation.                         *)
(*                                                                     *)
(* Assembles the residual keystone ([BitstreamResidualLemmas]) with the   *)
(* deparser commute lemmas: the [f]-concretization of a deparser's output  *)
(* bitstream ([deparser_output_bitstream]) is its concrete emitted bits     *)
(* followed by the concretized residual — i.e. exactly the concrete          *)
(* deparser's output packet ([emitted ++ residual]).                          *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrVarLike.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrConcreteSemanticsDeparser.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrSymbolicSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import DeparserCommuteLemmas.
From MyProject Require Import BitstreamResidualLemmas.
From MyProject Require Import ModnetHeaderLemmas.
From MyProject Require Import ModnetParserSourceLemmas.
From MyProject Require Import Maps.

Transparent lookup_varlike_map.

(* Concrete emission depends on the header map only through its lookups, so two
   maps agreeing at every lookup emit the same bits. *)
Lemma emit_bits_concrete_ext : forall m1 m2 emits,
  (forall h : Header, lookup_varlike_map m1 h = lookup_varlike_map m2 h) ->
  List.flat_map (emit_bits_concrete m1) emits
    = List.flat_map (emit_bits_concrete m2) emits.
Proof.
  intros m1 m2 emits Hext. induction emits as [|[h w] rest IH]; [reflexivity|].
  cbn [flat_map emit_bits_concrete]. rewrite (Hext h), IH. reflexivity.
Qed.

(* A lookup on the [PMap.map]-concretization is the f-evaluation of the lookup. *)
Lemma lookup_map_concretize : forall (m : PMap.t SmtArithExpr) (h : Header) f,
  lookup_varlike_map (PMap.map (fun e => eval_smt_arith e f) m) h
    = eval_smt_arith (lookup_varlike_map m h) f.
Proof.
  intros m h f. unfold lookup_varlike_map. rewrite PMap.gmap. reflexivity.
Qed.

(* The deparser output commutation: [sb_concrete] of the symbolic output
   bitstream is the concrete emitted bits (reading the concretized header map)
   followed by [sb_concrete] of the incoming residual. *)
Lemma deparser_output_commute : forall f d hm residual,
  sb_concrete (deparser_output_bitstream d hm residual) f
    = List.flat_map
        (emit_bits_concrete (PMap.map (fun e => eval_smt_arith e f) hm))
        (deparser_emits d)
      ++ sb_concrete residual f.
Proof.
  intros f d hm residual. unfold deparser_output_bitstream.
  rewrite sb_concrete_app, sb_concrete_allvalid_map, <- emitted_bits_commute.
  reflexivity.
Qed.

(* ================================================================== *)
(* Half 2: the concrete bitstream network refines the plain cursor      *)
(* network.  When the plain [eval_network_from_concrete] succeeds (no     *)
(* parser rejected), the concrete bitstream twin returns the SAME ledger, *)
(* the accept flag unchanged, and an outgoing residual equal to the        *)
(* residual the plain network threads.  Pure concrete reasoning.           *)
(* ================================================================== *)

Lemma bs_fold_none_c :
  forall net f_hdrs f_pkt fuel' rest,
  List.fold_left
    (fun acc_opt dst =>
       match acc_opt with
       | None => None
       | Some (gs_acc, acc_cond, _) =>
           eval_network_bitstream_concrete net dst f_hdrs f_pkt gs_acc acc_cond fuel'
       end) rest None = None.
Proof. intros. induction rest; simpl; auto. Qed.

(* The plain and bitstream concrete module steps produce the same updated
   state and the same downstream residual, when the plain step succeeds. *)
Lemma module_step_refine :
  forall m ls f_hdrs f_pkt ls'',
  eval_module_concrete m (set_module_packet (set_module_header_map ls f_hdrs) f_pkt) = Some ls'' ->
  eval_module_bitstream_concrete m ls f_hdrs f_pkt
    = Some (ls'', true,
            match ls'' with
            | ParserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
            | DeparserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
            | TransformerMod _ => f_pkt
            end).
Proof.
  intros m ls f_hdrs f_pkt ls'' H.
  destruct m as [nm p | nm d | nm sts ctls t]; destruct ls as [ts|ps0|ps0];
    cbn [eval_module_concrete eval_module_bitstream_concrete
         set_module_packet set_module_header_map] in *;
    try discriminate H.
  - (* parser *)
    destruct (eval_parser_concrete p _) as [cps|] eqn:Ep; [| discriminate H].
    injection H as <-. cbn [p_cursor p_packet]. reflexivity.
  - (* deparser *)
    injection H as <-. cbn [eval_deparser_concrete p_cursor p_packet skipn]. reflexivity.
  - (* transformer *)
    injection H as <-. reflexivity.
Qed.

(* A no-fan-out network has ≤ 1 downstream, so the downstream list is [] or [x]. *)
Lemma downstream_nil_or_single : forall net start,
  no_fan_out net ->
  downstream_modules net start = [] \/ exists x, downstream_modules net start = [x].
Proof.
  intros net start Hnf. specialize (Hnf start).
  destruct (downstream_modules net start) as [|x [|y tl]].
  - left. reflexivity.
  - right. exists x. reflexivity.
  - simpl in Hnf. exfalso. apply le_S_n in Hnf. inversion Hnf.
Qed.

(* A concrete module step producing a deparser state leaves its cursor at 0. *)
Lemma module_concrete_deparser_cursor : forall m X ds,
  eval_module_concrete m X = Some (DeparserMod ds) -> p_cursor ds = 0.
Proof.
  intros m X ds H. destruct m as [nm p | nm d | nm sts ctls t];
    cbn [eval_module_concrete] in H;
    destruct X as [ts|ps|ps]; try discriminate H.
  - destruct (eval_parser_concrete p ps); discriminate H.
  - injection H as <-. reflexivity.
Qed.

(* --- Graph bookkeeping to pin the sink output. --- *)

Lemma lookup_module_name : forall net start m,
  lookup_module net start = Some m -> get_mod_name m = start.
Proof.
  intros net start m H. unfold lookup_module in H.
  apply find_some in H. destruct H as [_ Hb].
  apply CrIdentifiers.posesque_eqb_iff in Hb. exact Hb.
Qed.

Lemma pmap_set_qq : forall {T} (m : PMap.t T) k v n,
  (PMap.set k v m) ?? n = if Coqlib.peq n k then Some v else m ?? n.
Proof. intros T m k v n. unfold PMap.set. cbn [snd]. apply PTree.gsspec. Qed.

Lemma lookup_module_in : forall net name m,
  lookup_module net name = Some m -> In m (net_modules net).
Proof.
  intros net name m H. unfold lookup_module in H.
  apply find_some in H. destruct H as [Hin _]. exact Hin.
Qed.

Lemma filter_nil_existsb : forall {A} (p : A -> bool) l,
  filter p l = [] -> existsb p l = false.
Proof.
  intros A p l. induction l as [|x xs IH]; [reflexivity|].
  simpl. destruct (p x) eqn:Hp; [ discriminate | exact IH ].
Qed.

Lemma downstream_empty_is_sink : forall net start m,
  lookup_module net start = Some m ->
  downstream_modules net start = [] ->
  is_sink net m = true.
Proof.
  intros net start m Hlk Hd. unfold is_sink.
  rewrite (lookup_module_name net start m Hlk).
  unfold downstream_modules in Hd.
  rewrite (filter_nil_existsb _ _ Hd). reflexivity.
Qed.

Lemma single_sink_singleton : forall net m,
  single_sink net -> In m (net_modules net) -> is_sink net m = true ->
  sink_modules net = [m].
Proof.
  intros net m Hss Hin His. unfold single_sink, sink_modules in *.
  assert (Hinf : In m (filter (is_sink net) (net_modules net)))
    by (apply filter_In; split; assumption).
  destruct (filter (is_sink net) (net_modules net)) as [|a [|b tl]] eqn:Ef;
    simpl in Hss; try discriminate.
  destruct Hinf as [->|[]]. reflexivity.
Qed.

(* Refinement (with sink pinning): when the plain concrete network succeeds, the
   concrete bitstream twin returns the SAME ledger and accept flag, and its
   outgoing residual is exactly the deparser sink's output packet. *)
Lemma refine_net : forall fuel net start f_hdrs f_pkt gs gs' b,
  no_fan_out net -> single_sink net ->
  eval_network_from_concrete net start f_hdrs f_pkt gs fuel = Some gs' ->
  exists out, eval_network_bitstream_concrete net start f_hdrs f_pkt gs b fuel
                = Some (gs', b, out) /\
    (forall ds, get_sink_states net (mod_states gs') = [DeparserMod ds] -> out = p_packet ds).
Proof.
  induction fuel as [|fuel' IH]; intros net start f_hdrs f_pkt gs gs' b Hnf Hss Hp.
  - discriminate Hp.
  - cbn [eval_network_from_concrete] in Hp. cbn [eval_network_bitstream_concrete].
    destruct (lookup_module net start) as [m|] eqn:Elk; [| discriminate Hp].
    destruct ((mod_states gs) ?? (unwrap start)) as [ls|] eqn:Els; [| discriminate Hp].
    destruct (eval_module_concrete m (set_module_packet (set_module_header_map ls f_hdrs) f_pkt))
      as [ls''|] eqn:Em; [| discriminate Hp].
    rewrite (module_step_refine m ls f_hdrs f_pkt ls'' Em).
    set (gs1 := set_gps_mod_states gs (PMap.set (unwrap start) ls'' (mod_states gs))) in *.
    set (fp' := match ls'' with
                | ParserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                | DeparserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                | TransformerMod _ => f_pkt end) in *.
    destruct (downstream_nil_or_single net start Hnf) as [Hd | [x Hd]]; rewrite Hd in *.
    + (* sink node: pin the output *)
      injection Hp as <-. exists fp'. rewrite Bool.andb_true_r. split; [reflexivity|].
      intros ds Hsink.
      (* start's module is the unique sink; its slot in gs1 is ls'' *)
      assert (Hsm : sink_modules net = [m]).
      { apply single_sink_singleton; [ exact Hss
          | eapply lookup_module_in; exact Elk
          | eapply downstream_empty_is_sink; [ exact Elk | exact Hd ] ]. }
      unfold get_sink_states in Hsink. rewrite Hsm in Hsink. cbn [fold_right] in Hsink.
      rewrite (lookup_module_name net start m Elk) in Hsink.
      unfold gs1 in Hsink. unfold set_gps_mod_states in Hsink. cbn [mod_states] in Hsink.
      rewrite pmap_set_qq in Hsink.
      destruct (Coqlib.peq (unwrap start) (unwrap start)) as [_|Hne]; [| exfalso; apply Hne; reflexivity].
      injection Hsink as Hds.
      (* ls'' = DeparserMod ds, so fp' = skipn (cursor) pkt with cursor 0 *)
      assert (Hc0 : p_cursor ds = 0).
      { apply (module_concrete_deparser_cursor m
                 (set_module_packet (set_module_header_map ls f_hdrs) f_pkt) ds).
        rewrite <- Hds. exact Em. }
      unfold fp'. rewrite Hds. cbn [p_cursor p_packet]. rewrite Hc0. cbn [skipn]. reflexivity.
    + (* single downstream: thread the pin from the IH (same final gs') *)
      cbn [fold_left] in Hp |- *. rewrite Bool.andb_true_r.
      destruct (IH net x (module_header_map ls'') fp' gs1 gs' b Hnf Hss Hp)
        as [out [Hbs Hpin]].
      exists out. split; assumption.
Qed.


(* Top-level half-2: from the plain concrete sinks being a single deparser, the
   concrete bitstream network yields the same sink, accept [true], and output
   packet equal to that deparser's [p_packet]. *)
Lemma refine_toplevel : forall p C ds,
  no_fan_out (get_network_from_general p) ->
  single_sink (get_network_from_general p) ->
  eval_general_program_concrete_sinks p C = Some [DeparserMod ds] ->
  eval_general_program_bitstream_concrete p C
    = Some ([DeparserMod ds], true, p_packet ds).
Proof.
  intros p C ds Hnf Hss Hsinks.
  unfold eval_general_program_concrete_sinks in Hsinks.
  destruct (eval_general_program_concrete p C) as [ledger|] eqn:Eplain; [| discriminate Hsinks].
  injection Hsinks as Hsl.
  unfold eval_general_program_concrete in Eplain.
  unfold eval_general_program_bitstream_concrete.
  destruct ((mod_states C) ?? (unwrap (start_module (get_network_from_general p))))
    as [start_state|] eqn:Est; [| discriminate Eplain].
  destruct (refine_net (length (net_modules (get_network_from_general p)))
              (get_network_from_general p) (start_module (get_network_from_general p))
              (module_header_map start_state) (sh_bit_map C) C ledger true Hnf Hss Eplain)
    as [out [Hbs Hpin]].
  rewrite Hbs. rewrite Hsl. rewrite (Hpin ds Hsl). reflexivity.
Qed.

(* ================================================================== *)
(* Half 1 (downstream): lockstep between the concrete and symbolic       *)
(* bitstream networks over a TRANSFORMER*/DEPARSER tail (no parsers — the  *)
(* single source parser is stepped separately).  Transformers preserve     *)
(* header agreement and pass the bitstream through; the deparser sink emits *)
(* [emitted ++ residual], whose concretization matches by                   *)
(* [deparser_output_commute].  Uses [no_fan_out] to collapse the fold.      *)
(* ================================================================== *)

Definition transformer_or_deparser (net : ModuleNetwork) : Prop :=
  forall name m, lookup_module net name = Some m ->
    (exists nm s c t, m = TransformerModule nm s c t) \/
    (exists nm d, m = DeparserModule nm d).

Lemma bitstream_downstream_lockstep :
  forall fuel net psrc start f_hdrs_c f_hdrs_s f_bits_c f_bits_s gc gs acc_c acc_s f,
  no_fan_out net ->
  (forall name m, lookup_module net name = Some m -> name <> psrc ->
     (exists nm s c t, m = TransformerModule nm s c t) \/
     (exists nm d, m = DeparserModule nm d)) ->
  start <> psrc ->
  (forall x, ~ In psrc (downstream_modules net x)) ->
  hm_agree f_hdrs_c f_hdrs_s f ->
  hdr_writes_present net f_hdrs_s ->
  f_bits_c = sb_concrete f_bits_s f ->
  acc_c = eval_smt_bool acc_s f ->
  ledger_agree_g gc gs f ->
  state_writes_present net gs ->
  match eval_network_bitstream_concrete net start f_hdrs_c f_bits_c gc acc_c fuel,
        eval_network_bitstream_acc net start f_hdrs_s f_bits_s gs acc_s fuel with
  | None, None => True
  | Some (gc', ac, oc), Some (gs', as_, os) =>
      ac = eval_smt_bool as_ f /\ ledger_agree_g gc' gs' f /\ oc = sb_concrete os f
  | _, _ => False
  end.
Proof.
  induction fuel as [|fuel' IH];
    intros net psrc start f_hdrs_c f_hdrs_s f_bits_c f_bits_s gc gs acc_c acc_s f
           Hnf Htd Hns Hnd Hhm Hdom Hbits Hacc Hled Hsw.
  - exact I.
  - cbn [eval_network_bitstream_concrete eval_network_bitstream_acc].
    destruct (lookup_module net start) as [m|] eqn:Elk; [| exact I].
    pose proof (Hled (unwrap start)) as Hslot.
    destruct ((mod_states gc) ?? (unwrap start)) as [mc|] eqn:Egc;
    destruct ((mod_states gs) ?? (unwrap start)) as [ms|] eqn:Egs;
      cbn in Hslot; try contradiction; [| exact I].
    destruct (Htd start m Elk Hns) as [[nm [sts [ctls [t Hm]]]] | [nm [d Hm]]]; subst m.
    + (* transformer *)
      destruct mc as [cs|pc|pc]; destruct ms as [ss|ps|ps];
        cbn [slot_agree_g] in Hslot; try contradiction;
        try (cbn [eval_module_bitstream_concrete eval_module_bitstream_acc
                  set_module_packet set_module_header_map]; exact I).
      cbn [eval_module_bitstream_concrete eval_module_bitstream_acc
           set_module_packet set_module_header_map].
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
      set (gc1 := set_gps_mod_states gc (PMap.set (unwrap start) (TransformerMod nc) (mod_states gc))) in *.
      set (gs1 := set_gps_mod_states gs (PMap.set (unwrap start) (TransformerMod ns) (mod_states gs))) in *.
      assert (Hled1 : ledger_agree_g gc1 gs1 f).
      { intro n. unfold gc1, gs1, set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
        destruct (Coqlib.peq n (unwrap start)); [ cbn [slot_agree_g]; exact Hnew | exact (Hled n) ]. }
      assert (Hsw1 : state_writes_present net gs1).
      { intros name m' ss' Hlk' Hslot' sv Hsv. unfold gs1, set_gps_mod_states in Hslot'.
        cbn [mod_states] in Hslot'. rewrite pmap_set_qq in Hslot'.
        destruct (Coqlib.peq (unwrap name) (unwrap start)) as [Eq|Ne].
        - inversion Hslot' as [Hss']. apply unwrap_inj in Eq. subst name.
          rewrite Elk in Hlk'. inversion Hlk'. subst m'. subst ss'.
          cbn [get_transformer_m] in Hsv. apply is_varlike_state_eval_transformer_smt.
          apply is_varlike_inject_state_present.
          eapply Hsw; [exact Elk | exact Egs | cbn [get_transformer_m]; exact Hsv].
        - eapply Hsw; [exact Hlk' | exact Hslot' | exact Hsv]. }
      cbn [module_header_map].
      assert (Hacc1 : (acc_c && true)%bool = eval_smt_bool (SmtBoolAnd acc_s SmtTrue) f).
      { cbn [eval_smt_bool]. rewrite ! Bool.andb_true_r. exact Hacc. }
      destruct (downstream_nil_or_single net start Hnf) as [Hd | [x Hd]]; rewrite Hd.
      * split; [exact Hacc1 | split; [exact Hled1 | exact Hbits]].
      * cbn [fold_left].
        assert (Hxns : x <> psrc).
        { intro Heq; subst x. apply (Hnd start). rewrite Hd. left. reflexivity. }
        exact (IH net psrc x _ _ f_bits_c f_bits_s gc1 gs1 (acc_c && true)%bool
                 (SmtBoolAnd acc_s SmtTrue) f
                 Hnf Htd Hxns Hnd Hnewhm Hnewdom Hbits Hacc1 Hled1 Hsw1).
    + (* deparser *)
      destruct mc as [cs|pc|dc]; destruct ms as [ss|ps|ds];
        cbn [slot_agree_g] in Hslot; try contradiction;
        try (cbn [eval_module_bitstream_concrete eval_module_bitstream_acc
                  set_module_packet set_module_header_map]; exact I).
      cbn [eval_module_bitstream_concrete eval_module_bitstream_acc
           set_module_packet set_module_header_map module_header_map
           eval_deparser_concrete eval_deparser_symbolic p_header_map].
      (* deparser preserves the header map, and its output concretizes correctly *)
      assert (Hout : (List.flat_map (emit_bits_concrete f_hdrs_c) (deparser_emits d) ++ f_bits_c)
                     = sb_concrete (deparser_output_bitstream d f_hdrs_s f_bits_s) f).
      { rewrite deparser_output_commute. rewrite <- Hbits. f_equal.
        apply emit_bits_concrete_ext. intro h. rewrite lookup_map_concretize. apply Hhm. }
      assert (Hacc1 : (acc_c && true)%bool = eval_smt_bool (SmtBoolAnd acc_s SmtTrue) f).
      { cbn [eval_smt_bool]. rewrite ! Bool.andb_true_r. exact Hacc. }
      set (gc1 := set_gps_mod_states gc (PMap.set (unwrap start)
                    (DeparserMod {| p_header_map := f_hdrs_c;
                       p_packet := List.flat_map (emit_bits_concrete f_hdrs_c) (deparser_emits d) ++ f_bits_c;
                       p_cursor := 0 |}) (mod_states gc))) in *.
      set (gs1 := set_gps_mod_states gs (PMap.set (unwrap start)
                    (DeparserMod {| p_header_map := f_hdrs_s;
                       p_packet := List.flat_map (emit_bits_symbolic f_hdrs_s) (deparser_emits d) ++ List.map fst f_bits_s;
                       p_cursor := 0 |}) (mod_states gs))) in *.
      assert (Hled1 : ledger_agree_g gc1 gs1 f).
      { intro n. unfold gc1, gs1, set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
        destruct (Coqlib.peq n (unwrap start)) as [Eq|Ne].
        - cbn [slot_agree_g p_header_map]. exact Hhm.
        - exact (Hled n). }
      assert (Hsw1 : state_writes_present net gs1).
      { intros name m' ss' Hlk' Hslot' sv Hsv. unfold gs1, set_gps_mod_states in Hslot'.
        cbn [mod_states] in Hslot'. rewrite pmap_set_qq in Hslot'.
        destruct (Coqlib.peq (unwrap name) (unwrap start)) as [Eq|Ne].
        - discriminate Hslot'.
        - eapply Hsw; [exact Hlk' | exact Hslot' | exact Hsv]. }
      destruct (downstream_nil_or_single net start Hnf) as [Hd | [x Hd]]; rewrite Hd.
      * split; [exact Hacc1 | split; [exact Hled1 | exact Hout]].
      * cbn [fold_left].
        assert (Hxns : x <> psrc).
        { intro Heq; subst x. apply (Hnd start). rewrite Hd. left. reflexivity. }
        exact (IH net psrc x f_hdrs_c f_hdrs_s _ _ gc1 gs1 (acc_c && true)%bool
                 (SmtBoolAnd acc_s SmtTrue) f Hnf Htd Hxns Hnd Hhm Hdom Hout Hacc1 Hled1 Hsw1).
Qed.

(* ================================================================== *)
(* Half 1 (assembly): step the single SOURCE PARSER, then hand the       *)
(* transformer*/deparser tail to [bitstream_downstream_lockstep].         *)
(* ================================================================== *)

(* Once the concrete bitstream accept flag is [false] it stays [false]. *)
Lemma bs_acc_false_monotone : forall fuel net start f_hdrs f_bits gc gc' oc ac,
  no_fan_out net ->
  eval_network_bitstream_concrete net start f_hdrs f_bits gc false fuel = Some (gc', ac, oc) ->
  ac = false.
Proof.
  induction fuel as [|fuel' IH]; intros net start f_hdrs f_bits gc gc' oc ac Hnf H; [discriminate H|].
  cbn [eval_network_bitstream_concrete] in H.
  destruct (lookup_module net start) as [m|]; [| discriminate H].
  destruct ((mod_states gc) ?? (unwrap start)) as [ls|]; [| discriminate H].
  destruct (eval_module_bitstream_concrete m ls f_hdrs f_bits) as [[[ls'' a] ob]|]; [| discriminate H].
  cbn [andb] in H.
  destruct (downstream_nil_or_single net start Hnf) as [Hd|[x Hd]]; rewrite Hd in H.
  - injection H as <- <- <-. reflexivity.
  - cbn [fold_left] in H.
    exact (IH net x (module_header_map ls'') ob _ _ _ _ Hnf H).
Qed.



(* Helper: [map fst] undoes the all-valid wrapping. *)
Lemma map_fst_allvalid : forall (L : list SmtBoolExpr),
  List.map fst (List.map (fun b => (b, SmtTrue)) L) = L.
Proof. intros L. rewrite map_map. cbn [fst]. apply map_id. Qed.

(* Whole-program half-1 lockstep. *)
Lemma bitstream_lockstep_toplevel :
  forall p S f nm pp sinks_c oc,
    let net := get_network_from_general p in
    let psrc := start_module net in
    no_fan_out net ->
    (forall name m, lookup_module net name = Some m -> name <> psrc ->
       (exists nm2 s c t, m = TransformerModule nm2 s c t) \/
       (exists nm2 d, m = DeparserModule nm2 d)) ->
    (forall x, ~ In psrc (downstream_modules net x)) ->
    lookup_module net psrc = Some (ParserModule nm pp) ->
    (forall ss, (mod_states S) ?? (unwrap psrc) = Some ss ->
        exists ps, ss = ParserMod ps /\
                   extract_targets_in_dom pp (module_header_map ss) /\
                   hdr_writes_present net (module_header_map ss)) ->
    state_writes_present net S ->
    eval_general_program_bitstream_concrete p (concretize_sym_modnet_state S f)
      = Some (sinks_c, true, oc) ->
    match eval_general_program_bitstream_acc p S with
    | Some (_, a_s, os) => eval_smt_bool a_s f = true /\ oc = sb_concrete os f
    | None => False
    end.
Proof.
  intros p S f nm pp sinks_c oc net psrc Hnf Htd Hnd Hlk Hss Hsw Hcon.
  unfold eval_general_program_bitstream_concrete, eval_general_program_bitstream_acc in *.
  fold net psrc in Hcon |- *.
  rewrite (concretize_slot S f (unwrap psrc)) in Hcon.
  destruct ((mod_states S) ?? (unwrap psrc)) as [ss|] eqn:Ess; cbn [option_map] in Hcon; [| discriminate Hcon].
  destruct (Hss ss eq_refl) as [ps [-> [Hext Hwp]]].
  rewrite module_header_map_concretize in Hcon.
  assert (Hin : In (ParserModule nm pp) (net_modules net)) by (eapply lookup_module_in; exact Hlk).
  destruct (net_modules net) as [|m0 rest] eqn:Emods; [ destruct Hin |]. cbn [length] in Hcon |- *.
  cbn [eval_network_bitstream_concrete eval_network_bitstream_acc] in Hcon |- *. fold net psrc.
  rewrite ! Hlk in Hcon |- *.
  rewrite (concretize_slot S f (unwrap psrc)), Ess in Hcon. cbn [option_map] in Hcon.
  rewrite Ess.
  cbn [eval_module_bitstream_concrete eval_module_bitstream_acc] in Hcon |- *.
  (* undo the all-valid wrapping on the symbolic packet, so it becomes [sh_bit_map S] *)
  rewrite map_fst_allvalid.
  set (pss := {| p_header_map := module_header_map (ParserMod ps);
                 p_packet := sh_bit_map S; p_cursor := 0 |} : SymbolicParserState) in *.
  set (validity := List.map snd (List.map (fun b => (b, SmtTrue)) (sh_bit_map S))) in *.
  (* symbolic parser input is now definitionally [ParserMod pss] *)
  change (set_module_packet (set_module_header_map (ParserMod ps) (module_header_map (ParserMod ps)))
            (sh_bit_map S)) with (ParserMod pss).
  (* concrete parser input is [ParserMod (eval_sym_parser_state pss f)] *)
  change (set_module_packet (set_module_header_map (concretize_sym_module_state (ParserMod ps) f)
            (PMap.map (fun e => eval_smt_arith e f) (module_header_map (ParserMod ps))))
            (sh_bit_map (concretize_sym_modnet_state S f)))
    with (ParserMod (eval_sym_parser_state pss f)) in Hcon.
  cbn [eval_module_bitstream_concrete eval_module_bitstream_acc] in Hcon |- *.
  assert (Hallv : forall v, In v validity -> eval_smt_bool v f = true).
  { intros v Hv. unfold validity in Hv. rewrite map_map in Hv.
    apply in_map_iff in Hv. destruct Hv as [b [<- _]]. reflexivity. }
  assert (Hlenv : length validity = length (p_packet pss)).
  { unfold validity, pss. cbn [p_packet]. rewrite ! length_map. reflexivity. }
  destruct (eval_parser_concrete pp (eval_sym_parser_state pss f)) as [cps|] eqn:Epc.
  - pose proof (eval_parser_symbolic_v_accept f validity pp pss cps Hallv Epc) as Hpa.
    pose proof (source_parser_hm_agree f pp pss cps Hext Epc) as Hhm0.
    rewrite <- (eval_parser_symbolic_v_headers pp pss validity) in Hhm0.
    pose proof (eval_parser_residual_v_commute f validity pp pss cps Hlenv Hallv Epc) as Hres.
    set (rsym := eval_parser_symbolic_v pp pss validity) in *.
    set (gc1 := set_gps_mod_states (concretize_sym_modnet_state S f)
                  (PMap.set (unwrap psrc) (ParserMod cps)
                     (mod_states (concretize_sym_modnet_state S f)))) in *.
    set (gs1 := set_gps_mod_states S (PMap.set (unwrap psrc)
                  (ParserMod {| p_header_map := spr_headers rsym;
                                p_packet := p_packet pss; p_cursor := p_cursor pss |}) (mod_states S))) in *.
    assert (Hled1 : ledger_agree_g gc1 gs1 f).
    { intro n. unfold gc1, gs1, set_gps_mod_states. cbn [mod_states]. rewrite ! pmap_set_qq.
      destruct (Coqlib.peq n (unwrap psrc)) as [Eq|Ne].
      - cbn [slot_agree_g p_header_map]. exact Hhm0.
      - exact (ledger_agree_g_concretize S f n). }
    assert (Hsw1 : state_writes_present net gs1).
    { intros name m' ss' Hlk' Hslot' sv Hsv. unfold gs1, set_gps_mod_states in Hslot'.
      cbn [mod_states] in Hslot'. rewrite pmap_set_qq in Hslot'.
      destruct (Coqlib.peq (unwrap name) (unwrap psrc)) as [Eq|Ne].
      - discriminate Hslot'.
      - eapply Hsw; [exact Hlk' | exact Hslot' | exact Hsv]. }
    assert (Hdom1 : hdr_writes_present net (spr_headers rsym)).
    { unfold rsym. rewrite (eval_parser_symbolic_v_headers pp pss validity).
      apply parser_out_writes_present. unfold pss. cbn [p_header_map]. exact Hwp. }
    assert (Hbits1 : List.skipn (p_cursor cps) (p_packet cps)
                     = sb_concrete (eval_parser_residual_v pp pss validity) f)
      by (symmetry; exact Hres).
    cbn [module_header_map] in Hcon |- *.
    destruct (downstream_nil_or_single net psrc Hnf) as [Hd | [x Hd]]; rewrite Hd in Hcon |- *.
    + cbv beta iota in Hcon |- *. injection Hcon as _ Hoc.
      split.
      * cbn [eval_smt_bool]. rewrite Hpa. reflexivity.
      * rewrite <- Hoc. exact Hbits1.
    + cbn [fold_left] in Hcon |- *.
      change (p_header_map {| p_header_map := spr_headers rsym; p_packet := p_packet pss; p_cursor := p_cursor pss |}) with (spr_headers rsym) in *.
      assert (Hxns : x <> psrc)
        by (intro Heq; subst x; apply (Hnd psrc); rewrite Hd; left; reflexivity).
      assert (Hacc0 : (true && true)%bool = eval_smt_bool (SmtBoolAnd SmtTrue (spr_accept rsym)) f)
        by (cbn [eval_smt_bool]; rewrite Hpa; reflexivity).
      pose proof (bitstream_downstream_lockstep (length rest) net psrc x
                    (p_header_map cps) (spr_headers rsym)
                    (List.skipn (p_cursor cps) (p_packet cps))
                    (eval_parser_residual_v pp pss validity)
                    gc1 gs1 (true && true)%bool (SmtBoolAnd SmtTrue (spr_accept rsym)) f
                    Hnf Htd Hxns Hnd Hhm0 Hdom1 Hbits1 Hacc0 Hled1 Hsw1) as Hstep.
      destruct (eval_network_bitstream_concrete net x (p_header_map cps)
                  (List.skipn (p_cursor cps) (p_packet cps)) gc1 (true && true) (length rest))
        as [[[gc' ac] oc']|] eqn:Ec.
      2:{ cbv beta iota in Hcon. discriminate Hcon. }
      destruct (eval_network_bitstream_acc net x (spr_headers rsym)
                  (eval_parser_residual_v pp pss validity) gs1
                  (SmtBoolAnd SmtTrue (spr_accept rsym)) (length rest))
        as [[[gs' as_] os]|] eqn:Es; cbv beta iota in Hstep; [| contradiction Hstep].
      destruct Hstep as [Hac [Hled' Hout']].
      cbv beta iota in Hcon. injection Hcon as Hs Hacc Hoc. cbv beta iota.
      split.
      * rewrite <- Hac. exact Hacc.
      * rewrite <- Hoc. exact Hout'.
  - exfalso. cbn [andb] in Hcon.
    destruct (downstream_nil_or_single net psrc Hnf) as [Hd | [x Hd]]; rewrite Hd in Hcon.
    + cbv beta iota in Hcon. injection Hcon as _ Hbad _. discriminate Hbad.
    + cbn [fold_left] in Hcon.
      match type of Hcon with
      | context[eval_network_bitstream_concrete ?a ?b ?c ?d ?e false ?g] =>
          destruct (eval_network_bitstream_concrete a b c d e false g) as [[[gg aa] oo]|] eqn:E
      end.
      * pose proof (bs_acc_false_monotone _ _ _ _ _ _ _ _ _ Hnf E) as Ha. subst aa.
        cbv beta iota in Hcon. injection Hcon as _ Hbad _. discriminate Hbad.
      * cbv beta iota in Hcon. discriminate Hcon.
Qed. *)
