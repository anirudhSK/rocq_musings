From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import Maps.
From MyProject Require Import SmtTypes.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtQuery.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import ModnetHeaderLemmas.
From MyProject Require Import ModnetParserSourceLemmas.
From MyProject Require Import BitstreamResidualLemmas.
From MyProject Require Import BitstreamNetworkLemmas.
From MyProject Require Import SmtHelperLemmas.

Definition keys_from_map {T A : Type} (fn : positive -> A) (m : PMap.t T) : list A :=
  List.map fn (List.map fst (PTree.elements (snd m))).

(* ------------------------------------------------------------------ *)
(* Header-map equivalence (the original network check): two transformer  *)
(* networks are equivalent when their single (transformer) sinks agree on *)
(* every signature header.  Retained for header-observable pipelines; the *)
(* bitstream-I/O check below is the default [modnet_equivalence_checker]. *)
Definition modnet_header_equivalence_checker
  (p1 : GeneralCaracaraProgram) (p2 : GeneralCaracaraProgram) (input_len : nat)
  : EquivalenceResult :=
  let sym1_opt := eval_general_program_symbolic_sinks p1 (init_general_symbolic_state_n "p1" p1 input_len) in
  let sym2_opt := eval_general_program_symbolic_sinks p2 (init_general_symbolic_state_n "p2" p2 input_len) in
  match sym1_opt, sym2_opt with
  | Some [TransformerMod sym1], Some [TransformerMod sym2] => (* assume one sink *)
    let h_map : PMap.t SmtArithExpr := (t_header_map sym1) in
    let header_ids : list Header := get_signature_from_general p1 in
    match smt_query (check_headers_and_state_vars sym1 sym2 header_ids []) with
    | SmtUnsat => Equivalent
    | SmtSat f => NotEquivalent f
    | SmtUnknown => NotEquivalentUnknown
    end
  | _, _ => NotEquivalentVariablesDiffer
  end.

(* ------------------------------------------------------------------ *)
(* Bitstream-I/O equivalence.                                          *)
(*                                                                     *)
(* The network's real interface is (input packet bits -> output packet  *)
(* bits): a source parser consumes the incoming bitstream, and a sink    *)
(* deparser emits the outgoing bitstream.  Two programs are equivalent   *)
(* when, for every [n]-bit input packet, their sinks emit the same        *)
(* output packet. *)

(* Two symbolic bits differ (XOR). *)
Definition smt_bit_neq (b1 b2 : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd b1 (SmtBoolNot b2)) (SmtBoolAnd (SmtBoolNot b1) b2).

(* Two positions of a validity-annotated bitstream differ: their validity
   disagrees, or both are valid and the bits differ.  (Padding — [valid =
   SmtFalse] on both sides — never contributes, so a data-dependent length is
   compared correctly.) *)
Definition sym_bit_differ (x1 x2 : SymBit) : SmtBoolExpr :=
  let '(b1, v1) := x1 in
  let '(b2, v2) := x2 in
  SmtBoolOr (smt_bit_neq v1 v2)
            (SmtBoolAnd (SmtBoolAnd v1 v2) (smt_bit_neq b1 b2)).

(* The two output bitstreams differ: some aligned position differs, or their
   (static max) lengths differ.  A SAT model of this query is an input packet on
   which the two programs emit different output packets. *)
Fixpoint bitstreams_differ_v (out1 out2 : SymBitstream) : SmtBoolExpr :=
  match out1, out2 with
  | nil, nil => SmtFalse
  | x1 :: r1, x2 :: r2 => SmtBoolOr (sym_bit_differ x1 x2) (bitstreams_differ_v r1 r2)
  | _, _ => SmtTrue   (* different max output lengths: they always differ *)
  end.

(* The two programs observably differ when they either accept different packets,
   or both accept but emit different output bitstreams.  Mirrors the single-parser
   [parser_neq_query]: [smt_bit_neq a1 a2] is the accept-XOR, and the output
   comparison is only demanded when both accept.  A SAT model is an input packet
   witnessing the difference. *)
Definition modnet_neq_query
  (a1 a2 : SmtBoolExpr) (out1 out2 : SymBitstream) : SmtBoolExpr :=
  SmtBoolOr (smt_bit_neq a1 a2)
            (SmtBoolAnd (SmtBoolAnd a1 a2) (bitstreams_differ_v out1 out2)).

(* Both programs are run symbolically from a shared [input_len]-bit input
   packet, so they range over one common input bitstream.  Their single sinks
   must be deparsers; equivalence is UNSAT of the [modnet_neq_query].

   Reject handling: the network runs through the accept/bitstream-aware semantics
   ([eval_general_program_bitstream_acc] -> [eval_parser_symbolic]), which
   threads each parser's [spr_accept] as a symbolic predicate and hands the
   conjunction ([a1] / [a2]) to the query.  A data-dependent [Reject] (which
   concretely makes [eval_parser_concrete] return [None] and aborts the network)
   is thus modelled as "accept condition is false" rather than being swallowed.

   Residual handling: the sink output ([out1] / [out2]) is a validity-annotated
   bitstream ([SymBitstream]).  A parser's unconsumed tail is emitted with a
   [valid] channel and merged across [select] branches ([eval_parser_residual_v]),
   so the data-dependent consumed length is represented exactly rather than by a
   single cursor — the deparser then prepends its emitted bits ahead of it.

   Chained parsers: a parser reading a *data-dependent* residual from an upstream
   parser is modelled EXACTLY — [eval_module_bitstream_acc] feeds the downstream
   parser the incoming validity channel, and [eval_parser_symbolic_v] requires
   every extracted position to be valid (else that parse cannot accept), while
   [eval_parser_residual_v] carries the incoming validity forward into the tail.
   With an all-valid source packet the validity guard is vacuous, matching the
   single-source-parser behaviour.

   REMAINING CAVEAT: on a fan-out DAG the sink's bitstream is taken from the last
   path explored; the intended topology is a linear chain ([is_linear_chain]).
   The [Admitted] lemmas below do not close this (nor do they yet verify the
   chained-parser model above — that is a semantic-exactness fix, still awaiting
   the Gap B bitstream commutation proof). *)
Definition modnet_equivalence_checker
  (p1 : GeneralCaracaraProgram) (p2 : GeneralCaracaraProgram) (input_len : nat)
  : EquivalenceResult :=
  let sym1_opt := eval_general_program_bitstream_acc p1 (init_general_symbolic_state_n "p1" p1 input_len) in
  let sym2_opt := eval_general_program_bitstream_acc p2 (init_general_symbolic_state_n "p2" p2 input_len) in
  match sym1_opt, sym2_opt with
  | Some ([DeparserMod _], a1, out1), Some ([DeparserMod _], a2, out2) => (* assume one (deparser) sink *)
    match smt_query (modnet_neq_query a1 a2 out1 out2) with
    | SmtUnsat => Equivalent
    | SmtSat f => NotEquivalent f
    | SmtUnknown => NotEquivalentUnknown
    end
  | _, _ => NotEquivalentVariablesDiffer
  end.

Definition is_linear_chain (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  is_dag net /\
  single_sink net /\
  no_fan_out net /\
  no_fan_in net.

(* NOTE/TODO: Open question about state equivalence and what it means for states to be equivalent for different network topologies *)
Lemma modnet_header_equivalence_checker_sound :
  forall p1 p2 input_len,
  (* if two well-formed programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and are transformer-only (see [transformer_ok]: every module a transformer,
     with write-targets present in the seeded initial symbolic state) *)
  transformer_ok "p1" p1 ->
  transformer_ok "p2" p2 ->
  (* and they're considered equivalent over an [input_len]-bit input packet *)
  modnet_header_equivalence_checker p1 p2 input_len = Equivalent ->
  (* then when starting from their initial concrete states *)
  forall s_i1 s_i2 c_i1 c_i2 f,
  s_i1 = init_general_symbolic_state_n "p1" p1 input_len ->
  s_i2 = init_general_symbolic_state_n "p2" p2 input_len ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  (* if they produce some final state *)
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* there is only one such final state *)
  exists c_f1 c_f2,
  l1 = [c_f1] /\
  l2 = [c_f2] /\
  (* and the output headers are identical.  NOTE: over [get_signature_from_general]
     (the OUTPUT signature the checker's [smt_query] actually ranges over), not
     [get_headers_from_general] (the input header format).  The query says nothing
     about input-only headers, so the original [get_headers_from_general] made this
     unprovable; this matches the [_complete] lemma below. *)
  (forall h, In h (get_signature_from_general p1) ->
    lookup_varlike_map (module_header_map c_f1) h
    = lookup_varlike_map (module_header_map c_f2) h).
Proof.
  intros p1 p2 input_len Hwf1 Hwf2 Hlc1 Hlc2 Hok1 Hok2 Hcheck
         s_i1 s_i2 c_i1 c_i2 f Hs1 Hs2 Hc1 Hc2 l1 l2 Hl1 Hl2.
  subst s_i1 s_i2 c_i1 c_i2.
  unfold modnet_header_equivalence_checker in Hcheck.
  destruct (eval_general_program_symbolic_sinks p1 (init_general_symbolic_state_n "p1" p1 input_len))
    as [[| [sym1 | ps1 | ps1] [| x1 xs1] ] |] eqn:Esym1; try discriminate Hcheck.
  destruct (eval_general_program_symbolic_sinks p2 (init_general_symbolic_state_n "p2" p2 input_len))
    as [[| [sym2 | ps2 | ps2] [| x2 xs2] ] |] eqn:Esym2; try discriminate Hcheck.
  destruct (smt_query (check_headers_and_state_vars sym1 sym2 (get_signature_from_general p1) []))
    eqn:Hq; try discriminate Hcheck.
  destruct (header_sink_agree_gs p1 (init_general_symbolic_state_n "p1" p1 input_len) f sym1
              (transformer_ok_n "p1" p1 input_len Hok1) Esym1 l1 Hl1) as [cs1 [Hl1eq Hts1]].
  destruct (header_sink_agree_gs p2 (init_general_symbolic_state_n "p2" p2 input_len) f sym2
              (transformer_ok_n "p2" p2 input_len Hok2) Esym2 l2 Hl2) as [cs2 [Hl2eq Hts2]].
  exists (TransformerMod cs1), (TransformerMod cs2).
  split; [exact Hl1eq | split; [exact Hl2eq |]].
  intros h Hh. cbn [module_header_map].
  pose proof (smt_query_sound_none _ Hq f) as Hqf.
  apply check_headers_and_state_vars_false in Hqf. destruct Hqf as [Hhdr _].
  specialize (Hhdr h Hh). apply smt_bool_eq_true in Hhdr.
  rewrite (ts_agree_hm cs1 sym1 f Hts1 h), (ts_agree_hm cs2 sym2 f Hts2 h).
  exact Hhdr.
Qed.

Lemma modnet_header_equivalence_checker_complete :
  forall p1 p2 input_len f,
  (* if two programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and are transformer-only *)
  transformer_ok "p1" p1 ->
  transformer_ok "p2" p2 ->
  (* if they're not considered equivalent over an [input_len]-bit input packet *)
  modnet_header_equivalence_checker p1 p2 input_len = NotEquivalent f ->
  (* then when starting from their initial concrete states *)
  forall s_i1 s_i2 c_i1 c_i2,
  s_i1 = init_general_symbolic_state_n "p1" p1 input_len ->
  s_i2 = init_general_symbolic_state_n "p2" p2 input_len ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  (* if they produce a some final state *)
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* they each produce a single final state *)
  exists cf_1 cf_2,
  l1 = [cf_1] /\
  l2 = [cf_2] /\
  (* and the output headers differ on at least one header *)
  (exists h, In h (get_signature_from_general p1) /\
    lookup_varlike_map (module_header_map cf_1) h
    <> lookup_varlike_map (module_header_map cf_2) h).
Proof.
  intros p1 p2 input_len f Hwf1 Hwf2 Hlc1 Hlc2 Hok1 Hok2 Hcheck
         s_i1 s_i2 c_i1 c_i2 Hs1 Hs2 Hc1 Hc2 l1 l2 Hl1 Hl2.
  subst s_i1 s_i2 c_i1 c_i2.
  unfold modnet_header_equivalence_checker in Hcheck.
  destruct (eval_general_program_symbolic_sinks p1 (init_general_symbolic_state_n "p1" p1 input_len))
    as [[| [sym1 | ps1 | ps1] [| x1 xs1] ] |] eqn:Esym1; try discriminate Hcheck.
  destruct (eval_general_program_symbolic_sinks p2 (init_general_symbolic_state_n "p2" p2 input_len))
    as [[| [sym2 | ps2 | ps2] [| x2 xs2] ] |] eqn:Esym2; try discriminate Hcheck.
  destruct (smt_query (check_headers_and_state_vars sym1 sym2 (get_signature_from_general p1) []))
    as [f0| |] eqn:Hq; try discriminate Hcheck.
  injection Hcheck as Hcheck'. subst f0.
  destruct (header_sink_agree_gs p1 (init_general_symbolic_state_n "p1" p1 input_len) f sym1
              (transformer_ok_n "p1" p1 input_len Hok1) Esym1 l1 Hl1) as [cs1 [Hl1eq Hts1]].
  destruct (header_sink_agree_gs p2 (init_general_symbolic_state_n "p2" p2 input_len) f sym2
              (transformer_ok_n "p2" p2 input_len Hok2) Esym2 l2 Hl2) as [cs2 [Hl2eq Hts2]].
  exists (TransformerMod cs1), (TransformerMod cs2).
  split; [exact Hl1eq | split; [exact Hl2eq |]].
  pose proof (smt_query_sound_some _ _ Hq) as Hqf.
  apply check_headers_and_state_vars_true in Hqf.
  destruct Hqf as [[h [Hh Hneq]] | [sv [Hsv _]]].
  - exists h. split; [exact Hh|]. cbn [module_header_map].
    apply smt_bool_eq_false in Hneq.
    rewrite (ts_agree_hm cs1 sym1 f Hts1 h), (ts_agree_hm cs2 sym2 f Hts2 h).
    exact Hneq.
  - simpl in Hsv. contradiction.
Qed.

Print Assumptions modnet_header_equivalence_checker_sound.
Print Assumptions modnet_header_equivalence_checker_complete.

(* ------------------------------------------------------------------ *)
(* Gap A closure: header-checker soundness for a SOURCE PARSER feeding a
   transformer chain ([Parser] -> Transformer* -> transformer sink).  The
   source parser consumes the real [input_len]-bit input packet; downstream
   transformers observe its extracted header map.  See [parser_source_ok]
   (ModnetParserSourceLemmas.v) for the well-formedness bundle: every non-source
   module is a transformer, the source is an in-degree-0 parser whose extractions
   and write headers stay within its declared header interface. *)
Lemma modnet_header_equivalence_checker_sound_parser_source :
  forall p1 p2 input_len,
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  parser_source_ok "p1" p1 input_len ->
  parser_source_ok "p2" p2 input_len ->
  modnet_header_equivalence_checker p1 p2 input_len = Equivalent ->
  forall s_i1 s_i2 c_i1 c_i2 f,
  s_i1 = init_general_symbolic_state_n "p1" p1 input_len ->
  s_i2 = init_general_symbolic_state_n "p2" p2 input_len ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  exists c_f1 c_f2,
  l1 = [c_f1] /\
  l2 = [c_f2] /\
  (forall h, In h (get_signature_from_general p1) ->
    lookup_varlike_map (module_header_map c_f1) h
    = lookup_varlike_map (module_header_map c_f2) h).
Proof.
  intros p1 p2 input_len Hwf1 Hwf2 Hlc1 Hlc2 Hok1 Hok2 Hcheck
         s_i1 s_i2 c_i1 c_i2 f Hs1 Hs2 Hc1 Hc2 l1 l2 Hl1 Hl2.
  subst s_i1 s_i2 c_i1 c_i2.
  unfold modnet_header_equivalence_checker in Hcheck.
  destruct (eval_general_program_symbolic_sinks p1 (init_general_symbolic_state_n "p1" p1 input_len))
    as [[| [sym1 | ps1 | ps1] [| x1 xs1] ] |] eqn:Esym1; try discriminate Hcheck.
  destruct (eval_general_program_symbolic_sinks p2 (init_general_symbolic_state_n "p2" p2 input_len))
    as [[| [sym2 | ps2 | ps2] [| x2 xs2] ] |] eqn:Esym2; try discriminate Hcheck.
  destruct (smt_query (check_headers_and_state_vars sym1 sym2 (get_signature_from_general p1) []))
    eqn:Hq; try discriminate Hcheck.
  destruct (header_sink_agree_parser_source "p1" p1 input_len f sym1 Hok1 Esym1 l1 Hl1)
    as [cs1 [Hl1eq Hts1]].
  destruct (header_sink_agree_parser_source "p2" p2 input_len f sym2 Hok2 Esym2 l2 Hl2)
    as [cs2 [Hl2eq Hts2]].
  exists (TransformerMod cs1), (TransformerMod cs2).
  split; [exact Hl1eq | split; [exact Hl2eq |]].
  intros h Hh. cbn [module_header_map].
  pose proof (smt_query_sound_none _ Hq f) as Hqf.
  apply check_headers_and_state_vars_false in Hqf. destruct Hqf as [Hhdr _].
  specialize (Hhdr h Hh). apply smt_bool_eq_true in Hhdr.
  rewrite (ts_agree_hm cs1 sym1 f Hts1 h), (ts_agree_hm cs2 sym2 f Hts2 h).
  exact Hhdr.
Qed.

Print Assumptions modnet_header_equivalence_checker_sound_parser_source.

(* ------------------------------------------------------------------ *)
(* SMT bridge: decode the [modnet_neq_query] against [sb_concrete].      *)

Lemma smt_bit_neq_eval : forall a b f,
  eval_smt_bool (smt_bit_neq a b) f = xorb (eval_smt_bool a f) (eval_smt_bool b f).
Proof.
  intros a b f. cbn [smt_bit_neq eval_smt_bool].
  destruct (eval_smt_bool a f), (eval_smt_bool b f); reflexivity.
Qed.

(* Two output bitstreams have equal concretizations exactly when the query's
   [bitstreams_differ_v] is false at [f]. *)
Lemma bitstreams_differ_v_false : forall f out1 out2,
  eval_smt_bool (bitstreams_differ_v out1 out2) f = false ->
  sb_concrete out1 f = sb_concrete out2 f.
Proof.
  intros f out1. induction out1 as [|[b1 v1] r1 IH]; intros [|[b2 v2] r2] H;
    try reflexivity;
    try (cbn [bitstreams_differ_v] in H; cbn [eval_smt_bool] in H; discriminate H).
  cbn [bitstreams_differ_v] in H. cbn [eval_smt_bool] in H.
  apply Bool.orb_false_iff in H. destruct H as [Hhead Htail].
  cbn [sym_bit_differ] in Hhead. cbn [eval_smt_bool] in Hhead.
  apply Bool.orb_false_iff in Hhead. destruct Hhead as [Hv Hb].
  change (sb_concrete ((b1, v1) :: r1) f)
    with ((if eval_smt_bool v1 f then [eval_smt_bool b1 f] else []) ++ sb_concrete r1 f).
  change (sb_concrete ((b2, v2) :: r2) f)
    with ((if eval_smt_bool v2 f then [eval_smt_bool b2 f] else []) ++ sb_concrete r2 f).
  rewrite (IH r2 Htail).
  f_equal.
  (* head positions contribute equally: validities agree (Hv), and when both
     valid the bits agree (Hb). *)
  assert (Hveq : eval_smt_bool v1 f = eval_smt_bool v2 f).
  { change (SmtBoolOr (SmtBoolAnd v1 (SmtBoolNot v2)) (SmtBoolAnd (SmtBoolNot v1) v2))
      with (smt_bit_neq v1 v2) in Hv.
    rewrite smt_bit_neq_eval in Hv. apply Bool.xorb_eq in Hv. exact Hv. }
  rewrite <- Hveq. destruct (eval_smt_bool v1 f) eqn:Ev1; [| reflexivity].
  assert (Ev2 : eval_smt_bool v2 f = true) by congruence.
  change (SmtBoolOr (SmtBoolAnd b1 (SmtBoolNot b2)) (SmtBoolAnd (SmtBoolNot b1) b2))
    with (smt_bit_neq b1 b2) in Hb.
  rewrite smt_bit_neq_eval, Ev2 in Hb. cbn [andb] in Hb.
  apply Bool.xorb_eq in Hb. rewrite Hb. reflexivity.
Qed.

(* NOTE: the converse ([bitstreams_differ_v out1 out2] true -> concretizations
   differ) does NOT hold: when [out1]/[out2] have different STATIC lengths,
   [bitstreams_differ_v] returns [SmtTrue] ("always differ"), yet [sb_concrete]
   drops invalid padding, so e.g. [sb_concrete [(SmtTrue,SmtFalse)] f = [] =
   sb_concrete [] f] while [bitstreams_differ_v [(SmtTrue,SmtFalse)] [] = SmtTrue].
   Hence the completeness lemma below is UNPROVABLE as stated: the query over-
   approximates output-length differences, so a SAT model can be spurious.  This
   is a precision bug in [modnet_neq_query], not a missing proof — closing it
   requires making [bitstreams_differ_v] length-exact w.r.t. the [valid] channel. *)
(* Well-formedness bundle for the bitstream checker, analogous to
   [parser_source_ok] for the header checker: a [source parser -> transformer*
   -> deparser] linear chain, plus the (topology) condition that a successful
   concrete run's sinks are a single deparser.  Everything is what
   [refine_toplevel] (half 2) and [bitstream_lockstep_toplevel] (half 1) need. *)
Definition bitstream_ok (pre : String.string) (p : GeneralCaracaraProgram) (n : nat) : Prop :=
  let net := get_network_from_general p in
  let psrc := start_module net in
  let S := init_general_symbolic_state_n pre p n in
  no_fan_out net /\
  single_sink net /\
  (forall name m, lookup_module net name = Some m -> name <> psrc ->
     (exists nm2 s c t, m = TransformerModule nm2 s c t) \/
     (exists nm2 d, m = DeparserModule nm2 d)) /\
  (forall x, ~ In psrc (downstream_modules net x)) /\
  (exists nm pp, lookup_module net psrc = Some (ParserModule nm pp) /\
     (forall ss, (mod_states S) ?? (unwrap psrc) = Some ss ->
        exists ps, ss = ParserMod ps /\
                   extract_targets_in_dom pp (module_header_map ss) /\
                   hdr_writes_present net (module_header_map ss))) /\
  state_writes_present net S /\
  (forall f l, eval_general_program_concrete_sinks p (concretize_sym_modnet_state S f) = Some l ->
     exists ds, l = [DeparserMod ds]).

(* Bitstream-I/O soundness: for the same concrete input packet (the
   [f]-concretization of the shared symbolic bits), the two programs' output
   packets are identical.  Same shape as the header-map lemma, but the observable
   is the sink deparser's output packet ([p_packet]).  Adds a [bitstream_ok]
   bundle (mirroring the Gap A closure's [parser_source_ok]). *)
Lemma modnet_equivalence_checker_sound :
  forall p1 p2 n,
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  bitstream_ok "p1" p1 n ->
  bitstream_ok "p2" p2 n ->
  modnet_equivalence_checker p1 p2 n = Equivalent ->
  forall s_i1 s_i2 c_i1 c_i2 f,
  s_i1 = init_general_symbolic_state_n "p1" p1 n ->
  s_i2 = init_general_symbolic_state_n "p2" p2 n ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  exists ds1 ds2,
  l1 = [DeparserMod ds1] /\
  l2 = [DeparserMod ds2] /\
  p_packet ds1 = p_packet ds2.
Proof.
  intros p1 p2 n Hwf1 Hwf2 Hlc1 Hlc2 Hok1 Hok2 Hcheck
         s_i1 s_i2 c_i1 c_i2 f Hs1 Hs2 Hc1 Hc2 l1 l2 Hl1 Hl2.
  subst s_i1 s_i2 c_i1 c_i2.
  destruct Hok1 as [Hnf1 [Hss1 [Htd1 [Hnd1 [[nm1 [pp1 [Hlk1 Hps1]]] [Hsw1 Hdep1]]]]]].
  destruct Hok2 as [Hnf2 [Hss2 [Htd2 [Hnd2 [[nm2 [pp2 [Hlk2 Hps2]]] [Hsw2 Hdep2]]]]]].
  (* the concrete sinks are single deparsers *)
  destruct (Hdep1 f l1 Hl1) as [ds1 ->]. destruct (Hdep2 f l2 Hl2) as [ds2 ->].
  exists ds1, ds2. split; [reflexivity | split; [reflexivity |]].
  (* half 2: the concrete bitstream network output = p_packet ds_i *)
  pose proof (refine_toplevel p1 (concretize_sym_modnet_state (init_general_symbolic_state_n "p1" p1 n) f)
                ds1 Hnf1 Hss1 Hl1) as Hrt1.
  pose proof (refine_toplevel p2 (concretize_sym_modnet_state (init_general_symbolic_state_n "p2" p2 n) f)
                ds2 Hnf2 Hss2 Hl2) as Hrt2.
  (* half 1: the symbolic accept is true and the concrete output = sb_concrete os *)
  pose proof (bitstream_lockstep_toplevel p1 (init_general_symbolic_state_n "p1" p1 n) f
                nm1 pp1 [DeparserMod ds1] (p_packet ds1)
                Hnf1 Htd1 Hnd1 Hlk1 Hps1 Hsw1 Hrt1) as Hls1.
  pose proof (bitstream_lockstep_toplevel p2 (init_general_symbolic_state_n "p2" p2 n) f
                nm2 pp2 [DeparserMod ds2] (p_packet ds2)
                Hnf2 Htd2 Hnd2 Hlk2 Hps2 Hsw2 Hrt2) as Hls2.
  (* unfold the checker to expose the symbolic runs and the UNSAT query *)
  unfold modnet_equivalence_checker in Hcheck.
  destruct (eval_general_program_bitstream_acc p1 (init_general_symbolic_state_n "p1" p1 n))
    as [[[sinks1 a1] out1]|] eqn:Esym1; [| contradiction Hls1].
  destruct (eval_general_program_bitstream_acc p2 (init_general_symbolic_state_n "p2" p2 n))
    as [[[sinks2 a2] out2]|] eqn:Esym2; [| contradiction Hls2].
  destruct Hls1 as [Ha1 Ho1]. destruct Hls2 as [Ha2 Ho2].
  (* the checker matched single-deparser sinks *)
  destruct sinks1 as [| [t1|q1|d1] [|y1 ys1]]; try discriminate Hcheck.
  destruct sinks2 as [| [t2|q2|d2] [|y2 ys2]]; try discriminate Hcheck.
  destruct (smt_query (modnet_neq_query a1 a2 out1 out2)) eqn:Hq; try discriminate Hcheck.
  (* soundness of the solver: the query is false at f *)
  pose proof (smt_query_sound_none _ Hq f) as Hqf.
  cbn [modnet_neq_query eval_smt_bool] in Hqf.
  apply Bool.orb_false_iff in Hqf. destruct Hqf as [_ Hand].
  (* both accept, so the bitstream-difference disjunct forces agreement *)
  rewrite Ha1, Ha2 in Hand. cbn [andb] in Hand.
  pose proof (bitstreams_differ_v_false f out1 out2 Hand) as Hbeq.
  (* p_packet ds1 = sb_concrete out1 = sb_concrete out2 = p_packet ds2 *)
  rewrite Ho1, Ho2. exact Hbeq.
Qed.

(* COMPLETENESS DOES NOT HOLD, and it is not merely unproven — it is FALSE as
   stated, because [modnet_neq_query] / [bitstreams_differ_v] OVER-APPROXIMATE
   the real (sb_concrete) output difference.  We record this formally instead of
   leaving a false [Admitted] (which would be an inconsistency landmine):

   (1) Length over-approximation: a bitstream with a trailing INVALID position
       has the same [sb_concrete] as the shorter one, yet [bitstreams_differ_v]
       returns [SmtTrue] for the length mismatch. *)
Lemma modnet_neq_query_overapprox_length :
  exists (f : SmtValuation) out1 out2,
    eval_smt_bool (bitstreams_differ_v out1 out2) f = true /\
    sb_concrete out1 f = sb_concrete out2 f.
Proof.
  exists (fun _ => UninitVal), [(SmtTrue, SmtFalse)], (@nil SymBit).
  split; reflexivity.
Qed.

(* (2) Per-position over-approximation (even at EQUAL length): two positions
       with swapped validity but equal underlying bits give equal [sb_concrete]
       while [bitstreams_differ_v] fires on the validity mismatch. *)
Lemma modnet_neq_query_overapprox_validity :
  exists (f : SmtValuation) out1 out2,
    length out1 = length out2 /\
    eval_smt_bool (bitstreams_differ_v out1 out2) f = true /\
    sb_concrete out1 f = sb_concrete out2 f.
Proof.
  exists (fun _ => UninitVal),
         [(SmtTrue, SmtTrue); (SmtTrue, SmtFalse)],
         [(SmtTrue, SmtFalse); (SmtTrue, SmtTrue)].
  split; [reflexivity | split; reflexivity].
Qed.

(* Consequently a SAT model returned by [modnet_equivalence_checker] can be
   SPURIOUS: the checker may report [NotEquivalent] on programs whose concrete
   outputs actually coincide.  So the checker is SOUND (see above) but NOT
   COMPLETE.  Closing completeness requires making [bitstreams_differ_v]
   length- and validity-exact w.r.t. [sb_concrete] (a semantics change to the
   query), not just a proof — this is tracked as a precision gap in
   SOUNDNESS.md, related to Gap C. *)

Print Assumptions modnet_equivalence_checker_sound.
