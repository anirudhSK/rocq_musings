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
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import ModnetHeaderLemmas.
From MyProject Require Import ModnetParserSourceLemmas.
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
   [valid] channel and merged across [select] branches ([eval_parser_residual]),
   so the data-dependent consumed length is represented exactly rather than by a
   single cursor — the deparser then prepends its emitted bits ahead of it.

   REMAINING CAVEATS: (1) a parser that reads a *data-dependent* residual
   produced by an upstream parser is approximate — [eval_module_bitstream_acc]
   drops the incoming validity ([List.map fst]) when feeding a parser, which is
   exact only for an all-valid source packet (single source parser feeding
   transformers/deparsers).  (2) On a fan-out DAG the sink's bitstream is taken
   from the last path explored; the intended topology is a linear chain
   ([is_linear_chain]).  The [Admitted] lemmas below do not close these. *)
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
(* Bitstream-I/O soundness / completeness.  Same shape as the header-map  *)
(* lemmas, but the observable is the sink deparser's output packet         *)
(* ([p_packet]) rather than a header map: for the same concrete input      *)
(* packet (the [f]-concretization of the shared symbolic bits), the two    *)
(* programs' output packets agree (soundness) or differ (completeness). *)
Lemma modnet_equivalence_checker_sound :
  forall p1 p2 n,
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  modnet_equivalence_checker p1 p2 n = Equivalent ->
  forall s_i1 s_i2 c_i1 c_i2 f,
  s_i1 = init_general_symbolic_state_n "p1" p1 n ->
  s_i2 = init_general_symbolic_state_n "p2" p2 n ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* each program's single sink is a deparser, and the emitted output
     bitstreams are identical *)
  exists ds1 ds2,
  l1 = [DeparserMod ds1] /\
  l2 = [DeparserMod ds2] /\
  p_packet ds1 = p_packet ds2.
Proof.
Admitted.

Lemma modnet_equivalence_checker_complete :
  forall p1 p2 n f,
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  modnet_equivalence_checker p1 p2 n = NotEquivalent f ->
  forall s_i1 s_i2 c_i1 c_i2,
  s_i1 = init_general_symbolic_state_n "p1" p1 n ->
  s_i2 = init_general_symbolic_state_n "p2" p2 n ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* each program's single sink is a deparser, and the emitted output
     bitstreams differ (on the input packet witnessed by [f]) *)
  exists ds1 ds2,
  l1 = [DeparserMod ds1] /\
  l2 = [DeparserMod ds2] /\
  p_packet ds1 <> p_packet ds2.
Proof.
Admitted.

Print Assumptions modnet_equivalence_checker_sound.
Print Assumptions modnet_equivalence_checker_complete.
