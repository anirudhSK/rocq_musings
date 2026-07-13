From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.

From MyProject Require Import CrDsl.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrModule.
From MyProject Require Import CrParser.
From MyProject Require Import CrDeparser.
From MyProject Require Import Integers.

(* Single-module: unconditionally adds 3 to h1.
   h1=5 → h1=8. *)
Definition mod_prog_single_add3 : GeneralCaracaraProgram :=
  let p := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (repr 3))
        (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_program_to_network net p in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [HeaderCtr 1] net [HeaderCtr 1].

(* Two-module pipeline: module 1 adds 1, module 2 multiplies by 2.
   h1=5 → (5+1)*2 = 12. *)
Definition mod_prog_add1_then_mul2 : GeneralCaracaraProgram :=
  let p1 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (repr 1))
        (HeaderCtr 1)
    ])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp MulOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (repr 2))
        (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_program_to_network net p1 in
  let '(net, m2) := add_program_to_network net p2 in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [HeaderCtr 1] net [HeaderCtr 1].

(* Two-module pipeline with conditional in the first module.
   Module 1: if h1 = 7 then h1 := 1 (no-op otherwise).
   Module 2: h1 := h1 + 10.
   h1=7 → 1 → 11.  h1=3 → 3 → 13. *)
Definition mod_prog_conditional_pipeline : GeneralCaracaraProgram :=
  let p1 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (repr 7) u8)] [
      StatelessOp AddOp u8
        (OpConst (repr 1))
        (OpConst (repr 0))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (repr 10))
        (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_program_to_network net p1 in
  let '(net, m2) := add_program_to_network net p2 in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [HeaderCtr 1] net [HeaderCtr 1].

(* Two-module pipeline exercising CmpLt with MatchHeader.
   Module 1: if h1 < h2 then h1 := h1 + h2.
   Module 2: h1 := h1 + 1.
   h1=3, h2=5 → 3<5 fires → h1=8 → h1=9.
   h1=5, h2=3 → no match  → h1=5 → h1=6. *)
Definition mod_prog_cmplt_matchheader : GeneralCaracaraProgram :=
  let p1 := CaracaraProgramDef [HeaderCtr 1; HeaderCtr 2] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpLt, MatchHeader (HeaderCtr 2))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpHeader (HeaderCtr 2))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (repr 1))
        (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_program_to_network net p1 in
  let '(net, m2) := add_program_to_network net p2 in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [HeaderCtr 1; HeaderCtr 2] net [HeaderCtr 1].

(* Parser module feeding a transformer module: the parser extracts one byte
   into h1; the transformer then adds 5.  With a packet byte 10: h1 = 10 -> 15. *)
Definition mod_prog_parser_then_transformer : GeneralCaracaraProgram :=
  let parser := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional Accept)
  ] in
  (* parsed fields are typed u64 (see apply_extract_concrete), so the
     transformer op reads h1 at u64 too. *)
  let t := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u64
        (OpHeader (HeaderCtr 1)) (OpConst (repr 5)) (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser in
  let '(net, m2) := add_program_to_network net t in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1].

(* Two parser modules in a pipeline: parser 1 extracts a byte into h1, parser 2
   extracts a byte (from its own packet) into h2, carrying h1 forward. *)
Definition mod_prog_two_parsers : GeneralCaracaraProgram :=
  let parser1 := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional Accept)
  ] in
  let parser2 := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser1 in
  let '(net, m2) := add_parser_to_network net parser2 in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1; HeaderCtr 2].

(* Bitstream I/O pipeline: a parser extracts two bytes into h1, h2; a deparser
   re-emits h1, h2 (prepending them to any residual payload).  This is the
   inverse-pair pipeline used to exercise the bitstream [modnet_equivalence_checker]:
   parse-then-deparse reproduces the input packet, so the pipeline is
   equivalent to itself over any input bitstream. *)
Definition mod_prog_parse_deparse : GeneralCaracaraProgram :=
  let parser := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ] in
  let deparser := mkDeparser [ EmitOpConstructor (HeaderCtr 1) 8;
                               EmitOpConstructor (HeaderCtr 2) 8 ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser in
  let '(net, m2) := add_deparser_to_network net deparser in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1; HeaderCtr 2].

(* Same parser, but the deparser emits the two headers in swapped order.  This
   pipeline is NOT equivalent to [mod_prog_parse_deparse]: on any input whose two
   bytes differ, the emitted output packets differ. *)
Definition mod_prog_parse_deparse_swapped : GeneralCaracaraProgram :=
  let parser := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ] in
  let deparser := mkDeparser [ EmitOpConstructor (HeaderCtr 2) 8;
                               EmitOpConstructor (HeaderCtr 1) 8 ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser in
  let '(net, m2) := add_deparser_to_network net deparser in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1; HeaderCtr 2].

(* Bitstream pipeline whose parser REJECTS the one-byte packet 0xFF (via a
   [select] case) and otherwise accepts, extracting the byte into h1; a deparser
   re-emits h1.  Paired with [mod_prog_parse_accept_deparse] below (identical but
   always-accepting) to exercise accept/reject handling in the bitstream
   [modnet_equivalence_checker]: the two agree on every packet except 0xFF, where
   one rejects and the other accepts.  The old swallow-the-reject symbolic
   semantics wrongly called them equivalent. *)
Definition mod_prog_parse_reject_deparse : GeneralCaracaraProgram :=
  let parser := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Select [mkSelectCase (HeaderCtr 1) 0 8
                 [true;true;true;true;true;true;true;true] Reject]
              Accept)
  ] in
  let deparser := mkDeparser [ EmitOpConstructor (HeaderCtr 1) 8 ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser in
  let '(net, m2) := add_deparser_to_network net deparser in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1].

(* Always-accepting counterpart of [mod_prog_parse_reject_deparse]. *)
Definition mod_prog_parse_accept_deparse : GeneralCaracaraProgram :=
  let parser := mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional Accept)
  ] in
  let deparser := mkDeparser [ EmitOpConstructor (HeaderCtr 1) 8 ] in
  let net := empty_net in
  let '(net, m1) := add_parser_to_network net parser in
  let '(net, m2) := add_deparser_to_network net deparser in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [] net [HeaderCtr 1].

Definition mod_test_programs : list GeneralCaracaraProgram := [
  mod_prog_single_add3;
  mod_prog_add1_then_mul2;
  mod_prog_conditional_pipeline;
  mod_prog_cmplt_matchheader;
  mod_prog_parser_then_transformer;
  mod_prog_two_parsers;
  mod_prog_parse_deparse;
  mod_prog_parse_deparse_swapped
].
