From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrConcreteSemanticsDeparser.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import TestParserPrograms.

(* A deparser that re-serializes two 8-bit headers h1, h2 in order — the
   inverse of [p_extract_two], which parses byte 0 into h1 and byte 1 into h2. *)
Definition d_two : Deparser :=
  mkDeparser [ EmitOpConstructor (HeaderCtr 1) 8;
               EmitOpConstructor (HeaderCtr 2) 8 ].

(* A concrete two-byte packet: 0x35, 0xAB. *)
Definition rt_packet : list bool :=
  byte false false true true false true false true      (* 0x35 *)
  ++ byte true false true false true false true true.   (* 0xAB *)

(* ------------------------------------------------------------------ *)
(* Direct check: emitting from a header map holding h1=0x35, h2=0xAB    *)
(* produces exactly those 16 bits (MSB-first), prepended to the (empty) *)
(* payload. *)
Definition hdrs_35_AB : PMap.t CrVal :=
  PMap.set 2 (mk_int u64 171)      (* 0xAB *)
    (PMap.set 1 (mk_int u64 53)    (* 0x35 *)
      (PMap.init UninitVal)).

Example emit_two_bytes :
  p_packet (eval_deparser_concrete d_two
    {| p_header_map := hdrs_35_AB; p_packet := []; p_cursor := 0 |}) = rt_packet.
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Round-trip: parse a packet into headers, then deparse those headers, *)
(* and recover the original packet.  This is the defining property of a  *)
(* deparser as the parser's inverse. *)
Definition deparse_after_parse (pkt : list bool) : option (list bool) :=
  match eval_parser_concrete p_extract_two (mk_cps pkt) with
  | None => None
  | Some ps =>
      Some (p_packet (eval_deparser_concrete d_two
              {| p_header_map := p_header_map ps;
                 p_packet     := skipn (p_cursor ps) (p_packet ps);  (* residual payload *)
                 p_cursor     := 0 |}))
  end.

Example deparser_roundtrip : deparse_after_parse rt_packet = Some rt_packet.
Proof. reflexivity. Qed.

(* A three-byte packet (extra payload byte 0xFF) still round-trips: the two
   parsed header bytes are re-emitted ahead of the untouched payload. *)
Example deparser_roundtrip_with_payload :
  deparse_after_parse (rt_packet ++ byte_FF) = Some (rt_packet ++ byte_FF).
Proof. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* End-to-end through the module network: a parser module feeding a      *)
(* deparser module.  Running the network on [rt_packet] must reconstruct  *)
(* [rt_packet] at the deparser sink. *)
Definition rt_headers : list Header := [HeaderCtr 1; HeaderCtr 2].

Definition parse_deparse_net : GeneralCaracaraProgram :=
  let net0 := empty_net in
  let '(net1, pid) := add_parser_to_network net0 p_extract_two in
  let '(net2, did) := add_deparser_to_network net1 d_two in
  let net3 := add_connection_to_network net2 pid did in
  let net4 := set_start_module net3 pid in
  GeneralCaracaraProgramDef rt_headers net4 rt_headers.

(* Feed [rt_packet] into the shared bit channel, run, and read the sink's
   emitted packet. *)
Definition run_net (pkt : list bool) : option (list bool) :=
  let gs0 := init_general_concrete_state parse_deparse_net in
  let gs1 := set_gps_shared_bits gs0 pkt in
  match eval_general_program_concrete_sinks parse_deparse_net gs1 with
  | Some [DeparserMod ds] => Some (p_packet ds)
  | _ => None
  end.

Example network_roundtrip : run_net rt_packet = Some rt_packet.
Proof. vm_compute. reflexivity. Qed.
