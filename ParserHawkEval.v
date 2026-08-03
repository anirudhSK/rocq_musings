From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrModule.
From MyProject Require Import CrParser.
From MyProject Require Import CrVal.

(* Port of the spec that ParserHawk uses for sai:
   https://github.com/ParserHawk/ParserHawk/blob/17be2c8a65a72dac59b2d33642a026d4ef9e90e3/z3/cegis_loop/one_short_revision/P4_examples/sai_v4_pkt_eth_v46_inv4_udp_tcp_icmp_arp/sai_v4_pkt_eth_v46_inv4_udp_tcp_icmp_arp_tofino_op.py#L165 *)
Definition sai_spec_parser : Parser := {|
  parser_start := ParserStateLabelCtr 1;
  parser_states := [
    mkParserStateDef (ParserStateLabelCtr 1)
        (Some (ExtractOpConstructor (HeaderCtr 1) 1 u8))
        (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 16 u16))
      (Select [
        mkSelectCase (HeaderCtr 2) 0 16
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false; false; false; false] (* 0x0800 *)
          (TargetState (ParserStateLabelCtr 3));
        mkSelectCase (HeaderCtr 2) 0 16
          [ true; false; false; false; false;  true;  true; false;
            true;  true; false;  true;  true;  true; false;  true] (* 0x86dd *)
          (TargetState (ParserStateLabelCtr 4));
        mkSelectCase (HeaderCtr 2) 0 16
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false;  true;  true; false] (* 0x0806 *)
          (TargetState (ParserStateLabelCtr 5))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 3)
      (Some (ExtractOpConstructor (HeaderCtr 3) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false;  true; false; false] (* 0x04 *)
          (TargetState (ParserStateLabelCtr 6));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false; false; false;  true] (* 0x01 *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 4)
      (Some (ExtractOpConstructor (HeaderCtr 4) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false;  true;  true;  true; false;  true; false] (* 0x3a *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 5)
      (Some (ExtractOpConstructor (HeaderCtr 9) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 6)
      (Some (ExtractOpConstructor (HeaderCtr 5) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false; false; false; false; false;  true] (* 0x01 *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 7)
      (Some (ExtractOpConstructor (HeaderCtr 6) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 8)
      (Some (ExtractOpConstructor (HeaderCtr 7) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 9)
      (Some (ExtractOpConstructor (HeaderCtr 8) 1 u8))
      (Unconditional Accept)
  ];
|}.

Inductive ParserHawkHdrs :=
| SAIHdr
  (h1 : Header) (h2 : Header) (h3 : Header)
  (h4 : Header) (h5 : Header) (h6 : Header)
  (h7 : Header) (h8 : Header) (h9 : Header).
Definition sai_dump_headers (p : Parser) (ordering : ParserHawkHdrs) : GeneralCaracaraProgram :=
  match ordering with
  | SAIHdr h1 h2 h3 h4 h5 h6 h7 h8 h9 =>
    GeneralCaracaraProgramDef 34 [] {|
      net_modules := [
        ParserModule (ModuleNameCtr 1) p;
        DeparserModule (ModuleNameCtr 2) (mkDeparser [
          EmitOpConstructor h1 1;
          EmitOpConstructor h2 16;
          EmitOpConstructor h3 8;
          EmitOpConstructor h4 8;
          EmitOpConstructor h5 8;
          EmitOpConstructor h6 1;
          EmitOpConstructor h7 1;
          EmitOpConstructor h8 1;
          EmitOpConstructor h9 1
        ])
      ];
      net_edges := fun a b => 
        match a, b with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end;
      start_module := ModuleNameCtr 1;
    |}
  end.

(* dumps 9 header fields next to one another *)
Definition sai_spec :=
  sai_dump_headers sai_spec_parser (SAIHdr
    (HeaderCtr 1) (HeaderCtr 2) (HeaderCtr 3)
    (HeaderCtr 4) (HeaderCtr 5) (HeaderCtr 6)
    (HeaderCtr 7) (HeaderCtr 8) (HeaderCtr 9)).
