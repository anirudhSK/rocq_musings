From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrModule.
From MyProject Require Import CrParser.
From MyProject Require Import CrVal.

(* Port of the spec that ParserHawk uses for icmp.  The three cases are the P4
   [select] in the docstring of both parse_icmp_accept_*_op.py, and they are
   ICMPv6 types 130..136 (MLD query/report/done, router solicit/advert,
   neighbor solicit/advert) as 2+4+1:

     16w0x8200 &&& 16w0xfe00   types 130..131
     16w0x8400 &&& 16w0xfc00   types 132..135
     16w0x8800 &&& 16w0xff00   type  136

   Take the masks from the _IPU_op.py encoding, NOT parse_icmp_accept_tofino_op.py:
   the tofino script's own encoded spec used 0xf800 on the third entry, which
   contradicts its docstring and over-matches types 137..143.
   https://github.com/ParserHawk/ParserHawk/blob/17be2c8a65a72dac59b2d33642a026d4ef9e90e3/z3/cegis_loop/one_short_revision/P4_examples/parse_icmp_accept/parse_icmp_accept_IPU_op.py#L75 *)
Definition icmp_spec_parser : Parser := {|
  parser_start := ParserStateLabelCtr 1;
  parser_states := [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 16 u16))
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 1) 9 16)
          [true; false; false; false; false; false; true] (* 0x8200 &&& 0xfe00 *)
          (TargetState (ParserStateLabelCtr 2));
        mkSelectCase (SelHdr (HeaderCtr 1) 10 16)
          [true; false; false; false; false; true]        (* 0x8400 &&& 0xfc00 *)
          (TargetState (ParserStateLabelCtr 2));
        mkSelectCase (SelHdr (HeaderCtr 1) 8 16)
          [true; false; false; false; true; false; false; false]
                                                          (* 0x8800 &&& 0xff00 *)
          (TargetState (ParserStateLabelCtr 2))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 1 u8))
      (Unconditional Accept)
  ];
|}.

(* https://github.com/ParserHawk/ParserHawk/blob/17be2c8a65a72dac59b2d33642a026d4ef9e90e3/z3/cegis_loop/one_short_revision/P4_examples/artifact_multiple_field_key/artifact_multiple_field_key_op.py#L77 *)
Definition mfk_spec_parser : Parser := {|
  parser_start := ParserStateLabelCtr 1;
  parser_states := [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u8))
      (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8 u8))
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 1) 0 8)
          [false; false; false; false; false; false; false; false]
          (TargetState (ParserStateLabelCtr 3))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 3)
      None
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 2) 0 8)
          [false; false; false; false; false; false; false; false]
          (TargetState (ParserStateLabelCtr 4))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 4)
      (Some (ExtractOpConstructor (HeaderCtr 3) 1 u8))
      (Unconditional Accept)
  ];
|}.


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
        mkSelectCase (SelHdr (HeaderCtr 2) 0 16)
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false; false; false; false] (* 0x0800 *)
          (TargetState (ParserStateLabelCtr 3));
        mkSelectCase (SelHdr (HeaderCtr 2) 0 16)
          [ true; false; false; false; false;  true;  true; false;
            true;  true; false;  true;  true;  true; false;  true] (* 0x86dd *)
          (TargetState (ParserStateLabelCtr 4));
        mkSelectCase (SelHdr (HeaderCtr 2) 0 16)
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false;  true;  true; false] (* 0x0806 *)
          (TargetState (ParserStateLabelCtr 5))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 3)
      (Some (ExtractOpConstructor (HeaderCtr 3) 8 u8))
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 3) 0 8)
          [false; false; false; false; false;  true; false; false] (* 0x04 *)
          (TargetState (ParserStateLabelCtr 6));
        mkSelectCase (SelHdr (HeaderCtr 3) 0 8)
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (SelHdr (HeaderCtr 3) 0 8)
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (SelHdr (HeaderCtr 3) 0 8)
          [false; false; false; false; false; false; false;  true] (* 0x01 *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 4)
      (Some (ExtractOpConstructor (HeaderCtr 4) 8 u8))
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 4) 0 8)
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (SelHdr (HeaderCtr 4) 0 8)
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (SelHdr (HeaderCtr 4) 0 8)
          [false; false;  true;  true;  true; false;  true; false] (* 0x3a *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 5)
      (Some (ExtractOpConstructor (HeaderCtr 9) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 6)
      (Some (ExtractOpConstructor (HeaderCtr 5) 8 u8))
      (Select [
        mkSelectCase (SelHdr (HeaderCtr 5) 0 8)
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (SelHdr (HeaderCtr 5) 0 8)
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (SelHdr (HeaderCtr 5) 0 8)
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
| ICMPHdr (h1 : Header) (h2 : Header)
| EthHdr (h1 : Header) (h2 : Header)
| SAIHdr
  (h1 : Header) (h2 : Header) (h3 : Header)
  (h4 : Header) (h5 : Header) (h6 : Header)
  (h7 : Header) (h8 : Header) (h9 : Header)
| MultiFieldHdr (h1 : Header) (h2 : Header) (h3 : Header).

Definition dump_headers (p : Parser) (ordering : ParserHawkHdrs) : GeneralCaracaraProgram :=
  match ordering with
  | ICMPHdr h1 h2 =>
    GeneralCaracaraProgramDef 17 [] {|
      net_modules := [
        ParserModule (ModuleNameCtr 1) p;
        DeparserModule (ModuleNameCtr 2) (mkDeparser [
          EmitOpConstructor h1 16;
          EmitOpConstructor h2 8
        ])
      ];
      net_edges := fun a b => 
        match a, b with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end;
      start_module := ModuleNameCtr 1;
    |}
  | EthHdr h1 h2 =>
    GeneralCaracaraProgramDef 17 [] {|
      net_modules := [
        ParserModule (ModuleNameCtr 1) p;
        DeparserModule (ModuleNameCtr 2) (mkDeparser [
          EmitOpConstructor h1 16;
          EmitOpConstructor h2 1
        ])
      ];
      net_edges := fun a b => 
        match a, b with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end;
      start_module := ModuleNameCtr 1;
    |}
  | MultiFieldHdr h1 h2 h3 =>
    GeneralCaracaraProgramDef 17 [] {|
      net_modules := [
        ParserModule (ModuleNameCtr 1) p;
        DeparserModule (ModuleNameCtr 2) (mkDeparser [
          EmitOpConstructor h1 8;
          EmitOpConstructor h2 8;
          EmitOpConstructor h3 1
        ])
      ];
      net_edges := fun a b =>
        match a, b with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end;
      start_module := ModuleNameCtr 1;
    |}
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

Definition icmp_spec :=
  dump_headers icmp_spec_parser (ICMPHdr (HeaderCtr 1) (HeaderCtr 2)).

Definition mfk_spec :=
  dump_headers mfk_spec_parser (MultiFieldHdr (HeaderCtr 1) (HeaderCtr 2) (HeaderCtr 3)).

Definition sai_spec :=
  dump_headers sai_spec_parser (SAIHdr
    (HeaderCtr 1) (HeaderCtr 2) (HeaderCtr 3)
    (HeaderCtr 4) (HeaderCtr 5) (HeaderCtr 6)
    (HeaderCtr 7) (HeaderCtr 8) (HeaderCtr 9)).
