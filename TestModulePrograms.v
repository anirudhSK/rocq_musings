From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.

From MyProject Require Import CrDsl.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrModule.
From MyProject Require Import Integers.

(* Single-module: unconditionally adds 3 to h1.
   h1=5 → h1=8. *)
Definition mod_prog_single_add3 : GeneralCaracaraProgram :=
  let p := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp
        (HeaderArg (HeaderCtr 1))
        (ConstantArg (CrUInt8 (repr 3)))
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
      StatelessOp AddOp
        (HeaderArg (HeaderCtr 1))
        (ConstantArg (CrUInt8 (repr 1)))
        (HeaderCtr 1)
    ])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp MulOp
        (HeaderArg (HeaderCtr 1))
        (ConstantArg (CrUInt8 (repr 2)))
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
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrUInt8 (repr 7)))] [
      StatelessOp AddOp
        (ConstantArg (CrUInt8 (repr 1)))
        (ConstantArg (CrUInt8 (repr 0)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp
        (HeaderArg (HeaderCtr 1))
        (ConstantArg (CrUInt8 (repr 10)))
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
      StatelessOp AddOp
        (HeaderArg (HeaderCtr 1))
        (HeaderArg (HeaderCtr 2))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ] in
  let p2 := CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp
        (HeaderArg (HeaderCtr 1))
        (ConstantArg (CrUInt8 (repr 1)))
        (HeaderCtr 1)
    ])
  ] in
  let net := empty_net in
  let '(net, m1) := add_program_to_network net p1 in
  let '(net, m2) := add_program_to_network net p2 in
  let net := add_connection_to_network net m1 m2 in
  let net := set_start_module net m1 in
  GeneralCaracaraProgramDef [HeaderCtr 1; HeaderCtr 2] net [HeaderCtr 1].

Definition mod_test_programs : list GeneralCaracaraProgram := [
  mod_prog_single_add3;
  mod_prog_add1_then_mul2;
  mod_prog_conditional_pipeline;
  mod_prog_cmplt_matchheader
].
