From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.

From MyProject Require Import CrDsl.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import Integers.

(* Unconditionally subtracts 2 from h1. *)
Definition prog_sub2_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp SubOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 2)))
        (HeaderCtr 1)
    ])
  ].

(* Subtracts 5 from h1 only when h1 = 0.
 * Used to test that a predicate mismatch leaves the state unchanged. *)
Definition prog_sub5_h1_if_h1eq0 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 0)))] [
      StatelessOp SubOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 5)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ].

(* Adds 3 to h1 when h1 = 5. *)
Definition prog_add3_h1_if_h1eq5 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 5)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 3)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ].

(* Two rules, both matching h1 = 5.
 * Tests that only the first matching rule fires (first-match semantics).
 * Rule 1: h1 += 1. Rule 2: h1 += 10. *)
Definition prog_first_match_h1eq5 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 5)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 1)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 5)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 10)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ].

(* StatefulOp: writes h1 - 2 into state variable s1, leaving h1 unchanged. *)
Definition prog_stateful_sub2_s1_from_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [StateCtr 1] [] [
    Seq (SeqCtr [] [
      StatefulOp SubOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 2)))
        (StateCtr 1)
    ])
  ].

(* Uses a ctrl-plane variable as an operand: h1 := h1 + ctrl1. *)
Definition prog_add_ctrl1_to_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [CtrlCtr 1] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpCtrlPlane (CtrlCtr 1))
        (HeaderCtr 1)
    ])
  ].

(* Action list [h1 += 1 ; h1 *= 2] with fold_left evaluation order:
 * the head of the list (h1 += 1) executes first, then h1 *= 2.
 * Starting from h1 = 10: 10 + 1 = 11, then 11 * 2 = 22. *)
Definition prog_fold_left_order : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 1)))
        (HeaderCtr 1);
      StatelessOp MulOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 2)))
        (HeaderCtr 1)
    ])
  ].

(* SubOp with underflow: exercises uint8 modular arithmetic.
 * h1 := h1 - 5. With h1 = 2: (2 - 5) mod 256 = 253. *)
Definition prog_sub_underflow_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp SubOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 5)))
        (HeaderCtr 1)
    ])
  ].

(* AddOp with overflow: exercises uint8 modular arithmetic.
 * h1 := h1 + 10. With h1 = 250: (250 + 10) mod 256 = 4. *)
Definition prog_add_overflow_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 10)))
        (HeaderCtr 1)
    ])
  ].

(* Bitwise AND mask: h1 := h1 AND 0x0F. With h1 = 0xAB (171): 0x0B (11). *)
Definition prog_and_mask_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp AndOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 15)))
        (HeaderCtr 1)
    ])
  ].

(* Bitwise OR: h1 := h1 OR 0xF0. With h1 = 0x05 (5): 0xF5 (245). *)
Definition prog_or_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp OrOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 240)))
        (HeaderCtr 1)
    ])
  ].

(* Bitwise XOR (invert via XOR with 0xFF):
 * h1 := h1 XOR 0xFF. With h1 = 0x55 (85): 0xAA (170). *)
Definition prog_xor_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp XorOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 255)))
        (HeaderCtr 1)
    ])
  ].

(* MulOp: h1 := h1 * 7. With h1 = 3: 21. *)
Definition prog_mul_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp MulOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 7)))
        (HeaderCtr 1)
    ])
  ].

(* DivOp (unsigned division): h1 := h1 / 3. With h1 = 10: 3. *)
Definition prog_div_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp DivOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 3)))
        (HeaderCtr 1)
    ])
  ].

(* ModOp (unsigned modulo): h1 := h1 mod 7. With h1 = 23: 2. *)
Definition prog_mod_h1 : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [] [
      StatelessOp ModOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 7)))
        (HeaderCtr 1)
    ])
  ].

(* OpStateful as operand: read from state variable as an input.
 * h1 := h1 + s1. With h1 = 3 and s1 = 4: h1 = 7. *)
Definition prog_stateful_arg_input : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [StateCtr 1] [] [
    Seq (SeqCtr [] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpStateful (StateCtr 1))
        (HeaderCtr 1)
    ])
  ].

(* Multi-rule transformer where the first rule does not match but the second does.
 * Rule 1: pattern h1 = 5, action h1 += 1.
 * Rule 2: pattern h1 = 10, action h1 += 100.
 * With h1 = 10, only rule 2 fires (find_first_match returns rule 2): h1 = 110. *)
Definition prog_multi_rule_second_matches : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 5)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 1)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 10)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 100)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ].

(* Cross-header predicate: predicate reads h2; action writes h1.
 * When h2 = 7, h1 := h1 + 1. With h1 = 5 and h2 = 7: h1 = 6, h2 unchanged. *)
Definition prog_cross_header_predicate : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1; HeaderCtr 2] [] [] [
    Seq (SeqCtr [(HeaderCtr 2, CmpEq, MatchConst (CrInt (repr 7)))] [
      StatelessOp AddOp u8
        (OpHeader (HeaderCtr 1))
        (OpConst (CrInt (repr 1)))
        (HeaderCtr 1)
    ]);
    Seq (SeqCtr [] [])
  ].

(* Empty transformer: no rules. State is left unchanged. *)
Definition prog_empty_transformer : CaracaraProgram :=
  CaracaraProgramDef [HeaderCtr 1] [] [] [Seq (SeqCtr [] [])].

Definition test_programs := [
  prog_sub2_h1;
  prog_sub5_h1_if_h1eq0;
  prog_add3_h1_if_h1eq5;
  prog_first_match_h1eq5;
  prog_stateful_sub2_s1_from_h1;
  prog_add_ctrl1_to_h1;
  prog_fold_left_order;
  prog_sub_underflow_h1;
  prog_add_overflow_h1;
  prog_and_mask_h1;
  prog_or_h1;
  prog_xor_h1;
  prog_mul_h1;
  prog_div_h1;
  prog_mod_h1;
  prog_stateful_arg_input;
  prog_multi_rule_second_matches;
  prog_cross_header_predicate;
  prog_empty_transformer
].
