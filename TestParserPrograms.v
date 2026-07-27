From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrParser.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* 8-bit MSB-first select patterns (compared against a header's whole value). *)
Definition pat_0   : list bool := [false;false;false;false;false;false;false;false].
Definition pat_1   : list bool := [false;false;false;false;false;false;false;true].
Definition pat_255 : list bool := [true;true;true;true;true;true;true;true].

(* 1. Single extraction: read one byte into h1, then Accept. *)
Definition p_extract8 : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Unconditional Accept)
  ].

(* 2. Two sequential extractions: byte 0 -> h1, byte 1 -> h2, then Accept. *)
Definition p_extract_two : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8 u64))
      (Unconditional Accept)
  ].

(* 3. Conditional extraction via [select]: extract h1; if h1 = 1, extract a
   second byte into h2, otherwise Accept without touching h2. *)
Definition p_select_extract : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_1 (TargetState (ParserStateLabelCtr 2))]
              Accept);
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8 u64))
      (Unconditional Accept)
  ].

(* 4. Looping parser (P4 header-stack style): keep extracting a byte into h1
   until a 0 terminator, then extract one payload byte into h2 and Accept.
   Exercises state revisiting, which needs the |states|*(|packet|+1) fuel. *)
Definition p_loop : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_0 (TargetState (ParserStateLabelCtr 2))]
              (TargetState (ParserStateLabelCtr 1)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8 u64))
      (Unconditional Accept)
  ].

(* 5. Explicit reject: extract h1; if h1 = 255 Reject (the parse fails),
   otherwise Accept. *)
Definition p_reject : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_255 Reject]
              Accept)
  ].

(* 6. Sub-field select: extract one byte into h1, then branch on its *high
   nibble* (bits [4,8), LSB-indexed).  If the high nibble is 3, extract a
   second byte into h2; otherwise Accept.  This is a genuine non-[0,end) slice,
   so the low nibble must not affect the decision. *)
Definition pat_nib3 : list bool := [false; false; true; true].  (* denotes 3 *)

Definition p_select_nibble : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
      (Select [mkSelectCase (HeaderCtr 1) 4 8 pat_nib3 (TargetState (ParserStateLabelCtr 2))]
              Accept);
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8 u64))
      (Unconditional Accept)
  ].

Definition parser_test_programs : list Parser :=
  [ p_extract8; p_extract_two; p_select_extract; p_loop; p_reject;
    p_select_nibble ].

(* ------------------------------------------------------------------ *)
(* Concrete checks for the sub-field select.  We observe [p_cursor]: it lands
   on 16 iff the second byte was extracted (i.e. the high-nibble match fired),
   and on 8 iff the parser Accepted after one byte. *)

Definition mk_cps (bits : list bool) : ConcreteParserState :=
  {| p_header_map := PMap.init UninitVal; p_packet := bits; p_cursor := 0 |}.

Definition run_cursor (p : Parser) (bits : list bool) : option nat :=
  option_map p_cursor (eval_parser_concrete p (mk_cps bits)).

(* MSB-first bits of one byte. *)
Definition byte (b7 b6 b5 b4 b3 b2 b1 b0 : bool) : list bool :=
  [b7; b6; b5; b4; b3; b2; b1; b0].
Definition byte_FF : list bool := byte true true true true true true true true.

(* 0x35: high nibble 3, low nibble 5 -> match fires -> second byte consumed. *)
Example nibble_match_35 :
  run_cursor p_select_nibble (byte false false true true false true false true ++ byte_FF)
  = Some 16.
Proof. reflexivity. Qed.

(* 0x3A = 58: whole value <> 3 but high nibble = 3 -> match still fires.  This
   is exactly the case the old whole-value compare mishandled. *)
Example nibble_match_3A :
  run_cursor p_select_nibble (byte false false true true true false true false ++ byte_FF)
  = Some 16.
Proof. reflexivity. Qed.

(* 0x45: high nibble 4 (low nibble 5, same as 0x35) -> match fails -> Accept. *)
Example nibble_nomatch_45 :
  run_cursor p_select_nibble (byte false true false false false true false true ++ byte_FF)
  = Some 8.
Proof. reflexivity. Qed.
