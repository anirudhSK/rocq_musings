From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrParser.
From MyProject Require Import CrIdentifiers.
From Stdlib Require Import ZArith.

(* 8-bit MSB-first select patterns (compared against a header's whole value). *)
Definition pat_0   : list bool := [false;false;false;false;false;false;false;false].
Definition pat_1   : list bool := [false;false;false;false;false;false;false;true].
Definition pat_255 : list bool := [true;true;true;true;true;true;true;true].

(* 1. Single extraction: read one byte into h1, then Accept. *)
Definition p_extract8 : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional Accept)
  ].

(* 2. Two sequential extractions: byte 0 -> h1, byte 1 -> h2, then Accept. *)
Definition p_extract_two : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ].

(* 3. Conditional extraction via [select]: extract h1; if h1 = 1, extract a
   second byte into h2, otherwise Accept without touching h2. *)
Definition p_select_extract : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_1 (TargetState (ParserStateLabelCtr 2))]
              Accept);
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ].

(* 4. Looping parser (P4 header-stack style): keep extracting a byte into h1
   until a 0 terminator, then extract one payload byte into h2 and Accept.
   Exercises state revisiting, which needs the |states|*(|packet|+1) fuel. *)
Definition p_loop : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_0 (TargetState (ParserStateLabelCtr 2))]
              (TargetState (ParserStateLabelCtr 1)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 8))
      (Unconditional Accept)
  ].

(* 5. Explicit reject: extract h1; if h1 = 255 Reject (the parse fails),
   otherwise Accept. *)
Definition p_reject : Parser :=
  mkParser (ParserStateLabelCtr 1) [
    mkParserStateDef (ParserStateLabelCtr 1)
      (Some (ExtractOpConstructor (HeaderCtr 1) 8))
      (Select [mkSelectCase (HeaderCtr 1) 0 8 pat_255 Reject]
              Accept)
  ].

Definition parser_test_programs : list Parser :=
  [ p_extract8; p_extract_two; p_select_extract; p_loop; p_reject ].
