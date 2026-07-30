(* ================================================================= *)
(* P4-style packet deparser.                                         *)
(*                                                                   *)
(* A deparser is the inverse of a parser: where a parser reads a run *)
(* of bits off the incoming packet into a header, a deparser reads a *)
(* header value and writes (emits) a run of bits back onto the       *)
(* outgoing packet.  It is a straight-line sequence of [emit]s (no   *)
(* FSM / loops), so no fuel is needed.                               *)
(* ================================================================= *)
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.
From MyProject Require Import CrIdentifiers.

(* ------------------------------------------------------------------ *)
(* Emit: write the low [width] bits of header [eo_header] onto the      *)
(* outgoing packet (MSB-first, the same wire order [CrParser.bits_to_Z] *)
(* reads).  The mirror image of [CrParser.ExtractOp].                   *)
Inductive EmitOp : Type :=
  | EmitOpConstructor (eo_header : Header) (width : nat).

(* A deparser is just the ordered list of emits it performs. *)
Record Deparser : Type := mkDeparser {
  deparser_emits : list EmitOp;
}.

(* ------------------------------------------------------------------ *)
(* Bit helper.  Inverse of [CrParser.bits_to_Z]: the [width]-bit,       *)
(* MSB-first representation of [z]'s low [width] bits (index 0 of the   *)
(* result is the most significant bit on the wire).                     *)
Definition Z_to_bits (width : nat) (z : Z) : list bool :=
  List.map (fun i => Z.testbit z (Z.of_nat i))
           (List.rev (List.seq 0 width)).
