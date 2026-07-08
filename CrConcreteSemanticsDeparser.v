From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Concrete deparser semantics.                                        *)
(*                                                                     *)
(* A deparser reads header values and writes bits.  It is the inverse  *)
(* of the parser: [apply_extract_concrete] read [width] bits into a    *)
(* header; here each [emit] reads a header value and appends its low   *)
(* [width] bits (MSB-first) to the outgoing packet.  The header map is  *)
(* left untouched, so every emit reads the same (input) header values. *)
(* ================================================================== *)

(* The [i]th emitted bit of a value: bit [i] of an integer value (via the
   already-proven [slice_val]), [false] for a non-integer value.  Phrasing it
   through [slice_val] is what makes the symbolic side line up for free. *)
Definition emit_bit_val (v : CrVal) (i : nat) : bool :=
  CrVal.eqb (slice_val i (S i) v) (mk_int u64 1).

(* Bits emitted for one [EmitOp], MSB-first (index [width-1] down to [0]). *)
Definition emit_bits_concrete (hm : PMap.t CrVal) (eo : EmitOp) : list bool :=
  match eo with
  | EmitOpConstructor h width =>
      List.map (emit_bit_val (lookup_varlike_map hm h))
               (List.rev (List.seq 0 width))
  end.

(* Run the deparser: concatenate every emit's bits (all reading the fixed input
   header map) and prepend them to the incoming payload [p_packet].  Parser then
   deparser thus restores the packet: the parser strips header bits off the
   front, the deparser writes them back. *)
Definition eval_deparser_concrete (d : Deparser) (ps : ConcreteParserState)
    : ConcreteParserState :=
  let emitted := List.flat_map (emit_bits_concrete (p_header_map ps)) (deparser_emits d) in
  {| p_header_map := p_header_map ps;
     p_packet     := emitted ++ p_packet ps;
     p_cursor     := 0 |}.
