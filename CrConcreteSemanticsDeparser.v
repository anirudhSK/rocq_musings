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

(* =================================================================== *)
(* Concrete deparser semantics.                                        *)
(*                                                                     *)
(* A deparser reads header values and writes bits.  It is the inverse  *)
(* of the parser: [apply_extract_concrete] read [width] bits into a    *)
(* header; here each [emit] reads a header value and appends its low   *)
(* [width] bits (MSB-first) to the outgoing packet.  The header map is *)
(* left untouched, so every emit reads the same (input) header values. *)
(* =================================================================== *)

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
   header map) into the outgoing packet.  The output is exactly the emitted bits
   -- the incoming payload is not carried -- so a parser that strips header bits
   off the front followed by a deparser that emits them back restores the packet
   whenever the parser consumed all of it.

   TOTAL: it never fails.  A header holding no integer -- UninitVal from a
   header never written, ErrorVal from a type-mismatched op -- emits zero bits
   of its full width, since [emit_bit_val] is total and yields [false] on any
   non-integer.  Do not add a validity guard here without an exact symbolic
   counterpart; SOUNDNESS.md, "Why a deparser is total", has the argument. *)
Definition eval_deparser_concrete (d : Deparser) (ps : ConcreteParserState)
    : ConcreteParserState :=
  let emitted := List.flat_map (emit_bits_concrete (p_header_map ps)) (deparser_emits d) in
  {| p_header_map := p_header_map ps;
     p_packet     := emitted;
     p_cursor     := 0 |}.
