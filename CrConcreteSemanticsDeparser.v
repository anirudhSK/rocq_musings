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
   header map) into the outgoing packet.  The output is exactly the emitted bits
   -- the incoming payload is not carried -- so a parser that strips header bits
   off the front followed by a deparser that emits them back restores the packet
   whenever the parser consumed all of it.

   A deparser is TOTAL: it never fails, not even when asked to emit a header
   that holds no integer (UninitVal from a header never written, ErrorVal from a
   type-mismatched op).  [emit_bit_val] is already total and yields [false] for
   any non-integer, so such an emit writes zero bits rather than rejecting.

   This is deliberate, and the alternative is worth understanding before
   changing it back.  An earlier version guarded the emit with a validity check
   and returned [None] on a non-integer header.  But [eval_deparser_symbolic]
   has no counterpart to such a guard -- symbolically a header is an
   [SmtArithExpr] term, and deciding whether it denotes an [IntVal] needs a
   path-sensitive analysis over [SmtConditional] plus the type-agreement rules
   of [iv_binop_at].  While the guard existed, the symbolic side simply treated
   every deparse as accepting, so the two semantics disagreed.

   That disagreement is not a merely conservative one.  [check_sym_pkt_out]
   treats "both networks invalid" as equivalent, so ANY imprecision in the
   symbolic validity -- in either direction -- is unsound: over-approximating
   acceptance compares garbage bits, and under-approximating it hides real
   output differences inside the both-invalid case.  Soundness therefore forces
   the symbolic validity to be exact, and the cheapest exact option is to have
   no validity condition at all on either side, which is what this does.  It
   also restores the invariant [DeparserCommuteLemmas] was written against: "a
   deparser never fails, so this is a plain equality".

   The cost is a lost diagnostic: emitting a never-written header now silently
   produces zeros instead of rejecting.  If that behaviour is wanted back, the
   guard must be reintroduced together with an exact symbolic counterpart --
   either a static well-formedness check making the guard vacuous, or a
   [hdr_valid : SmtArithExpr -> SmtBoolExpr] folded into [gps_valid] the way the
   parser folds [spr_accept]. *)
Definition eval_deparser_concrete (d : Deparser) (ps : ConcreteParserState)
    : ConcreteParserState :=
  let emitted := List.flat_map (emit_bits_concrete (p_header_map ps)) (deparser_emits d) in
  {| p_header_map := p_header_map ps;
     p_packet     := emitted;
     p_cursor     := 0 |}.
