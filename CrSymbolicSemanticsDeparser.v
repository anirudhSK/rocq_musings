From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrVarLike.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Symbolic deparser semantics.  Mirrors [eval_deparser_concrete]      *)
(* symbol-for-symbol: each emitted bit becomes an [SmtBoolExpr] testing *)
(* the corresponding bit of the header's symbolic value.               *)
(*                                                                     *)
(* The packet-bit type is [ConditionalVal SmtBoolExpr]: [cvv] is the    *)
(* bit's value and [cvc] its presence/validity condition.  Every bit a  *)
(* deparser emits is unconditionally present (a fixed-width emit always  *)
(* writes its bits), so each emitted position carries [cvc := SmtTrue].  *)
(* ================================================================== *)

(* The [i]th emitted bit of a symbolic value [e]: bit [i] is set iff the
   1-bit slice [i, i+1) equals 1.  The concrete counterpart is [emit_bit_val],
   built on the same [slice_val]/[SmtBitSlice] correspondence. *)
Definition emit_bit_expr (e : SmtArithExpr) (i : nat) : SmtBoolExpr :=
  SmtBoolEq (SmtBitSlice i (S i) e) (SmtArithConst (mask_width W64 1) u64).

Definition emit_bits_symbolic (hm : PMap.t SmtArithExpr) (eo : EmitOp)
    : list SmtBoolExpr :=
  match eo with
  | EmitOpConstructor h width =>
      List.map (emit_bit_expr (lookup_varlike_map hm h))
               (List.rev (List.seq 0 width))
  end.

(* Run the deparser: concatenate every emit's bits (all reading the fixed
   symbolic header map) into the outgoing packet.  Mirrors
   [eval_deparser_concrete], which likewise sets [p_packet] to just the
   emitted bits (the incoming payload is not carried).  Every emitted bit is
   present, hence [cvc := SmtTrue].

   Total, and its concrete counterpart is total for exactly this reason: there
   is no cheap exact symbolic test for "this header holds an integer", and an
   inexact one is unsound in either direction because [check_sym_pkt_out] treats
   two invalid networks as equivalent.  [eval_deparser_concrete] carries the
   full argument -- keep the two totality decisions together. *)
Definition eval_deparser_symbolic (d : Deparser) (ps : SymbolicParserState)
    : SymbolicParserState :=
  let emitted := List.flat_map (emit_bits_symbolic (p_header_map ps)) (deparser_emits d) in
  {| p_header_map := p_header_map ps;
     p_packet     := List.map (fun b => {| cvc := SmtTrue; cvv := b |}) emitted;
     p_cursor     := 0 |}.
