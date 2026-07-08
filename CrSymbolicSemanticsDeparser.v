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

Definition eval_deparser_symbolic (d : Deparser) (ps : SymbolicParserState)
    : SymbolicParserState :=
  let emitted := List.flat_map (emit_bits_symbolic (p_header_map ps)) (deparser_emits d) in
  {| p_header_map := p_header_map ps;
     p_packet     := emitted ++ p_packet ps;
     p_cursor     := 0 |}.
