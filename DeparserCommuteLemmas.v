(* Concrete<->symbolic deparser commutation: the deparser analogue of
   [ParserCommuteLemmas].  Culminates in [eval_deparser_commute], which says
   concretizing the symbolic deparser output equals running the concrete
   deparser on the concretized input.  A deparser never fails, so this is a
   plain equality (no option / accept condition). *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrConcreteSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import ParserCommuteLemmas.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From MyProject Require Import PMapHelperLemmas.

(* ------------------------------------------------------------------ *)
(* Generic list plumbing.                                             *)
(* ------------------------------------------------------------------ *)

(* ------------------------------------------------------------------ *)
(* Bit level.                                                         *)
(* ------------------------------------------------------------------ *)

(* The whole commutation rests on this: the two [emit_bit_*] definitions are
   the SAME expression over the [SmtBitSlice]/[slice_val] correspondence that
   [eval_smt_arith] already establishes node for node.  Nothing here is
   deparser-specific -- which is why the deparser was built through
   [slice_val] rather than with its own bit extraction. *)
Lemma emit_bit_commute : forall e i f,
  eval_smt_bool (emit_bit_expr e i) f = emit_bit_val (eval_smt_arith e f) i.
Proof.
  intros e i f. unfold emit_bit_expr, emit_bit_val.
  (* unfold only the [SmtBoolEq] node, so the constant survives for
     [eval_const_mask_u64] to rewrite *)
  cbn [eval_smt_bool].
  rewrite eval_const_mask_u64.
  cbn [eval_smt_arith].
  destruct (CrVal.eqb (slice_val i (S i) (eval_smt_arith e f)) (mk_int u64 1));
    reflexivity.
Qed.

Lemma emit_bits_commute : forall hm eo f,
  List.map (fun b => eval_smt_bool b f) (emit_bits_symbolic hm eo)
  = emit_bits_concrete (PMap.map (fun e => eval_smt_arith e f) hm) eo.
Proof.
  intros hm eo f. destruct eo as [h width].
  cbn [emit_bits_symbolic emit_bits_concrete].
  rewrite lookup_varlike_map_commute, List.map_map.
  apply List.map_ext. intros i. apply emit_bit_commute.
Qed.

(* The same, under the [flat_map] over a deparser's whole emit list. *)
Lemma emitted_bits_commute : forall hm emits f,
  List.map (fun b => eval_smt_bool b f)
           (List.flat_map (emit_bits_symbolic hm) emits)
  = List.flat_map
      (emit_bits_concrete (PMap.map (fun e => eval_smt_arith e f) hm)) emits.
Proof.
  intros hm emits f. induction emits as [| eo rest IH]; cbn [List.flat_map].
  - reflexivity.
  - rewrite List.map_app, emit_bits_commute, IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Whole deparser.                                                    *)
(* ------------------------------------------------------------------ *)

(* Concretizing the symbolic deparser's output is running the concrete
   deparser on the concretized input.  Stated in the exact shape
   [CrSymbolicSemanticsModule.concretize_sym_module_state] uses for its
   [DeparserMod] branch, so the network-level proof can rewrite with it
   directly.

   A plain equality, with no [option] and no accept condition, because a
   deparser is total on both sides -- and the packet is compared POSITIONALLY
   rather than through [present_bits] because every bit a deparser emits
   carries [cvc := SmtTrue]. *)
Theorem eval_deparser_commute : forall d (ps : SymbolicParserState) f,
  eval_deparser_concrete d
    {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
       p_packet     := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet ps);
       p_cursor     := p_cursor ps |}
  = {| p_header_map := PMap.map (fun e => eval_smt_arith e f)
                         (p_header_map (eval_deparser_symbolic d ps));
       p_packet     := List.map (fun b => eval_smt_bool (cvv b) f)
                         (p_packet (eval_deparser_symbolic d ps));
       p_cursor     := p_cursor (eval_deparser_symbolic d ps) |}.
Proof.
  intros d ps f.
  unfold eval_deparser_concrete, eval_deparser_symbolic.
  cbn [p_header_map p_packet p_cursor].
  f_equal.
  (* the emitted bits: [map cvv] undoes the [cvc := SmtTrue] wrapper, then the
     per-emit lemma applies under the [flat_map] *)
  rewrite List.map_map. cbn [cvv].
  symmetry. apply emitted_bits_commute.
Qed.
