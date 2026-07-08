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

(* --- A single emitted bit commutes: interpreting the symbolic bit at [f]
   equals the concrete bit of the [f]-evaluation of the operand.  Both sides are
   phrased through [slice_val], so this is just peeling [SmtBitSlice] (via
   [eval_smt_slice]) and the [mask_width]ed 1-constant (via [eval_const_mask_u64]). --- *)
Lemma emit_bit_commute : forall e i f,
  eval_smt_bool (emit_bit_expr e i) f = emit_bit_val (eval_smt_arith e f) i.
Proof.
  intros e i f. unfold emit_bit_expr, emit_bit_val.
  cbn [eval_smt_bool].
  rewrite eval_smt_slice.
  rewrite eval_const_mask_u64.
  destruct (CrVal.eqb (slice_val i (S i) (eval_smt_arith e f)) (mk_int u64 1));
    reflexivity.
Qed.

(* --- A header lookup on a valuation-concretized header map is the
   [f]-evaluation of the symbolic lookup (a specialization of
   [eval_sym_lookup_header] to a bare packet-less state). --- *)
Lemma lookup_map_commute : forall (H : PMap.t SmtArithExpr) (h : Header) f,
  lookup_varlike_map (PMap.map (fun e => eval_smt_arith e f) H) h
  = eval_smt_arith (lookup_varlike_map H h) f.
Proof.
  intros H h f.
  exact (eval_sym_lookup_header
           {| p_header_map := H; p_packet := @nil SmtBoolExpr; p_cursor := 0 |} f h).
Qed.

(* --- All bits emitted for one [EmitOp] commute. --- *)
Lemma emit_bits_commute : forall H eo f,
  emit_bits_concrete (PMap.map (fun e => eval_smt_arith e f) H) eo
  = List.map (fun b => eval_smt_bool b f) (emit_bits_symbolic H eo).
Proof.
  intros H [h width] f. unfold emit_bits_concrete, emit_bits_symbolic.
  rewrite map_map.
  rewrite lookup_map_commute.
  apply map_ext. intros i. symmetry. apply emit_bit_commute.
Qed.

(* --- The whole emitted packet commutes (fold over the emit list). --- *)
Lemma emitted_bits_commute : forall H emits f,
  List.flat_map (emit_bits_concrete (PMap.map (fun e => eval_smt_arith e f) H)) emits
  = List.map (fun b => eval_smt_bool b f)
             (List.flat_map (emit_bits_symbolic H) emits).
Proof.
  intros H emits f. induction emits as [| eo rest IH]; simpl.
  - reflexivity.
  - rewrite map_app. rewrite emit_bits_commute, IH. reflexivity.
Qed.

(* --- Main result: the deparser commutes with concretization. --- *)
Lemma eval_deparser_commute : forall d s f,
  eval_deparser_concrete d (eval_sym_parser_state s f) =
  eval_sym_parser_state (eval_deparser_symbolic d s) f.
Proof.
  intros d s f.
  unfold eval_deparser_concrete, eval_deparser_symbolic, eval_sym_parser_state.
  cbn [p_header_map p_packet p_cursor].
  f_equal.
  rewrite map_app, emitted_bits_commute.
  reflexivity.
Qed.
