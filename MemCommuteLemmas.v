(* Concrete<->symbolic commutation for MEMORY: the multi-byte accesses and the
   access-extent bookkeeping.

   [CrVal.ld_val]/[st_val] and [CrSymbolicSemanticsTransformer.smt_ld_val]/
   [smt_st_val] were deliberately written as node-for-node mirrors -- so were
   the [byte_*] helpers underneath them and the [bump_extent_*] pair beside
   them -- precisely so this file could exist.  Until it did, that mirroring
   was a convention held up by comments: the Coq development related the two
   sides only through [eval_smt_*], and nothing forced them to agree.  These
   lemmas are what turn the convention into a theorem.

   Five levels are proved here, bottom up:

   1. VALUE and MEMORY-CONTEXT --

        eval_smt_arith (smt_ld_val ty a base) f
          = ld_val ty (eval_smt_mem a f) (eval_smt_arith base f)

      and the same for [smt_st_val] and for [bump_extent_smt] /
      [bump_extent_span_smt], through [concretize_mem_ctx].  This is the piece
      TODO 1.4 step 2 names.  It is self-contained: nothing about header maps,
      hence no side conditions.

   2. A single op, [eval_hdr_op_assign_mem_commute], covering all seven
      [HdrOp] constructors including [LoadOp], [StatefulLoadOp] and
      [StoreOp].

   3. An op list, [eval_hdr_op_list_mem_commute], by induction.

   4. A match-action rule, [ma_rule_commute_mem] / [_extent] / [_hdr] /
      [_sv].  The concrete side runs the action or not; the symbolic side
      always runs it and merges under the match condition.

   5. A transformer, [transformer_commute_mem] / [_extent] / [_hdr] / [_sv] /
      [_ctrl].  First match wins concretely; symbolically the conditions pick
      out of a [switch_case_arr] / [switch_case_expr] chain.

   Levels 1-3 state whole memory contexts; levels 4 and 5 state one KEY and
   one variable at a time.  That is forced rather than lazy:
   [concretize_mem_ctx] is [PMap.map], which commutes with the [PMap.set]s an
   op performs, whereas a merge rebuilds the map by folding [PMap.set] over an
   explicit key list and so leaves every other key reading the map's DEFAULT.
   It is also the granularity [ConcreteToSymbolicLemmas] already uses for
   headers and state variables, where the same merge shape forces the same
   choice.  Lifting either to whole-state equality is one job, at the module
   level, not four: [NetworkCommuteLemmas.pmap_ext] plus the shape lemmas
   beside it do it once, for the transformer's module state.

   Level 2 was expected to need a whole-state header-map commutation, which
   today exists only per-key and behind an [is_varlike_in_ps] hypothesis.  It
   does not: the two facts it actually wants -- [commute_lookup_eval] for
   operands and [commute_update_eval_varlike] for the write back -- are both
   UNCONDITIONAL.  The side conditions appear at levels 4 and 5, where the
   merge machinery is, not on the op level.

   The memory-free lemmas in [ConcreteToSymbolicLemmas] are NOT reusable for
   levels 4 and 5, which is why those levels are restated here rather than
   applied.  The merge shape is the same but what is merged is not:
   [eval_hdr_op_list_smt] sends a load to [smt_error] where
   [eval_hdr_op_list_smt_mem] sends it to [smt_ld_val] of the region, so the
   two produce different terms for any action that touches memory.  What IS
   shared is the argument around them -- [commute_sym_vs_conc_match_pattern]
   making the two match conditions the same boolean, and the
   [update_all_varlike] lookup, stated here over an arbitrary pair of write
   functions ([lookup_state_merge_hdr] / [_sv]) so that no merge shape leaks
   into it. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrVarLike.
From MyProject Require Import ListUtils.
From MyProject Require Import CtrlPlaneInvariants.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import HelperLemmas.
From MyProject Require Import ConcreteToSymbolicLemmas.
From MyProject Require Import Maps.
From MyProject Require Import Integers.

(* ====================================================================== *)
(* Concretizing a memory context.                                         *)
(* ====================================================================== *)

(* The [MemCtx] analogue of [concretize_sym_modnet_state]: contents through
   [eval_smt_mem], extents through [eval_smt_arith].  Both components are
   [PMap]s, so both are a [PMap.map] -- which is what makes [pmap_map_set] the
   workhorse below, since every memory op is a [PMap.set]. *)
Definition concretize_mem_ctx (mc : SymbolicMemCtx) (f : SmtValuation)
    : ConcreteMemCtx :=
  {| mc_mem    := PMap.map (fun a => eval_smt_mem a f) (mc_mem mc);
     mc_extent := PMap.map (fun e => eval_smt_arith e f) (mc_extent mc) |}.

Lemma concretize_mem_ctx_mem : forall mc f k,
  (mc_mem (concretize_mem_ctx mc f)) !! k = eval_smt_mem ((mc_mem mc) !! k) f.
Proof. intros mc f k. cbn [concretize_mem_ctx mc_mem]. apply PMap.gmap. Qed.

Lemma concretize_mem_ctx_extent : forall mc f k,
  (mc_extent (concretize_mem_ctx mc f)) !! k
  = eval_smt_arith ((mc_extent mc) !! k) f.
Proof. intros mc f k. cbn [concretize_mem_ctx mc_extent]. apply PMap.gmap. Qed.

(* ====================================================================== *)
(* One-node eval equations.                                               *)
(*                                                                        *)
(* All hold by [reflexivity], but they have to be named: [cbn]/[simpl] on  *)
(* [eval_smt_arith] reduces the WHOLE term, including the [SmtArithConst]  *)
(* leaves, and once a constant has been reduced to                         *)
(* [mk_int u64 (unsigned (mask_width W64 z))] the [eval_const_mask_u64]    *)
(* rewrite no longer matches.  Rewriting one node at a time keeps the      *)
(* constants intact until that lemma has had them.                         *)
(* ====================================================================== *)

Lemma eval_bitadd : forall ty a b f,
  eval_smt_arith (SmtBitAdd ty a b) f
  = add_at ty (eval_smt_arith a f) (eval_smt_arith b f).
Proof. reflexivity. Qed.

Lemma eval_bitmul : forall ty a b f,
  eval_smt_arith (SmtBitMul ty a b) f
  = mul_at ty (eval_smt_arith a f) (eval_smt_arith b f).
Proof. reflexivity. Qed.

Lemma eval_bitor : forall ty a b f,
  eval_smt_arith (SmtBitOr ty a b) f
  = or_at ty (eval_smt_arith a f) (eval_smt_arith b f).
Proof. reflexivity. Qed.

Lemma eval_cast_node : forall from to e f,
  eval_smt_arith (SmtCast from to e) f = cast from to (eval_smt_arith e f).
Proof. reflexivity. Qed.

Lemma eval_bitslice : forall lo hi e f,
  eval_smt_arith (SmtBitSlice lo hi e) f
  = slice_val lo hi (eval_smt_arith e f).
Proof. reflexivity. Qed.

Lemma eval_conditional : forall c a b f,
  eval_smt_arith (SmtConditional c a b) f
  = if eval_smt_bool c f then eval_smt_arith a f else eval_smt_arith b f.
Proof. reflexivity. Qed.

Lemma eval_boollt : forall a b f,
  eval_smt_bool (SmtBoolLt a b) f
  = CrVal.ltb (eval_smt_arith a f) (eval_smt_arith b f).
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* Byte-level helpers.                                                    *)
(* ====================================================================== *)

Lemma smt_byte_addr_commute : forall base i f,
  eval_smt_arith (smt_byte_addr base i) f = byte_addr (eval_smt_arith base f) i.
Proof.
  intros base i f. unfold smt_byte_addr, byte_addr.
  rewrite eval_bitadd, eval_const_mask_u64. reflexivity.
Qed.

Lemma smt_byte_of_val_commute : forall v i f,
  eval_smt_arith (smt_byte_of_val v i) f = byte_of_val (eval_smt_arith v f) i.
Proof.
  intros v i f. unfold smt_byte_of_val, byte_of_val.
  rewrite eval_cast_node, eval_bitslice. reflexivity.
Qed.

Lemma smt_byte_into_val_commute : forall b i f,
  eval_smt_arith (smt_byte_into_val b i) f
  = byte_into_val (eval_smt_arith b f) i.
Proof.
  intros b i f. unfold smt_byte_into_val, byte_into_val.
  rewrite eval_bitmul, eval_cast_node, eval_const_mask_u64. reflexivity.
Qed.

(* [SmtArrSel] is [ld_cell]: both collapse the same partiality the same way,
   out of bounds and undeclared and non-integer offset all landing on
   [ErrorVal].  (The [Z3Solver.ml] lowering has to reproduce this with an
   explicit guard, since Z3's [select] is total -- see SOUNDNESS.md.) *)
Lemma smt_arr_sel_commute : forall a idx f,
  eval_smt_arith (SmtArrSel a idx) f
  = ld_cell (eval_smt_mem a f) (eval_smt_arith idx f).
Proof.
  intros a idx f. cbn [eval_smt_arith]. unfold ld_cell. reflexivity.
Qed.

Lemma smt_arr_st_commute : forall a idx v f,
  eval_smt_mem (SmtArrSt a idx v) f
  = match st_arr (eval_smt_mem a f) (eval_smt_arith idx f) (eval_smt_arith v f) with
    | Legal a' => a'
    | Illegal => eval_smt_mem a f
    end.
Proof. intros a idx v f. cbn [eval_smt_mem]. reflexivity. Qed.

(* ====================================================================== *)
(* Multi-byte load.                                                       *)
(* ====================================================================== *)

(* The fold, over an arbitrary index list and an arbitrary accumulator, so the
   induction has something to move on.  [smt_ld_val] instantiates it at
   [List.seq 0 (it_bytes ty)] and a zero accumulator. *)
Lemma smt_ld_val_fold : forall l a base f acc,
  eval_smt_arith
    (List.fold_left
      (fun acc i =>
         SmtBitOr u64 acc (smt_byte_into_val (SmtArrSel a (smt_byte_addr base i)) i))
      l acc) f
  = List.fold_left
      (fun acc i =>
         or_at u64 acc
           (byte_into_val
              (ld_cell (eval_smt_mem a f) (byte_addr (eval_smt_arith base f) i)) i))
      l (eval_smt_arith acc f).
Proof.
  intros l a base f. induction l as [| i r IH]; intros acc; cbn [List.fold_left].
  - reflexivity.
  - rewrite IH, eval_bitor,
            smt_byte_into_val_commute, smt_arr_sel_commute, smt_byte_addr_commute.
    reflexivity.
Qed.

Theorem smt_ld_val_commute : forall ty a base f,
  eval_smt_arith (smt_ld_val ty a base) f
  = ld_val ty (eval_smt_mem a f) (eval_smt_arith base f).
Proof.
  intros ty a base f. unfold smt_ld_val, ld_val.
  rewrite eval_cast_node, smt_ld_val_fold, eval_const_mask_u64.
  reflexivity.
Qed.

(* ====================================================================== *)
(* Multi-byte store.                                                      *)
(* ====================================================================== *)

(* Note the shape of the concrete side: a cell that falls outside the region
   is DROPPED and the rest are still written -- the store is not atomic.  That
   is forced by the symbolic side ([SmtArrSt] is guarded per cell and "all of
   these are in bounds" is not an [SmtBoolExpr]), and this lemma is where the
   two have to agree about it. *)
Lemma smt_st_val_fold : forall l a base v f,
  eval_smt_mem
    (List.fold_left
      (fun acc i => SmtArrSt acc (smt_byte_addr base i) (smt_byte_of_val v i))
      l a) f
  = List.fold_left
      (fun acc i =>
         match st_arr acc (byte_addr (eval_smt_arith base f) i)
                          (byte_of_val (eval_smt_arith v f) i) with
         | Legal a' => a'
         | Illegal => acc
         end)
      l (eval_smt_mem a f).
Proof.
  intros l. induction l as [| i r IH]; intros a base v f; cbn [List.fold_left].
  - reflexivity.
  - rewrite IH, smt_arr_st_commute,
            smt_byte_addr_commute, smt_byte_of_val_commute.
    reflexivity.
Qed.

Theorem smt_st_val_commute : forall ty a base v f,
  eval_smt_mem (smt_st_val ty a base v) f
  = st_val ty (eval_smt_mem a f) (eval_smt_arith base f) (eval_smt_arith v f).
Proof.
  intros ty a base v f. unfold smt_st_val, st_val.
  apply smt_st_val_fold.
Qed.

(* ====================================================================== *)
(* Access extents.                                                        *)
(* ====================================================================== *)

(* [sh_mem_extent]'s whole purpose is to distinguish a program that reads
   further into a region from one that does not, so it has to concretize
   exactly -- an off-by-one here would be invisible to every other lemma and
   would silently weaken the equivalence relation. *)
Theorem bump_extent_commute : forall mc r off f,
  concretize_mem_ctx (bump_extent_smt mc r off) f
  = bump_extent_concrete (concretize_mem_ctx mc f) r (eval_smt_arith off f).
Proof.
  intros mc r off f.
  unfold bump_extent_smt, bump_extent_concrete, set_mc_extent, concretize_mem_ctx.
  cbn [mc_mem mc_extent].
  rewrite pmap_map_set.
  (* the conditional: [SmtBoolLt]/[SmtConditional] against [CrVal.ltb]/[if] *)
  rewrite eval_conditional, eval_boollt, !smt_byte_addr_commute, PMap.gmap.
  reflexivity.
Qed.

Lemma bump_extent_span_fold : forall l mc r base f,
  concretize_mem_ctx
    (List.fold_left (fun acc i => bump_extent_smt acc r (smt_byte_addr base i)) l mc) f
  = List.fold_left
      (fun acc i => bump_extent_concrete acc r (byte_addr (eval_smt_arith base f) i))
      l (concretize_mem_ctx mc f).
Proof.
  intros l. induction l as [| i rest IH]; intros mc r base f; cbn [List.fold_left].
  - reflexivity.
  - rewrite IH, bump_extent_commute, smt_byte_addr_commute. reflexivity.
Qed.

Theorem bump_extent_span_commute : forall mc r base n f,
  concretize_mem_ctx (bump_extent_span_smt mc r base n) f
  = bump_extent_span_concrete (concretize_mem_ctx mc f) r (eval_smt_arith base f) n.
Proof.
  intros mc r base n f.
  unfold bump_extent_span_smt, bump_extent_span_concrete.
  apply bump_extent_span_fold.
Qed.

(* ====================================================================== *)
(* The two together: a region write, as a memory context update.          *)
(* ====================================================================== *)

(* [StoreOp] writes the region back with [PMap.set] before bumping the extent,
   so this is the shape the op-level proof will rewrite with. *)
Theorem concretize_mem_ctx_store : forall mc r ty base v f,
  concretize_mem_ctx
    (set_mc_mem mc (PMap.set (unwrap r)
       (smt_st_val ty ((mc_mem mc) !! (unwrap r)) base v) (mc_mem mc))) f
  = set_mc_mem (concretize_mem_ctx mc f)
      (PMap.set (unwrap r)
        (st_val ty ((mc_mem (concretize_mem_ctx mc f)) !! (unwrap r))
                (eval_smt_arith base f) (eval_smt_arith v f))
        (mc_mem (concretize_mem_ctx mc f))).
Proof.
  intros mc r ty base v f.
  unfold set_mc_mem, concretize_mem_ctx. cbn [mc_mem mc_extent].
  rewrite pmap_map_set, smt_st_val_commute, PMap.gmap. reflexivity.
Qed.


(* ====================================================================== *)
(* The op level: a single memory-threading assignment.                    *)
(*                                                                        *)
(* Level 2 of the five the header lists.  It needs nothing new about       *)
(* header maps, contrary to what was expected: the two facts it            *)
(* wants -- [HelperLemmas.commute_lookup_eval] for operands and            *)
(* [ConcreteToSymbolicLemmas.commute_update_eval_varlike] for the write    *)
(* back -- are both UNCONDITIONAL.  The [is_varlike_in_ps] side conditions *)
(* live on the per-key transformer lemmas further up, not here.            *)
(* ====================================================================== *)

Lemma smt_as_offset_commute : forall e f,
  eval_smt_arith (smt_as_offset e) f = as_offset (eval_smt_arith e f).
Proof.
  intros e f. unfold smt_as_offset, as_offset. apply eval_bitslice.
Qed.

Theorem eval_hdr_op_assign_mem_commute : forall op mc ps f,
  eval_hdr_op_assign_concrete_mem op (concretize_mem_ctx mc f) (eval_sym_state ps f)
  = (concretize_mem_ctx (fst (eval_hdr_op_assign_smt_mem op mc ps)) f,
     eval_sym_state (snd (eval_hdr_op_assign_smt_mem op mc ps)) f).
Proof.
  intros op mc ps f.
  destruct op as [ fn ty a1 a2 tgt | fn ty a1 a2 tgt
                 | fr t a tgt | fr t a tgt
                 | ty r off tgt | ty r off tgt
                 | ty r off val ];
    cbn [eval_hdr_op_assign_concrete_mem eval_hdr_op_assign_smt_mem fst snd].
  (* the four pure-expression ops: memory untouched, state written *)
  1-4: rewrite commute_update_eval_varlike, commute_sym_conc_expr; reflexivity.
  - (* LoadOp *)
    rewrite commute_update_eval_varlike, commute_lookup_eval,
            <- smt_as_offset_commute,
            bump_extent_span_commute, smt_ld_val_commute,
            concretize_mem_ctx_mem.
    reflexivity.
  - rewrite commute_update_eval_varlike, commute_lookup_eval,
            <- smt_as_offset_commute,
            bump_extent_span_commute, smt_ld_val_commute,
            concretize_mem_ctx_mem.
    reflexivity.
  - (* StoreOp: the region is written back with [PMap.set], then the extent
       is bumped over every cell the access covered *)
    (* two operands here, the offset and the stored value, hence [!] *)
    rewrite !commute_lookup_eval, <- smt_as_offset_commute,
            <- eval_smt_cast,
            <- concretize_mem_ctx_store,
            bump_extent_span_commute.
    reflexivity.
Qed.

(* The op LIST is a plain fold over the op level, so it lifts by induction with
   nothing new.  The fold's step destructures its accumulator with a [let], so
   these cons equations are stated first: without them the accumulator is not
   syntactically a pair after one step and the induction hypothesis will not
   apply. *)
Lemma hdr_op_list_concrete_mem_cons : forall op rest mc ps,
  eval_hdr_op_list_concrete_mem (op :: rest) mc ps
  = eval_hdr_op_list_concrete_mem rest
      (fst (eval_hdr_op_assign_concrete_mem op mc ps))
      (snd (eval_hdr_op_assign_concrete_mem op mc ps)).
Proof.
  intros op rest mc ps. unfold eval_hdr_op_list_concrete_mem.
  cbn [List.fold_left]. destruct (eval_hdr_op_assign_concrete_mem op mc ps).
  reflexivity.
Qed.

Lemma hdr_op_list_smt_mem_cons : forall op rest mc ps,
  eval_hdr_op_list_smt_mem (op :: rest) mc ps
  = eval_hdr_op_list_smt_mem rest
      (fst (eval_hdr_op_assign_smt_mem op mc ps))
      (snd (eval_hdr_op_assign_smt_mem op mc ps)).
Proof.
  intros op rest mc ps. unfold eval_hdr_op_list_smt_mem.
  cbn [List.fold_left]. destruct (eval_hdr_op_assign_smt_mem op mc ps).
  reflexivity.
Qed.

(* Generalising over BOTH the memory context and the state is what makes the
   step go through: each op can change either. *)
Theorem eval_hdr_op_list_mem_commute : forall hol mc ps f,
  eval_hdr_op_list_concrete_mem hol (concretize_mem_ctx mc f) (eval_sym_state ps f)
  = (concretize_mem_ctx (fst (eval_hdr_op_list_smt_mem hol mc ps)) f,
     eval_sym_state (snd (eval_hdr_op_list_smt_mem hol mc ps)) f).
Proof.
  intros hol. induction hol as [| op rest IH]; intros mc ps f.
  - reflexivity.
  - rewrite hdr_op_list_concrete_mem_cons, hdr_op_list_smt_mem_cons.
    rewrite eval_hdr_op_assign_mem_commute. cbn [fst snd]. apply IH.
Qed.


(* ====================================================================== *)
(* 4. THE MERGE LEVEL.                                                    *)
(*                                                                        *)
(* Everything above this point concretizes a memory context with          *)
(* [concretize_mem_ctx], which is [PMap.map] and so commutes with the     *)
(* [PMap.set]s an op performs.  A MERGE does not have that shape: both    *)
(* [merge_mem_ctx_smt] and the [mem']/[ext'] folds inside                 *)
(* [eval_transformer_smt_mem] rebuild the map by folding [PMap.set] over  *)
(* an explicit key list, which leaves every other key reading the map's   *)
(* DEFAULT.  So from here the statements are per key, matching the shape  *)
(* the memory-free development in [ConcreteToSymbolicLemmas] already uses *)
(* for headers and state variables -- and a key outside the list needs an *)
(* argument of its own, which is what the defaults section below is for.  *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Defaults survive a run.                                                 *)
(*                                                                         *)
(* A merge enumerates the keys both sides bind explicitly and rebuilds only *)
(* those.  At every other key it just keeps the incoming map, which is only *)
(* correct because the branch could not have differed there: an op reaches  *)
(* memory through [PMap.set], which never touches the default, so the two   *)
(* sides read the same value at any key neither of them binds.  Without     *)
(* this the merge would be wrong precisely on the regions no rule mentions. *)
(* ---------------------------------------------------------------------- *)

Lemma bump_extent_span_fold_default : forall l mc r base,
  fst (mc_mem (List.fold_left
        (fun acc i => bump_extent_smt acc r (smt_byte_addr base i)) l mc))
    = fst (mc_mem mc)
  /\ fst (mc_extent (List.fold_left
        (fun acc i => bump_extent_smt acc r (smt_byte_addr base i)) l mc))
    = fst (mc_extent mc).
Proof.
  intros l. induction l as [| i rest IH]; intros mc r base; cbn [List.fold_left].
  - split; reflexivity.
  - destruct (IH (bump_extent_smt mc r (smt_byte_addr base i)) r base) as [H1 H2].
    rewrite H1, H2. split; reflexivity.
Qed.

Lemma bump_extent_span_smt_default : forall mc r base n,
  fst (mc_mem (bump_extent_span_smt mc r base n)) = fst (mc_mem mc)
  /\ fst (mc_extent (bump_extent_span_smt mc r base n)) = fst (mc_extent mc).
Proof.
  intros mc r base n. unfold bump_extent_span_smt.
  apply bump_extent_span_fold_default.
Qed.

Lemma eval_hdr_op_assign_smt_mem_default : forall op mc ps,
  fst (mc_mem (fst (eval_hdr_op_assign_smt_mem op mc ps))) = fst (mc_mem mc)
  /\ fst (mc_extent (fst (eval_hdr_op_assign_smt_mem op mc ps))) = fst (mc_extent mc).
Proof.
  intros op mc ps.
  destruct op as [ fn ty a1 a2 tgt | fn ty a1 a2 tgt
                 | fr t a tgt | fr t a tgt
                 | ty r off tgt | ty r off tgt
                 | ty r off val ];
    cbn [eval_hdr_op_assign_smt_mem fst].
  1-4: split; reflexivity.
  1-2: apply bump_extent_span_smt_default.
  - destruct (bump_extent_span_smt_default
                (set_mc_mem mc (PMap.set (unwrap r)
                   (smt_st_val ty ((mc_mem mc) !! (unwrap r))
                      (smt_as_offset (lookup_smt u64 off ps))
                      (smt_cast ty ty (lookup_smt ty val ps))) (mc_mem mc)))
                r (smt_as_offset (lookup_smt u64 off ps)) (it_bytes ty))
      as [H1 H2].
    rewrite H1, H2. split; reflexivity.
Qed.

Lemma eval_hdr_op_list_smt_mem_default : forall hol mc ps,
  fst (mc_mem (fst (eval_hdr_op_list_smt_mem hol mc ps))) = fst (mc_mem mc)
  /\ fst (mc_extent (fst (eval_hdr_op_list_smt_mem hol mc ps))) = fst (mc_extent mc).
Proof.
  intros hol. induction hol as [| op rest IH]; intros mc ps.
  - split; reflexivity.
  - rewrite hdr_op_list_smt_mem_cons.
    destruct (IH (fst (eval_hdr_op_assign_smt_mem op mc ps))
                 (snd (eval_hdr_op_assign_smt_mem op mc ps))) as [H1 H2].
    destruct (eval_hdr_op_assign_smt_mem_default op mc ps) as [H3 H4].
    rewrite H1, H2, H3, H4. split; reflexivity.
Qed.

(* Two maps with the same default agree at any key neither binds. *)
Lemma pmap_lookup_outside : forall {A : Type} (m1 m2 : PMap.t A) k,
  fst m1 = fst m2 ->
  ~ In k (pmap_keys m1) -> ~ In k (pmap_keys m2) ->
  m1 !! k = m2 !! k.
Proof.
  intros A m1 m2 k Hd H1 H2.
  rewrite (pmap_get_notin_keys m1 k H1), (pmap_get_notin_keys m2 k H2).
  assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* [merge_mem_ctx_smt], per key.                                           *)
(* ---------------------------------------------------------------------- *)

Definition merge_keys (mc1 mc2 : SymbolicMemCtx) : list positive :=
  pmap_keys (mc_mem mc1) ++ pmap_keys (mc_mem mc2)
  ++ pmap_keys (mc_extent mc1) ++ pmap_keys (mc_extent mc2).

Lemma merge_mem_ctx_smt_mem : forall c mc1 mc2 k,
  (mc_mem (merge_mem_ctx_smt c mc1 mc2)) !! k
  = if in_dec Coqlib.peq k (merge_keys mc1 mc2)
    then SmtArrIte c ((mc_mem mc1) !! k) ((mc_mem mc2) !! k)
    else (mc_mem mc2) !! k.
Proof.
  intros c mc1 mc2 k. unfold merge_mem_ctx_smt, merge_keys. cbn [mc_mem].
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - apply (pmap_fold_set_in
             (fun k => SmtArrIte c ((mc_mem mc1) !! k) ((mc_mem mc2) !! k))).
    assumption.
  - apply (pmap_fold_set_notin
             (fun k => SmtArrIte c ((mc_mem mc1) !! k) ((mc_mem mc2) !! k))).
    assumption.
Qed.

Lemma merge_mem_ctx_smt_extent : forall c mc1 mc2 k,
  (mc_extent (merge_mem_ctx_smt c mc1 mc2)) !! k
  = if in_dec Coqlib.peq k (merge_keys mc1 mc2)
    then SmtConditional c ((mc_extent mc1) !! k) ((mc_extent mc2) !! k)
    else (mc_extent mc2) !! k.
Proof.
  intros c mc1 mc2 k. unfold merge_mem_ctx_smt, merge_keys. cbn [mc_extent].
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - apply (pmap_fold_set_in
             (fun k => SmtConditional c ((mc_extent mc1) !! k) ((mc_extent mc2) !! k))).
    assumption.
  - apply (pmap_fold_set_notin
             (fun k => SmtConditional c ((mc_extent mc1) !! k) ((mc_extent mc2) !! k))).
    assumption.
Qed.

(* Outside the merged keys the two sides are the same map entry, so the merge
   keeping [mc2] is not a choice at all.  Both halves need the defaults to
   have survived the branch, which is what the section above establishes. *)
Lemma merge_outside_mem : forall mc1 mc2 k,
  fst (mc_mem mc1) = fst (mc_mem mc2) ->
  ~ In k (merge_keys mc1 mc2) ->
  (mc_mem mc1) !! k = (mc_mem mc2) !! k.
Proof.
  intros mc1 mc2 k Hd Hnin. unfold merge_keys in Hnin.
  apply pmap_lookup_outside.
  - assumption.
  - intro H; apply Hnin; apply in_or_app; left; assumption.
  - intro H; apply Hnin; apply in_or_app; right; apply in_or_app; left;
      assumption.
Qed.

Lemma merge_outside_extent : forall mc1 mc2 k,
  fst (mc_extent mc1) = fst (mc_extent mc2) ->
  ~ In k (merge_keys mc1 mc2) ->
  (mc_extent mc1) !! k = (mc_extent mc2) !! k.
Proof.
  intros mc1 mc2 k Hd Hnin. unfold merge_keys in Hnin.
  apply pmap_lookup_outside.
  - assumption.
  - intro H; apply Hnin; apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; left; assumption.
  - intro H; apply Hnin; apply in_or_app; right; apply in_or_app; right;
      apply in_or_app; right; assumption.
Qed.

(* ---------------------------------------------------------------------- *)
(* A match-action rule, memory component.                                  *)
(*                                                                         *)
(* The concrete side runs the action or not; the symbolic side always runs *)
(* it and merges under the match condition.  They line up because          *)
(* [commute_sym_vs_conc_match_pattern] makes the two conditions the same   *)
(* boolean -- the same reason the header/state-variable versions of these  *)
(* lemmas work in [ConcreteToSymbolicLemmas].                              *)
(* ---------------------------------------------------------------------- *)

Lemma seq_rule_commute_mem : forall srule mc ps f k,
  (mc_mem (fst (eval_seq_rule_concrete_mem srule
                  (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_mem ((mc_mem (fst (eval_seq_rule_smt_mem srule mc ps))) !! k) f.
Proof.
  intros [mp action] mc ps f k.
  cbn [eval_seq_rule_concrete_mem eval_seq_rule_smt_mem].
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  rewrite eval_hdr_op_list_mem_commute.
  cbn [fst].
  rewrite merge_mem_ctx_smt_mem.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin];
    destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
    cbn [fst eval_smt_mem]; rewrite ?E, ?concretize_mem_ctx_mem;
    try reflexivity.
  (* the one real case: the branch taken wrote a key the merge does not
     enumerate, which cannot happen -- both sides are still the default *)
  f_equal. apply merge_outside_mem; [| assumption ].
  apply (eval_hdr_op_list_smt_mem_default action mc ps).
Qed.

Lemma seq_rule_commute_extent : forall srule mc ps f k,
  (mc_extent (fst (eval_seq_rule_concrete_mem srule
                     (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_arith ((mc_extent (fst (eval_seq_rule_smt_mem srule mc ps))) !! k) f.
Proof.
  intros [mp action] mc ps f k.
  cbn [eval_seq_rule_concrete_mem eval_seq_rule_smt_mem].
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  rewrite eval_hdr_op_list_mem_commute.
  cbn [fst].
  rewrite merge_mem_ctx_smt_extent.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin];
    destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
    cbn [fst eval_smt_arith]; rewrite ?E, ?concretize_mem_ctx_extent;
    try reflexivity.
  f_equal. apply merge_outside_extent; [| assumption ].
  apply (eval_hdr_op_list_smt_mem_default action mc ps).
Qed.

(* [ParRule] is the same function with a [proj1_sig] in front of the action --
   memory is threaded through it sequentially, see the comment on
   [eval_par_rule_concrete_mem] -- so the proofs are the same. *)
Lemma par_rule_commute_mem : forall prule mc ps f k,
  (mc_mem (fst (eval_par_rule_concrete_mem prule
                  (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_mem ((mc_mem (fst (eval_par_rule_smt_mem prule mc ps))) !! k) f.
Proof.
  intros [mp action] mc ps f k.
  cbn [eval_par_rule_concrete_mem eval_par_rule_smt_mem].
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  rewrite eval_hdr_op_list_mem_commute.
  cbn [fst].
  rewrite merge_mem_ctx_smt_mem.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin];
    destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
    cbn [fst eval_smt_mem]; rewrite ?E, ?concretize_mem_ctx_mem;
    try reflexivity.
  f_equal. apply merge_outside_mem; [| assumption ].
  apply (eval_hdr_op_list_smt_mem_default (proj1_sig action) mc ps).
Qed.

Lemma par_rule_commute_extent : forall prule mc ps f k,
  (mc_extent (fst (eval_par_rule_concrete_mem prule
                     (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_arith ((mc_extent (fst (eval_par_rule_smt_mem prule mc ps))) !! k) f.
Proof.
  intros [mp action] mc ps f k.
  cbn [eval_par_rule_concrete_mem eval_par_rule_smt_mem].
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  rewrite eval_hdr_op_list_mem_commute.
  cbn [fst].
  rewrite merge_mem_ctx_smt_extent.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin];
    destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
    cbn [fst eval_smt_arith]; rewrite ?E, ?concretize_mem_ctx_extent;
    try reflexivity.
  f_equal. apply merge_outside_extent; [| assumption ].
  apply (eval_hdr_op_list_smt_mem_default (proj1_sig action) mc ps).
Qed.

Theorem ma_rule_commute_mem : forall rule mc ps f k,
  (mc_mem (fst (eval_match_action_rule_concrete_mem rule
                  (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_mem
      ((mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps))) !! k) f.
Proof.
  intros [srule | prule] mc ps f k.
  - apply seq_rule_commute_mem.
  - apply par_rule_commute_mem.
Qed.

Theorem ma_rule_commute_extent : forall rule mc ps f k,
  (mc_extent (fst (eval_match_action_rule_concrete_mem rule
                     (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_arith
      ((mc_extent (fst (eval_match_action_rule_smt_mem rule mc ps))) !! k) f.
Proof.
  intros [srule | prule] mc ps f k.
  - apply seq_rule_commute_extent.
  - apply par_rule_commute_extent.
Qed.

(* ---------------------------------------------------------------------- *)
(* A match-action rule, state component.                                   *)
(*                                                                         *)
(* [ConcreteToSymbolicLemmas] already has this for the memory-free          *)
(* evaluators, and it is NOT reusable here: the two differ in what the      *)
(* action produced.  [eval_hdr_op_list_smt] sends a load to [smt_error],    *)
(* [eval_hdr_op_list_smt_mem] sends it to [smt_ld_val] of the region, so    *)
(* the merged expressions are different terms whenever the action touches   *)
(* memory.  The merge around them is the same, though, which is what the    *)
(* first two lemmas isolate -- they are stated over an arbitrary post-state *)
(* [ps'] so nothing about the action leaks into them.                       *)
(* ---------------------------------------------------------------------- *)

(* Both merges -- the rule's [SmtConditional] and the transformer's
   [switch_case_expr] chain -- write every header and every state variable
   through the same two nested [update_all_varlike]s, so what a lookup sees is
   just the function that was written, whatever it was.  Stating it over an
   arbitrary [gh]/[gs] keeps the merge shape out of the levels above. *)
Lemma lookup_state_merge_hdr :
  forall (ps : SymbolicTransformerState)
         (gh : Header -> SmtArithExpr) (gs : State -> SmtArithExpr) f (h : Header),
  is_varlike_in_ps ps h <> None ->
  lookup_varlike
    (eval_sym_state (update_all_varlike (update_all_varlike ps gh) gs) f) h
  = eval_smt_arith (gh h) f.
Proof.
  intros ps gh gs f h Hh.
  rewrite commute_lookup_eval_varlike. f_equal.
  rewrite <- commute_varlike_updates.
  unfold lookup_varlike at 1.
  rewrite lookup_varlike_after_update_all_varlike.
  - reflexivity.
  - rewrite is_v1_in_ps_after_update_all_v2. assumption.
Qed.

Lemma lookup_state_merge_sv :
  forall (ps : SymbolicTransformerState)
         (gh : Header -> SmtArithExpr) (gs : State -> SmtArithExpr) f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  lookup_varlike
    (eval_sym_state (update_all_varlike (update_all_varlike ps gh) gs) f) sv
  = eval_smt_arith (gs sv) f.
Proof.
  intros ps gh gs f sv Hsv.
  rewrite commute_lookup_eval_varlike. f_equal.
  unfold lookup_varlike at 1.
  rewrite lookup_varlike_after_update_all_varlike.
  - reflexivity.
  - rewrite is_v1_in_ps_after_update_all_v2. assumption.
Qed.

Lemma seq_rule_commute_hdr : forall srule mc ps f (h : Header),
  is_varlike_in_ps ps h <> None ->
  lookup_varlike (snd (eval_seq_rule_concrete_mem srule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) h
  = lookup_varlike (eval_sym_state (snd (eval_seq_rule_smt_mem srule mc ps)) f) h.
Proof.
  intros [mp hol] mc ps f h Hh.
  cbn [eval_seq_rule_concrete_mem eval_seq_rule_smt_mem snd].
  rewrite lookup_state_merge_hdr by assumption.
  rewrite eval_conditional.
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E.
  - rewrite eval_hdr_op_list_mem_commute. cbn [snd].
    apply commute_lookup_eval_varlike.
  - cbn [snd]. apply commute_lookup_eval_varlike.
Qed.

Lemma seq_rule_commute_sv : forall srule mc ps f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  lookup_varlike (snd (eval_seq_rule_concrete_mem srule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) sv
  = lookup_varlike (eval_sym_state (snd (eval_seq_rule_smt_mem srule mc ps)) f) sv.
Proof.
  intros [mp hol] mc ps f sv Hsv.
  cbn [eval_seq_rule_concrete_mem eval_seq_rule_smt_mem snd].
  rewrite lookup_state_merge_sv by assumption.
  rewrite eval_conditional.
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E.
  - rewrite eval_hdr_op_list_mem_commute. cbn [snd].
    apply commute_lookup_eval_varlike.
  - cbn [snd]. apply commute_lookup_eval_varlike.
Qed.

Lemma par_rule_commute_hdr : forall prule mc ps f (h : Header),
  is_varlike_in_ps ps h <> None ->
  lookup_varlike (snd (eval_par_rule_concrete_mem prule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) h
  = lookup_varlike (eval_sym_state (snd (eval_par_rule_smt_mem prule mc ps)) f) h.
Proof.
  intros [mp action] mc ps f h Hh.
  cbn [eval_par_rule_concrete_mem eval_par_rule_smt_mem snd].
  rewrite lookup_state_merge_hdr by assumption.
  rewrite eval_conditional.
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E.
  - rewrite eval_hdr_op_list_mem_commute. cbn [snd].
    apply commute_lookup_eval_varlike.
  - cbn [snd]. apply commute_lookup_eval_varlike.
Qed.

Lemma par_rule_commute_sv : forall prule mc ps f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  lookup_varlike (snd (eval_par_rule_concrete_mem prule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) sv
  = lookup_varlike (eval_sym_state (snd (eval_par_rule_smt_mem prule mc ps)) f) sv.
Proof.
  intros [mp action] mc ps f sv Hsv.
  cbn [eval_par_rule_concrete_mem eval_par_rule_smt_mem snd].
  rewrite lookup_state_merge_sv by assumption.
  rewrite eval_conditional.
  rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl).
  destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E.
  - rewrite eval_hdr_op_list_mem_commute. cbn [snd].
    apply commute_lookup_eval_varlike.
  - cbn [snd]. apply commute_lookup_eval_varlike.
Qed.

Theorem ma_rule_commute_hdr : forall rule mc ps f (h : Header),
  is_varlike_in_ps ps h <> None ->
  lookup_varlike (snd (eval_match_action_rule_concrete_mem rule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) h
  = lookup_varlike
      (eval_sym_state (snd (eval_match_action_rule_smt_mem rule mc ps)) f) h.
Proof.
  intros [srule | prule] mc ps f h Hh.
  - apply seq_rule_commute_hdr; assumption.
  - apply par_rule_commute_hdr; assumption.
Qed.

Theorem ma_rule_commute_sv : forall rule mc ps f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  lookup_varlike (snd (eval_match_action_rule_concrete_mem rule
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) sv
  = lookup_varlike
      (eval_sym_state (snd (eval_match_action_rule_smt_mem rule mc ps)) f) sv.
Proof.
  intros [srule | prule] mc ps f sv Hsv.
  - apply seq_rule_commute_sv; assumption.
  - apply par_rule_commute_sv; assumption.
Qed.

(* ====================================================================== *)
(* 5. THE TRANSFORMER LEVEL.                                              *)
(*                                                                        *)
(* First match wins on the concrete side; the symbolic side builds the    *)
(* whole chain and lets the conditions pick.  The memory-free version of  *)
(* this argument is [ConcreteToSymbolicLemmas]'s pair of                  *)
(* [switch_case_expr_*_match_lemma]s, one for a match and one for none.   *)
(* Here they are a single statement whose right-hand side is the [option] *)
(* [find_first_match] returns, which is what makes the induction step     *)
(* uniform: the recursive call is the same lemma at [t], not a different  *)
(* one depending on how the search turned out.                            *)
(* ====================================================================== *)

Lemma switch_case_arr_match : forall t mc ps f k,
  eval_smt_mem
    (switch_case_arr
       (List.combine (get_match_results_smt t ps)
          (List.map (fun m => (mc_mem m) !! k)
             (List.map fst
                (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
       ((mc_mem mc) !! k)) f
  = match find_first_match
            (List.combine (get_match_results t (eval_sym_state ps f)) t) with
    | Some rule =>
        (mc_mem (fst (eval_match_action_rule_concrete_mem rule
                        (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
    | None => (mc_mem (concretize_mem_ctx mc f)) !! k
    end.
Proof.
  intros t mc ps f k. induction t as [| a rest IH].
  - cbn [switch_case_arr get_match_results_smt get_match_results
         List.map List.combine find_first_match].
    symmetry. apply concretize_mem_ctx_mem.
  - destruct a as [[mp action] | [mp action]];
      cbn [get_match_results_smt get_match_results List.map List.combine
           switch_case_arr find_first_match];
      rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl);
      cbn [eval_smt_mem];
      destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
      [ symmetry; apply ma_rule_commute_mem | apply IH
      | symmetry; apply ma_rule_commute_mem | apply IH ].
Qed.

Lemma switch_case_expr_extent_match : forall t mc ps f k,
  eval_smt_arith
    (switch_case_expr
       (List.combine (get_match_results_smt t ps)
          (List.map (fun m => (mc_extent m) !! k)
             (List.map fst
                (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
       ((mc_extent mc) !! k)) f
  = match find_first_match
            (List.combine (get_match_results t (eval_sym_state ps f)) t) with
    | Some rule =>
        (mc_extent (fst (eval_match_action_rule_concrete_mem rule
                           (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
    | None => (mc_extent (concretize_mem_ctx mc f)) !! k
    end.
Proof.
  intros t mc ps f k. induction t as [| a rest IH].
  - cbn [switch_case_expr get_match_results_smt get_match_results
         List.map List.combine find_first_match].
    symmetry. apply concretize_mem_ctx_extent.
  - destruct a as [[mp action] | [mp action]];
      cbn [get_match_results_smt get_match_results List.map List.combine
           switch_case_expr find_first_match];
      rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl);
      rewrite eval_conditional;
      destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
      [ symmetry; apply ma_rule_commute_extent | apply IH
      | symmetry; apply ma_rule_commute_extent | apply IH ].
Qed.

(* ---------------------------------------------------------------------- *)
(* The keys the transformer-level merge enumerates.                        *)
(*                                                                         *)
(* Same shape as [merge_keys] one level down, and the same obligation: a    *)
(* key outside the list keeps the INCOMING context, so it has to be a key   *)
(* no branch could have written.  [In rule t] is what connects the branch   *)
(* [find_first_match] picked to the list that was enumerated.               *)
(* ---------------------------------------------------------------------- *)

Definition transformer_keys (t : Transformer) (mc : SymbolicMemCtx)
    (ps : SymbolicTransformerState) : list positive :=
  let mem_ctxs :=
    List.map fst (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t) in
  List.concat (List.map (fun m => pmap_keys (mc_mem m)) mem_ctxs)
  ++ List.concat (List.map (fun m => pmap_keys (mc_extent m)) mem_ctxs)
  ++ pmap_keys (mc_mem mc) ++ pmap_keys (mc_extent mc).

Lemma ma_rule_smt_mem_default : forall rule mc ps,
  fst (mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps))) = fst (mc_mem mc)
  /\ fst (mc_extent (fst (eval_match_action_rule_smt_mem rule mc ps)))
     = fst (mc_extent mc).
Proof.
  intros [[mp action] | [mp action]] mc ps;
    cbn [eval_match_action_rule_smt_mem eval_seq_rule_smt_mem eval_par_rule_smt_mem
         fst merge_mem_ctx_smt mc_mem mc_extent];
    split; apply pmap_fold_set_default.
Qed.

Lemma transformer_keys_mem : forall t mc ps rule k,
  In rule t ->
  In k (pmap_keys (mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps)))) ->
  In k (transformer_keys t mc ps).
Proof.
  intros t mc ps rule k Hr Hk. unfold transformer_keys.
  apply in_or_app. left. apply List.in_concat.
  exists (pmap_keys (mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps)))).
  split; [| assumption ].
  apply (in_map (fun m => pmap_keys (mc_mem m))).
  apply (in_map fst).
  apply (in_map (fun r => eval_match_action_rule_smt_mem r mc ps)).
  assumption.
Qed.

Lemma transformer_keys_extent : forall t mc ps rule k,
  In rule t ->
  In k (pmap_keys (mc_extent (fst (eval_match_action_rule_smt_mem rule mc ps)))) ->
  In k (transformer_keys t mc ps).
Proof.
  intros t mc ps rule k Hr Hk. unfold transformer_keys.
  apply in_or_app. right. apply in_or_app. left. apply List.in_concat.
  exists (pmap_keys (mc_extent (fst (eval_match_action_rule_smt_mem rule mc ps)))).
  split; [| assumption ].
  apply (in_map (fun m => pmap_keys (mc_extent m))).
  apply (in_map fst).
  apply (in_map (fun r => eval_match_action_rule_smt_mem r mc ps)).
  assumption.
Qed.

Lemma transformer_keys_incoming_mem : forall t mc ps k,
  In k (pmap_keys (mc_mem mc)) -> In k (transformer_keys t mc ps).
Proof.
  intros. unfold transformer_keys.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; assumption.
Qed.

Lemma transformer_keys_incoming_extent : forall t mc ps k,
  In k (pmap_keys (mc_extent mc)) -> In k (transformer_keys t mc ps).
Proof.
  intros. unfold transformer_keys.
  apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; assumption.
Qed.

(* Outside the enumerated keys the rule that ran is indistinguishable from the
   incoming context: it bound no key there and could not have moved the
   default. *)
Lemma transformer_outside_mem : forall t mc ps rule k,
  In rule t ->
  ~ In k (transformer_keys t mc ps) ->
  (mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps))) !! k = (mc_mem mc) !! k.
Proof.
  intros t mc ps rule k Hr Hnin.
  apply pmap_lookup_outside.
  - apply (ma_rule_smt_mem_default rule mc ps).
  - intro H; apply Hnin; apply (transformer_keys_mem t mc ps rule k Hr H).
  - intro H; apply Hnin; apply (transformer_keys_incoming_mem t mc ps k H).
Qed.

Lemma transformer_outside_extent : forall t mc ps rule k,
  In rule t ->
  ~ In k (transformer_keys t mc ps) ->
  (mc_extent (fst (eval_match_action_rule_smt_mem rule mc ps))) !! k
  = (mc_extent mc) !! k.
Proof.
  intros t mc ps rule k Hr Hnin.
  apply pmap_lookup_outside.
  - apply (ma_rule_smt_mem_default rule mc ps).
  - intro H; apply Hnin; apply (transformer_keys_extent t mc ps rule k Hr H).
  - intro H; apply Hnin; apply (transformer_keys_incoming_extent t mc ps k H).
Qed.

(* The rule [find_first_match] returns is one of the transformer's own. *)
Lemma find_first_match_in_transformer : forall t c rule,
  Some rule = find_first_match (List.combine (get_match_results t c) t) ->
  In rule t.
Proof.
  intros t c rule H.
  assert (Hin : In (true, rule) (List.combine (get_match_results t c) t))
    by (apply find_first_match_lemma2; assumption).
  apply List.in_combine_r in Hin. assumption.
Qed.

Lemma eval_transformer_smt_mem_mem : forall t mc ps k,
  (mc_mem (fst (eval_transformer_smt_mem t mc ps))) !! k
  = if in_dec Coqlib.peq k (transformer_keys t mc ps)
    then switch_case_arr
           (List.combine (get_match_results_smt t ps)
              (List.map (fun m => (mc_mem m) !! k)
                 (List.map fst
                    (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
           ((mc_mem mc) !! k)
    else (mc_mem mc) !! k.
Proof.
  intros t mc ps k. unfold eval_transformer_smt_mem, transformer_keys.
  cbn [fst mc_mem].
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - apply (pmap_fold_set_in
             (fun k => switch_case_arr
                (List.combine (get_match_results_smt t ps)
                   (List.map (fun m => (mc_mem m) !! k)
                      (List.map fst
                         (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
                ((mc_mem mc) !! k))).
    assumption.
  - apply (pmap_fold_set_notin
             (fun k => switch_case_arr
                (List.combine (get_match_results_smt t ps)
                   (List.map (fun m => (mc_mem m) !! k)
                      (List.map fst
                         (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
                ((mc_mem mc) !! k))).
    assumption.
Qed.

Lemma eval_transformer_smt_mem_extent : forall t mc ps k,
  (mc_extent (fst (eval_transformer_smt_mem t mc ps))) !! k
  = if in_dec Coqlib.peq k (transformer_keys t mc ps)
    then switch_case_expr
           (List.combine (get_match_results_smt t ps)
              (List.map (fun m => (mc_extent m) !! k)
                 (List.map fst
                    (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
           ((mc_extent mc) !! k)
    else (mc_extent mc) !! k.
Proof.
  intros t mc ps k. unfold eval_transformer_smt_mem, transformer_keys.
  cbn [fst mc_extent].
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - apply (pmap_fold_set_in
             (fun k => switch_case_expr
                (List.combine (get_match_results_smt t ps)
                   (List.map (fun m => (mc_extent m) !! k)
                      (List.map fst
                         (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
                ((mc_extent mc) !! k))).
    assumption.
  - apply (pmap_fold_set_notin
             (fun k => switch_case_expr
                (List.combine (get_match_results_smt t ps)
                   (List.map (fun m => (mc_extent m) !! k)
                      (List.map fst
                         (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
                ((mc_extent mc) !! k))).
    assumption.
Qed.

Theorem transformer_commute_mem : forall t mc ps f k,
  (mc_mem (fst (eval_transformer_concrete_mem t
                  (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_mem ((mc_mem (fst (eval_transformer_smt_mem t mc ps))) !! k) f.
Proof.
  intros t mc ps f k.
  rewrite eval_transformer_smt_mem_mem.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (in_dec Coqlib.peq k (transformer_keys t mc ps)) as [Hin | Hnin].
  - rewrite switch_case_arr_match.
    destruct (find_first_match
                (List.combine (get_match_results t (eval_sym_state ps f)) t));
      cbn [fst]; reflexivity.
  - destruct (find_first_match
                (List.combine (get_match_results t (eval_sym_state ps f)) t))
      as [rule |] eqn:Hf; cbn [fst].
    + rewrite ma_rule_commute_mem. f_equal.
      apply (transformer_outside_mem t mc ps rule k); [| assumption ].
      apply (find_first_match_in_transformer t (eval_sym_state ps f) rule).
      symmetry; assumption.
    + apply concretize_mem_ctx_mem.
Qed.

Theorem transformer_commute_extent : forall t mc ps f k,
  (mc_extent (fst (eval_transformer_concrete_mem t
                     (concretize_mem_ctx mc f) (eval_sym_state ps f)))) !! k
  = eval_smt_arith ((mc_extent (fst (eval_transformer_smt_mem t mc ps))) !! k) f.
Proof.
  intros t mc ps f k.
  rewrite eval_transformer_smt_mem_extent.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (in_dec Coqlib.peq k (transformer_keys t mc ps)) as [Hin | Hnin].
  - rewrite switch_case_expr_extent_match.
    destruct (find_first_match
                (List.combine (get_match_results t (eval_sym_state ps f)) t));
      cbn [fst]; reflexivity.
  - destruct (find_first_match
                (List.combine (get_match_results t (eval_sym_state ps f)) t))
      as [rule |] eqn:Hf; cbn [fst].
    + rewrite ma_rule_commute_extent. f_equal.
      apply (transformer_outside_extent t mc ps rule k); [| assumption ].
      apply (find_first_match_in_transformer t (eval_sym_state ps f) rule).
      symmetry; assumption.
    + apply concretize_mem_ctx_extent.
Qed.

Lemma switch_case_hdr_match : forall t mc ps f (h : Header),
  is_varlike_in_ps ps h <> None ->
  eval_smt_arith
    (switch_case_expr
       (List.combine (get_match_results_smt t ps)
          (List.map (fun p => lookup_varlike p h)
             (List.map snd
                (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
       (lookup_varlike ps h)) f
  = match find_first_match
            (List.combine (get_match_results t (eval_sym_state ps f)) t) with
    | Some rule =>
        lookup_varlike (snd (eval_match_action_rule_concrete_mem rule
                               (concretize_mem_ctx mc f) (eval_sym_state ps f))) h
    | None => lookup_varlike (eval_sym_state ps f) h
    end.
Proof.
  intros t mc ps f h Hh. induction t as [| a rest IH].
  - cbn [switch_case_expr get_match_results_smt get_match_results
         List.map List.combine find_first_match].
    symmetry. apply commute_lookup_eval_varlike.
  - destruct a as [[mp action] | [mp action]];
      cbn [get_match_results_smt get_match_results List.map List.combine
           switch_case_expr find_first_match];
      rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl);
      rewrite eval_conditional;
      destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
      [ symmetry; rewrite <- commute_lookup_eval_varlike;
          apply ma_rule_commute_hdr; assumption
      | apply IH
      | symmetry; rewrite <- commute_lookup_eval_varlike;
          apply ma_rule_commute_hdr; assumption
      | apply IH ].
Qed.

Lemma switch_case_sv_match : forall t mc ps f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  eval_smt_arith
    (switch_case_expr
       (List.combine (get_match_results_smt t ps)
          (List.map (fun p => lookup_varlike p sv)
             (List.map snd
                (List.map (fun r => eval_match_action_rule_smt_mem r mc ps) t))))
       (lookup_varlike ps sv)) f
  = match find_first_match
            (List.combine (get_match_results t (eval_sym_state ps f)) t) with
    | Some rule =>
        lookup_varlike (snd (eval_match_action_rule_concrete_mem rule
                               (concretize_mem_ctx mc f) (eval_sym_state ps f))) sv
    | None => lookup_varlike (eval_sym_state ps f) sv
    end.
Proof.
  intros t mc ps f sv Hsv. induction t as [| a rest IH].
  - cbn [switch_case_expr get_match_results_smt get_match_results
         List.map List.combine find_first_match].
    symmetry. apply commute_lookup_eval_varlike.
  - destruct a as [[mp action] | [mp action]];
      cbn [get_match_results_smt get_match_results List.map List.combine
           switch_case_expr find_first_match];
      rewrite (commute_sym_vs_conc_match_pattern mp f ps (eval_sym_state ps f) eq_refl);
      rewrite eval_conditional;
      destruct (eval_smt_bool (eval_match_smt mp ps) f) eqn:E;
      [ symmetry; rewrite <- commute_lookup_eval_varlike;
          apply ma_rule_commute_sv; assumption
      | apply IH
      | symmetry; rewrite <- commute_lookup_eval_varlike;
          apply ma_rule_commute_sv; assumption
      | apply IH ].
Qed.

Theorem transformer_commute_hdr : forall t mc ps f (h : Header),
  is_varlike_in_ps ps h <> None ->
  lookup_varlike (snd (eval_transformer_concrete_mem t
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) h
  = lookup_varlike (eval_sym_state (snd (eval_transformer_smt_mem t mc ps)) f) h.
Proof.
  intros t mc ps f h Hh.
  unfold eval_transformer_smt_mem. cbv zeta. cbn [snd].
  rewrite lookup_state_merge_hdr by assumption.
  rewrite switch_case_hdr_match by assumption.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (find_first_match
              (List.combine (get_match_results t (eval_sym_state ps f)) t));
    cbn [snd]; reflexivity.
Qed.

Theorem transformer_commute_sv : forall t mc ps f (sv : State),
  is_varlike_in_ps ps sv <> None ->
  lookup_varlike (snd (eval_transformer_concrete_mem t
                         (concretize_mem_ctx mc f) (eval_sym_state ps f))) sv
  = lookup_varlike (eval_sym_state (snd (eval_transformer_smt_mem t mc ps)) f) sv.
Proof.
  intros t mc ps f sv Hsv.
  unfold eval_transformer_smt_mem. cbv zeta. cbn [snd].
  rewrite lookup_state_merge_sv by assumption.
  rewrite switch_case_sv_match by assumption.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (find_first_match
              (List.combine (get_match_results t (eval_sym_state ps f)) t));
    cbn [snd]; reflexivity.
Qed.

(* The third map of the state.  Nothing writes it -- [update_all_varlike] runs
   over headers and state variables only -- so this is the [_mem] restatement
   of [ConcreteToSymbolicLemmas.commute_sym_vs_conc_transformer_ctrl_map], and
   unlike the other two it needs no domain hypothesis. *)
Theorem transformer_commute_ctrl : forall t mc ps f,
  t_ctrl_map (snd (eval_transformer_concrete_mem t
                     (concretize_mem_ctx mc f) (eval_sym_state ps f)))
  = t_ctrl_map (eval_sym_state (snd (eval_transformer_smt_mem t mc ps)) f).
Proof.
  intros t mc ps f.
  rewrite ctrl_plane_invariant_transformer_mem.
  unfold eval_transformer_smt_mem, eval_sym_state. cbv zeta.
  cbn [snd program_state_mapper t_ctrl_map].
  reflexivity.
Qed.

(* ====================================================================== *)
(* 6. THE CONCRETE SIDE IS A CONGRUENCE FOR POINTWISE MEMORY AGREEMENT.   *)
(*                                                                        *)
(* Levels 4 and 5 relate the two evaluators only PER KEY, and section 4's *)
(* header explains why that is forced.  The consequence shows up one      *)
(* level higher, at the network: after one module the concrete memory is  *)
(* no longer literally [PMap.map] of the symbolic one, only equal to it   *)
(* at every key.  For the induction to take another step, the concrete    *)
(* evaluator has to be insensitive to that difference.                    *)
(*                                                                        *)
(* It is, and for a reason that is easy to check rather than hope for:    *)
(* memory is only ever touched through [!!] and [PMap.set].  Nothing      *)
(* looks at the key SET -- the one thing on which the two sides differ.   *)
(* (The one exception is [mem_extents_in_bounds_concrete], which folds    *)
(* over [pmap_keys]; it is handled separately, where it is used.)         *)
(* ====================================================================== *)

Definition mc_agree (mc1 mc2 : ConcreteMemCtx) : Prop :=
  (forall k, (mc_mem mc1) !! k = (mc_mem mc2) !! k) /\
  (forall k, (mc_extent mc1) !! k = (mc_extent mc2) !! k).

Lemma mc_agree_refl : forall mc, mc_agree mc mc.
Proof. intros mc. split; intros k; reflexivity. Qed.

Lemma bump_extent_concrete_cong : forall mc1 mc2 r off,
  mc_agree mc1 mc2 ->
  mc_agree (bump_extent_concrete mc1 r off) (bump_extent_concrete mc2 r off).
Proof.
  intros mc1 mc2 r off [Hm He].
  unfold bump_extent_concrete, set_mc_extent. split; cbn [mc_mem mc_extent].
  - exact Hm.
  - intros k. rewrite !PMap.gsspec.
    destruct (Coqlib.peq k (unwrap r)); [ rewrite He | ]; apply He || reflexivity.
Qed.

Lemma bump_extent_span_fold_cong : forall l mc1 mc2 r base,
  mc_agree mc1 mc2 ->
  mc_agree
    (List.fold_left (fun acc i => bump_extent_concrete acc r (byte_addr base i)) l mc1)
    (List.fold_left (fun acc i => bump_extent_concrete acc r (byte_addr base i)) l mc2).
Proof.
  intros l. induction l as [| i rest IH]; intros mc1 mc2 r base H;
    cbn [List.fold_left]; [ exact H |].
  apply IH. apply bump_extent_concrete_cong. exact H.
Qed.

Lemma bump_extent_span_concrete_cong : forall mc1 mc2 r base n,
  mc_agree mc1 mc2 ->
  mc_agree (bump_extent_span_concrete mc1 r base n)
           (bump_extent_span_concrete mc2 r base n).
Proof.
  intros. unfold bump_extent_span_concrete. apply bump_extent_span_fold_cong.
  assumption.
Qed.

Lemma eval_hdr_op_assign_concrete_mem_cong : forall op mc1 mc2 ps,
  mc_agree mc1 mc2 ->
  mc_agree (fst (eval_hdr_op_assign_concrete_mem op mc1 ps))
           (fst (eval_hdr_op_assign_concrete_mem op mc2 ps))
  /\ snd (eval_hdr_op_assign_concrete_mem op mc1 ps)
     = snd (eval_hdr_op_assign_concrete_mem op mc2 ps).
Proof.
  intros op mc1 mc2 ps H.
  pose proof H as [Hm He].
  destruct op as [ fn ty a1 a2 tgt | fn ty a1 a2 tgt
                 | fr t a tgt | fr t a tgt
                 | ty r off tgt | ty r off tgt
                 | ty r off val ];
    cbn [eval_hdr_op_assign_concrete_mem fst snd].
  1-4: split; [ exact H | reflexivity ].
  (* the two loads: the value read is the same, so the state is the same *)
  1-2: split; [ apply bump_extent_span_concrete_cong; exact H
              | rewrite Hm; reflexivity ].
  (* the store: same old contents, so the same new contents *)
  split; [| reflexivity ].
  apply bump_extent_span_concrete_cong.
  unfold set_mc_mem. split; cbn [mc_mem mc_extent]; [| exact He ].
  intros k. rewrite !PMap.gsspec.
  destruct (Coqlib.peq k (unwrap r)); [ rewrite Hm; reflexivity | apply Hm ].
Qed.

Lemma eval_hdr_op_list_concrete_mem_cong : forall hol mc1 mc2 ps,
  mc_agree mc1 mc2 ->
  mc_agree (fst (eval_hdr_op_list_concrete_mem hol mc1 ps))
           (fst (eval_hdr_op_list_concrete_mem hol mc2 ps))
  /\ snd (eval_hdr_op_list_concrete_mem hol mc1 ps)
     = snd (eval_hdr_op_list_concrete_mem hol mc2 ps).
Proof.
  intros hol. induction hol as [| op rest IH]; intros mc1 mc2 ps H.
  - split; [ exact H | reflexivity ].
  - rewrite !eval_hdr_op_list_concrete_mem_cons.
    destruct (eval_hdr_op_assign_concrete_mem_cong op mc1 mc2 ps H) as [Ha Hs].
    rewrite Hs. apply IH. exact Ha.
Qed.

Lemma eval_match_action_rule_concrete_mem_cong : forall rule mc1 mc2 ps,
  mc_agree mc1 mc2 ->
  mc_agree (fst (eval_match_action_rule_concrete_mem rule mc1 ps))
           (fst (eval_match_action_rule_concrete_mem rule mc2 ps))
  /\ snd (eval_match_action_rule_concrete_mem rule mc1 ps)
     = snd (eval_match_action_rule_concrete_mem rule mc2 ps).
Proof.
  intros [[mp action] | [mp action]] mc1 mc2 ps H;
    cbn [eval_match_action_rule_concrete_mem eval_seq_rule_concrete_mem
         eval_par_rule_concrete_mem];
    destruct (eval_match_concrete mp ps);
    solve [ apply eval_hdr_op_list_concrete_mem_cong; exact H
          | cbn [fst snd]; split; [ exact H | reflexivity ] ].
Qed.

Theorem eval_transformer_concrete_mem_cong : forall t mc1 mc2 ps,
  mc_agree mc1 mc2 ->
  mc_agree (fst (eval_transformer_concrete_mem t mc1 ps))
           (fst (eval_transformer_concrete_mem t mc2 ps))
  /\ snd (eval_transformer_concrete_mem t mc1 ps)
     = snd (eval_transformer_concrete_mem t mc2 ps).
Proof.
  intros t mc1 mc2 ps H.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (find_first_match
              (List.combine (get_match_results t ps) t)) as [rule |].
  - apply eval_match_action_rule_concrete_mem_cong. exact H.
  - cbn [fst snd]. split; [ exact H | reflexivity ].
Qed.
