From MyProject Require Import CrTransformer.
From MyProject Require Import CrVal.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From Stdlib Require Import ZArith.
From MyProject Require Import CrProgramState.
From MyProject Require Import Maps.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From Stdlib Require Import List.
Import ListNotations.

(* Convert an operand to its SmtArithExpr at the expected type [ty]: a constant
   adopts [ty]; a variable carries its stored (symbolic) value. *)
Definition lookup_smt (ty : CrIntType) (arg : Operand) (ps : SymbolicTransformerState) : SmtArithExpr :=
  match arg with
  | OpCtrlPlane c => lookup_varlike_map (@map_from_ps Ctrl _ _ ps) c
  | OpHeader h    => lookup_varlike_map (@map_from_ps Header _ _ ps) h
  | OpConst n     => SmtArithConst n ty
  | OpStateful s  => lookup_varlike_map (@map_from_ps State _ _ ps) s
  end.

(* Symbolic mirror of [apply_bin_op_of]: the typed SMT op at [ty]; operands are
   already typed [ty] (looked up at [ty]), so eval type-checks like the concrete. *)
Definition smt_binop_of (f : BinaryOp) (ty : CrIntType) (e1 e2 : SmtArithExpr) : SmtArithExpr :=
  match f with
  | AddOp => SmtBitAdd ty e1 e2
  | SubOp => SmtBitSub ty e1 e2
  | AndOp => SmtBitAnd ty e1 e2
  | OrOp  => SmtBitOr  ty e1 e2
  | XorOp => SmtBitXor ty e1 e2
  | MulOp => SmtBitMul ty e1 e2
  | DivOp => SmtBitDiv ty e1 e2
  | ModOp => SmtBitMod ty e1 e2
  end.

(* Symbolic mirror of [apply_cast]. *)
Definition smt_cast (from to : CrIntType) (e : SmtArithExpr) : SmtArithExpr :=
  SmtCast from to e.

(* [SmtArithExpr] has no ErrorVal literal.  A cast of the uninitialized value
   to a different width is the canonical way to denote one: [CrVal.cast]
   rejects both the type mismatch and the non-integer operand, so this
   evaluates to ErrorVal under every valuation. *)
Definition smt_error : SmtArithExpr := SmtCast u8 u16 SmtUninit.

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) (ps : SymbolicTransformerState) : SmtArithExpr :=
    match h with
    | StatefulOp f ty arg1 arg2 _ => smt_binop_of f ty (lookup_smt ty arg1 ps) (lookup_smt ty arg2 ps)
    | StatelessOp f ty arg1 arg2 _ => smt_binop_of f ty (lookup_smt ty arg1 ps) (lookup_smt ty arg2 ps)
    | CastStateOp from to arg _ => smt_cast from to (lookup_smt from arg ps)
    | CastHeaderOp from to arg _ => smt_cast from to (lookup_smt from arg ps)
    (* Mirrors [eval_hdr_op_expr_concrete]: memory ops are not expressions of
       the state alone. *)
    | LoadOp _ _ _ _ | StoreOp _ _ _ _ => smt_error
    end.

(* ------------------------------------------------------------------ *)
(* Memory ops.  Mirror of the concrete side, expression for expression.

   [smt_as_offset] is the mirror of [as_offset]: [SmtBitSlice 0 64] evaluates
   to [slice_val 0 64], which normalises any integer to u64 and anything else
   to ErrorVal. *)
Definition smt_as_offset (e : SmtArithExpr) : SmtArithExpr := SmtBitSlice 0 64 e.

Definition smt_byte_addr (base : SmtArithExpr) (i : nat) : SmtArithExpr :=
  SmtBitAdd u64 base (SmtArithConst (mask_width W64 (Z.of_nat i)) u64).

(* Mirror of [bump_extent_concrete]: count bytes required by the program. *)
Definition bump_extent_smt (mc : SymbolicMemCtx) (r : MemRegion) (off : SmtArithExpr)
    : SymbolicMemCtx :=
  let k := unwrap r in
  let prev := (mc_extent mc) !! k in
  let reach := smt_byte_addr off 1 in
  set_mc_extent mc
    (PMap.set k (SmtConditional (SmtBoolLt prev reach) reach prev) (mc_extent mc)).

(* ------------------------------------------------------------------ *)
(* Multi-byte access, the mirror of [CrVal.ld_val] / [st_val] / [byte_*].
   Each definition below lines up node-for-node with its concrete counterpart:
   [SmtArrSel] with [ld_cell], [SmtCast] with [cast], [SmtBitMul]/[SmtBitOr]
   with [mul_at]/[or_at], [SmtBitSlice] with [slice_val].  Keep them in step --
   a divergence here is invisible to the Coq development, which only relates
   the two through [eval_smt_*]. *)

Definition smt_byte_of_val (v : SmtArithExpr) (i : nat) : SmtArithExpr :=
  SmtCast u64 u8 (SmtBitSlice (8 * i) (8 * i + 8) v).

Definition smt_byte_into_val (b : SmtArithExpr) (i : nat) : SmtArithExpr :=
  SmtBitMul u64 (SmtCast u8 u64 b)
    (SmtArithConst (mask_width W64 (2 ^ (8 * Z.of_nat i))) u64).

Definition smt_ld_val (ty : CrIntType) (a : SmtArrExpr) (base : SmtArithExpr)
    : SmtArithExpr :=
  SmtCast u64 ty
    (List.fold_left
      (fun acc i =>
        SmtBitOr u64 acc (smt_byte_into_val (SmtArrSel a (smt_byte_addr base i)) i))
      (List.seq 0 (it_bytes ty)) (SmtArithConst (mask_width W64 0) u64)).

Definition smt_st_val (ty : CrIntType) (a : SmtArrExpr)
    (base v : SmtArithExpr) : SmtArrExpr :=
  List.fold_left
    (fun acc i => SmtArrSt acc (smt_byte_addr base i) (smt_byte_of_val v i))
    (List.seq 0 (it_bytes ty)) a.

Definition bump_extent_span_smt (mc : SymbolicMemCtx) (r : MemRegion)
    (base : SmtArithExpr) (n : nat) : SymbolicMemCtx :=
  List.fold_left (fun acc i => bump_extent_smt acc r (smt_byte_addr base i))
    (List.seq 0 n) mc.

Definition eval_hdr_op_assign_smt_mem
  (ho : HdrOp) (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
    match ho with
    | StatefulOp _ _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_smt ho ps))
    | StatelessOp _ _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_smt ho ps))
    | CastStateOp _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_smt ho ps))
    | CastHeaderOp _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_smt ho ps))
    | LoadOp ty r off target =>
        let o := smt_as_offset (lookup_smt u64 off ps) in
        (bump_extent_span_smt mc r o (it_bytes ty),
         update_varlike ps target
           (smt_ld_val ty ((mc_mem mc) !! (unwrap r)) o))
    | StoreOp ty r off val =>
        let o := smt_as_offset (lookup_smt u64 off ps) in
        let v := smt_cast ty ty (lookup_smt ty val ps) in
        let region' := smt_st_val ty ((mc_mem mc) !! (unwrap r)) o v in
        (bump_extent_span_smt (set_mc_mem mc (PMap.set (unwrap r) region' (mc_mem mc)))
           r o (it_bytes ty), ps)
    end.

(* Merge two memory contexts under a condition, the memory counterpart of the
   [SmtConditional] merge [eval_seq_rule_smt] applies to headers and state
   vars.  Regions merge with [SmtArrIte] because [SmtConditional] only builds
   arith expressions.  Both maps carry the same default on either side (an
   undeclared region, extent zero), so only the keys present need merging. *)
Definition pmap_keys {T : Type} (m : PMap.t T) : list positive :=
  List.map fst (PTree.elements (snd m)).

Definition merge_mem_ctx_smt (c : SmtBoolExpr) (mc1 mc2 : SymbolicMemCtx)
    : SymbolicMemCtx :=
  let ks := pmap_keys (mc_mem mc1) ++ pmap_keys (mc_mem mc2)
            ++ pmap_keys (mc_extent mc1) ++ pmap_keys (mc_extent mc2) in
  {| mc_mem := List.fold_left
       (fun acc k => PMap.set k (SmtArrIte c ((mc_mem mc1) !! k) ((mc_mem mc2) !! k)) acc)
       ks (mc_mem mc2);
     mc_extent := List.fold_left
       (fun acc k => PMap.set k (SmtConditional c ((mc_extent mc1) !! k) ((mc_extent mc2) !! k)) acc)
       ks (mc_extent mc2) |}.

(* n-ary version, the memory counterpart of [switch_case_expr]. *)
Fixpoint switch_case_arr (cases : list (SmtBoolExpr * SmtArrExpr)) (default_case : SmtArrExpr)
    : SmtArrExpr :=
  match cases with
  | [] => default_case
  | (cond, a) :: rest => SmtArrIte cond a (switch_case_arr rest default_case)
  end.

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: SymbolicTransformerState) (f : SmtValuation) : ConcreteTransformerState :=
   let sym_eval := fun e => eval_smt_arith e f in
   program_state_mapper sym_eval sym_eval sym_eval s.

(* ------------------------------------------------------------------ *)
(* Memory-free evaluation: the mirror of
   [CrConcreteSemanticsTransformer.eval_hdr_op_assign_concrete] and friends.
   See the note there for why this is a separate recursion rather than the
   threading version specialised to an empty memory. *)
Definition eval_hdr_op_assign_smt (ho : HdrOp) (ps: SymbolicTransformerState) : SymbolicTransformerState :=
    match ho with
    | StatefulOp _ _ _ _ target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_varlike ps target op_output
    | StatelessOp _ _ _ _ target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_varlike ps target op_output
    | CastStateOp _ _ _ target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_varlike ps target op_output
    | CastHeaderOp _ _ _ target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_varlike ps target op_output
    | LoadOp _ _ _ target => update_varlike ps target smt_error
    | StoreOp _ _ _ _ => ps
    end.

(* Define evaluation over a list of HdrOp *)
(* The list is evaluated left to right: the head of the list executes first. *)
Definition eval_hdr_op_list_smt_mem (hol : list HdrOp)
  (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
  List.fold_left (fun (acc : SymbolicMemCtx * SymbolicTransformerState) op =>
    let (mc', ps') := acc in eval_hdr_op_assign_smt_mem op mc' ps') hol (mc, ps).

Definition eval_hdr_op_list_smt (hol : list HdrOp) (ps : SymbolicTransformerState) : SymbolicTransformerState :=
  List.fold_left (fun acc op => eval_hdr_op_assign_smt op acc) hol ps.

Definition eval_cmp_smt (op : CmpOp) (e1 e2 : SmtArithExpr) : SmtBoolExpr :=
  match op with
  | CmpEq => SmtBoolEq e1 e2
  | CmpGt => SmtBoolLt e2 e1
  | CmpLt => SmtBoolLt e1 e2
  end.

Definition eval_match_smt (match_pattern : MatchPattern) (ps : SymbolicTransformerState) : SmtBoolExpr :=
  (* For every list element, check if the Header's current value (determined by ps) equals the match value *)
  (* Note that because SmtBoolAnd is associative and commutative, both fold_left and fold_right give the same answer. *)
  List.fold_right (fun '(h, c, v) acc =>
    let v' := match v with
    | MatchConst k' ty => SmtArithConst k' ty
    | MatchHeader h' => lookup_varlike ps h'
    end in
    SmtBoolAnd (eval_cmp_smt c (lookup_varlike ps h) v') acc) SmtTrue match_pattern.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_smt_mem (srule : SeqRule)
  (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
  match srule with
  | SeqCtr match_pattern action =>
        let condition := eval_match_smt match_pattern ps in

        (* Second, evaluate all the hdr_ops contained in the action to get a new intermediate state ps' from ps *)
        let r := eval_hdr_op_list_smt_mem (action) mc ps in
        let mc' := fst r in
        let ps' := snd r in

          (* Third, return the updated program state:
             ctrl_plane_map: same as what it was in the original state ps,
             header_map: for every header, its value is SmtConditional condition (value in ps') (value in ps)
             state_map: similar to header_map
             memory: merged the same way, but with SmtArrIte, since
             SmtConditional only builds arith expressions *)
          (merge_mem_ctx_smt condition mc' mc,
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s)))
  end.

Definition eval_seq_rule_smt (srule : SeqRule) (ps : SymbolicTransformerState) : (SymbolicTransformerState) :=
  match srule with
  | SeqCtr match_pattern action =>
        let condition := eval_match_smt match_pattern ps in
        let ps' := eval_hdr_op_list_smt (action) ps in
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s))
  end.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel.
   This is identical to eval_seq_rule, except that the action is a list with some conditions: the targets are all unique
   these conditions are realized using subset types, that's why we need proj1_sig *)
Definition eval_par_rule_smt_mem (prule : ParRule)
  (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
  match prule with
  | ParCtr match_pattern action =>
        (* First evaluate the match pattern by itself against the original state ps *)
        let condition := eval_match_smt match_pattern ps in

        (* Second, evaluate all the hdr_ops contained in the action to get a new intermediate state ps' from ps *)
        let r := eval_hdr_op_list_smt_mem (proj1_sig action) mc ps in
        let mc' := fst r in
        let ps' := snd r in

          (* Third, return the updated program state:
             ctrl_plane_map: same as what it was in the original state ps,
             header_map: for every header, its value is SmtConditional condition (value in ps') (value in ps)
             state_map: similar to header_map *)
          (merge_mem_ctx_smt condition mc' mc,
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s)))
  end.

Definition eval_par_rule_smt (prule : ParRule) (ps : SymbolicTransformerState) : (SymbolicTransformerState) :=
  match prule with
  | ParCtr match_pattern action =>
        let condition := eval_match_smt match_pattern ps in
        let ps' := eval_hdr_op_list_smt (proj1_sig action) ps in
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s))
  end.

Definition eval_match_action_rule_smt_mem (rule : MatchActionRule)
  (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
  match rule with
  | Seq srule => eval_seq_rule_smt_mem srule mc ps
  | Par prule => eval_par_rule_smt_mem prule mc ps
  end.

Definition eval_match_action_rule_smt (rule : MatchActionRule) (ps : SymbolicTransformerState) : (SymbolicTransformerState) :=
  match rule with
  | Seq srule => eval_seq_rule_smt srule ps
  | Par prule => eval_par_rule_smt prule ps
  end.

Fixpoint switch_case_expr (cases : list (SmtBoolExpr * SmtArithExpr)) (default_case : SmtArithExpr) : SmtArithExpr :=
  match cases with
  | [] => default_case
  | (cond, expr) :: rest =>
      SmtConditional cond expr (switch_case_expr rest default_case)
  end.

(* Compute match results for each match pattern (one embedded in each rule) *)
Definition get_match_results_smt (t : Transformer) (ps : SymbolicTransformerState) : list SmtBoolExpr :=
  List.map (fun rule =>
    match rule with
    | Seq (SeqCtr match_pattern _) => eval_match_smt match_pattern ps
    | Par (ParCtr match_pattern _) => eval_match_smt match_pattern ps
    end) t.

Definition eval_transformer_smt_mem (t : Transformer)
  (mc : SymbolicMemCtx) (ps : SymbolicTransformerState)
  : SymbolicMemCtx * SymbolicTransformerState :=
  (* get all future states, one for each rule; each carries its own memory *)
  let results        := List.map (fun rule => eval_match_action_rule_smt_mem rule mc ps) t in
  let mem_ctxs       := List.map fst results in
  let program_states := List.map snd results in
  let conds          := get_match_results_smt t ps in
  (* map a header to all possible future exprs, one for each future state *)
  let header_exprs   := fun (h : Header) => List.map (fun ps => lookup_varlike ps h) program_states in
  (* same as above, for state variables *)
  let state_vars     := fun (s : State) => List.map (fun ps => lookup_varlike ps s) program_states in
  (* ...and for memory.  Same first-match-wins shape as [switch_case_expr],
     but over [SmtArrIte]; the extents merge as ordinary arith expressions.
     Keys come from every branch plus the incoming context, so a region that
     only one rule touches is still merged against the others. *)
  let keys := List.concat (List.map (fun m => pmap_keys (mc_mem m)) mem_ctxs)
              ++ List.concat (List.map (fun m => pmap_keys (mc_extent m)) mem_ctxs)
              ++ pmap_keys (mc_mem mc) ++ pmap_keys (mc_extent mc) in
  let mem' := List.fold_left
    (fun acc k => PMap.set k
      (switch_case_arr (List.combine conds (List.map (fun m => (mc_mem m) !! k) mem_ctxs))
                       ((mc_mem mc) !! k)) acc)
    keys (mc_mem mc) in
  let ext' := List.fold_left
    (fun acc k => PMap.set k
      (switch_case_expr (List.combine conds (List.map (fun m => (mc_extent m) !! k) mem_ctxs))
                        ((mc_extent mc) !! k)) acc)
    keys (mc_extent mc) in
  ({| mc_mem := mem'; mc_extent := ext' |},
    update_all_varlike
    (update_all_varlike ps (fun h => switch_case_expr (List.combine (get_match_results_smt t ps) (header_exprs h)) (lookup_varlike ps h)))
    (fun s => switch_case_expr (List.combine (get_match_results_smt t ps) (state_vars s)) (lookup_varlike ps s))).

Definition eval_transformer_smt (t : Transformer) (ps : SymbolicTransformerState) : SymbolicTransformerState :=
  let program_states := List.map (fun rule => eval_match_action_rule_smt rule ps) t in
  let header_exprs   := fun (h : Header) => List.map (fun ps => lookup_varlike ps h) program_states in
  let state_vars     := fun (s : State) => List.map (fun ps => lookup_varlike ps s) program_states in
    update_all_varlike
    (update_all_varlike ps (fun h => switch_case_expr (List.combine (get_match_results_smt t ps) (header_exprs h)) (lookup_varlike ps h)))
    (fun s => switch_case_expr (List.combine (get_match_results_smt t ps) (state_vars s)) (lookup_varlike ps s)).