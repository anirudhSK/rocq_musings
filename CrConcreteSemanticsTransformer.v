(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import ListUtils.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From MyProject Require Import Integers.

(* Apply binary operation [f] at type [ty]: both operands must already be typed
   [ty] (else the underlying [*_at] yields ErrorVal); result is typed [ty]. *)
Definition apply_bin_op_of (f : BinaryOp) (ty : CrIntType) (v1 v2 : CrVal) : CrVal :=
  match f with
  | AddOp => add_at  ty v1 v2
  | SubOp => sub_at  ty v1 v2
  | AndOp => and_at  ty v1 v2
  | OrOp  => or_at   ty v1 v2
  | XorOp => xor_at  ty v1 v2
  | MulOp => mul_at  ty v1 v2
  | DivOp => divu_at ty v1 v2
  | ModOp => modu_at ty v1 v2
  end.

(* Reinterpret [v] from int type [from] to [to] (the operand must be typed
   [from], else ErrorVal). *)
Definition apply_cast (from to : CrIntType) (v : CrVal) : CrVal := cast from to v.

(* Evaluate an operand at the expected type [ty]: a constant adopts [ty]; a
   variable carries whatever type it was stored with (which the op then checks). *)
Definition lookup_concrete (ty : CrIntType) (arg : Operand) (ps : ConcreteTransformerState) : CrVal :=
  match arg with
  | OpCtrlPlane c => lookup_varlike_map (@map_from_ps Ctrl _ _ ps) c
  | OpHeader h    => lookup_varlike_map (@map_from_ps Header _ _ ps) h
  | OpConst n     => mk_int ty (unsigned n)
  | OpStateful s  => lookup_varlike_map (@map_from_ps State _ _ ps) s
  end.

Definition eval_hdr_op_expr_concrete (op : HdrOp) (ps : ConcreteTransformerState) : CrVal :=
  match op with
  | StatefulOp f ty arg1 arg2 _ => apply_bin_op_of f ty (lookup_concrete ty arg1 ps) (lookup_concrete ty arg2 ps)
  | StatelessOp f ty arg1 arg2 _ => apply_bin_op_of f ty (lookup_concrete ty arg1 ps) (lookup_concrete ty arg2 ps)
  | CastStateOp from to arg _ => apply_cast from to (lookup_concrete from arg ps)
  | CastHeaderOp from to arg _ => apply_cast from to (lookup_concrete from arg ps)
  (* Memory ops are not expressions: a load's result depends on the memory, not
     just the state, and a store produces no value at all.  They are handled in
     [eval_hdr_op_assign_concrete_mem] below.  Returning ErrorVal here keeps
     this function total for the memory-free entry points. *)
  | LoadOp _ _ _ _ | StoreOp _ _ _ _ => ErrorVal
  end.

(* ------------------------------------------------------------------ *)
(* Memory ops.

   An offset is an address, not a value: it is read at whatever width it was
   stored and then normalised to u64 by [as_offset], so that extent
   comparisons (which go through [CrVal.ltb], and so require both sides to
   carry the same type) always compare like with like.  The symbolic mirror is
   [SmtBitSlice 0 64], which is exactly what [slice_val 0 64] computes. *)
Definition as_offset (v : CrVal) : CrVal := slice_val 0 64 v.

(* Grow the region's recorded access extent to cover [off].  Every access
   updates it, in bounds or not: reaching past a region's end is precisely the
   difference between two programs that this is here to expose. *)
Definition bump_extent_concrete (mc : ConcreteMemCtx) (r : MemRegion) (off : CrVal)
    : ConcreteMemCtx :=
  let k := unwrap r in
  let prev := (mc_extent mc) !! k in
  set_mc_extent mc (PMap.set k (if CrVal.ltb prev off then off else prev) (mc_extent mc)).

(* Every cell an access covers counts towards the extent, not just its base:
   a u64 load at the last byte of a region reaches seven bytes past it, and
   that is exactly the difference the extent exists to expose. *)
Definition bump_extent_span_concrete (mc : ConcreteMemCtx) (r : MemRegion)
    (base : CrVal) (n : nat) : ConcreteMemCtx :=
  List.fold_left (fun acc i => bump_extent_concrete acc r (byte_addr base i))
    (List.seq 0 n) mc.

Definition eval_hdr_op_assign_concrete_mem
  (op : HdrOp) (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
  match op with
  | StatefulOp _ _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_concrete op ps))
  | StatelessOp _ _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_concrete op ps))
  | CastStateOp _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_concrete op ps))
  | CastHeaderOp _ _ _ target =>
        (mc, update_varlike ps target (eval_hdr_op_expr_concrete op ps))
  | LoadOp ty r off target =>
      let o := as_offset (lookup_concrete u64 off ps) in
      (* [it_bytes ty] cells, little-endian.  A cell that is out of bounds or
         was never written reads ErrorVal, and the assembly propagates that to
         the whole value -- same observable behaviour as before (matches
         nothing, emits no bits), and in exact lockstep with the symbolic
         mirror, which gets it from [SmtArrSel] and [SmtCast]. *)
      (bump_extent_span_concrete mc r o (it_bytes ty),
       update_varlike ps target (ld_val ty ((mc_mem mc) !! (unwrap r)) o))
  | StoreOp ty r off val =>
      let o := as_offset (lookup_concrete u64 off ps) in
      let v := apply_cast ty ty (lookup_concrete ty val ps) in
      let region' := st_val ty ((mc_mem mc) !! (unwrap r)) o v in
      (bump_extent_span_concrete
         (set_mc_mem mc (PMap.set (unwrap r) region' (mc_mem mc))) r o (it_bytes ty),
       ps)
  end.

(* ------------------------------------------------------------------ *)
(* Memory-free evaluation.

   This is the transformer-level semantics: the domain of [CaracaraProgram]
   and of [SmtQuery]'s checker, where memory does not exist because a
   [CaracaraProgram] has nowhere to declare a region.  It is a separate
   recursion from the [_mem] one above rather than [snd (... empty ...)]: an
   op's effect on memory persists into the next op, so specialising the
   threading version to an empty memory is not definitionally the same
   function, and every induction over an action list would need an invariant
   about the memory staying empty to say otherwise.

   The two must agree on the non-memory ops, and they do -- both delegate to
   [eval_hdr_op_expr_concrete].  On the memory ops this one takes the answer
   the threading version gives for an undeclared region: a load yields
   ErrorVal, a store does nothing. *)
Definition eval_hdr_op_assign_concrete (op : HdrOp) (ps: ConcreteTransformerState) : ConcreteTransformerState :=
  match op with
  | StatefulOp _ _ _ _ target =>
        let op_output := eval_hdr_op_expr_concrete op ps in update_varlike ps target op_output
  | StatelessOp _ _ _ _ target =>
        let op_output := eval_hdr_op_expr_concrete op ps in update_varlike ps target op_output
  | CastStateOp _ _ _ target =>
        let op_output := eval_hdr_op_expr_concrete op ps in update_varlike ps target op_output
  | CastHeaderOp _ _ _ target =>
        let op_output := eval_hdr_op_expr_concrete op ps in update_varlike ps target op_output
  | LoadOp _ _ _ target => update_varlike ps target ErrorVal
  | StoreOp _ _ _ _ => ps
  end.

Definition eval_cmp_concrete (op : CmpOp) (v1 v2 : CrVal) : bool :=
  match op with
  | CmpEq => CrVal.eqb v1 v2
  | CmpGt => CrVal.ltb v2 v1
  | CmpLt => CrVal.ltb v1 v2
  end.

Definition eval_match_concrete (match_pattern : MatchPattern) (ps : ConcreteTransformerState) : bool :=
  List.forallb (fun '(h, c, v) =>
  let v' := match v with
  | MatchConst k' ty => mk_int ty (unsigned k')
  | MatchHeader h' => (lookup_varlike ps h')
  end in
  eval_cmp_concrete c (lookup_varlike ps h) v') match_pattern.

(* Define evaluation over a list of HdrOp *)
(* The list is evaluated left to right: the head of the list executes first. *)
Definition eval_hdr_op_list_concrete_mem (hol : list HdrOp)
  (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
  List.fold_left (fun (acc : ConcreteMemCtx * ConcreteTransformerState) op =>
    let (mc', ps') := acc in eval_hdr_op_assign_concrete_mem op mc' ps') hol (mc, ps).

Definition eval_hdr_op_list_concrete (hol : list HdrOp) (ps : ConcreteTransformerState) : ConcreteTransformerState :=
  List.fold_left (fun acc op => eval_hdr_op_assign_concrete op acc) hol ps.

(* Peel one op off the fold.  The accumulator is a pair, so the [fold_left]
   step does not reduce on its own; every induction over an action list needs
   this to expose it. *)
Lemma eval_hdr_op_list_concrete_mem_cons :
  forall a hol mc c,
    eval_hdr_op_list_concrete_mem (a :: hol) mc c =
    eval_hdr_op_list_concrete_mem hol
      (fst (eval_hdr_op_assign_concrete_mem a mc c))
      (snd (eval_hdr_op_assign_concrete_mem a mc c)).
Proof.
  intros. unfold eval_hdr_op_list_concrete_mem. simpl.
  destruct (eval_hdr_op_assign_concrete_mem a mc c). reflexivity.
Qed.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_concrete_mem (srule : SeqRule)
  (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
  match srule with
  | SeqCtr match_pattern action =>
      if (eval_match_concrete match_pattern ps) then
        eval_hdr_op_list_concrete_mem action mc ps
      else
        (mc, ps)
  end.

Definition eval_seq_rule_concrete (srule : SeqRule) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
  match srule with
  | SeqCtr match_pattern action =>
      if (eval_match_concrete match_pattern ps) then
        eval_hdr_op_list_concrete action ps
      else
        ps
  end.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel *)
(* This is identical to eval_seq_rule,
   except that the action is a list with some conditions: the targets are all unique
   these conditions are realized using subset types, that's why we need proj1_sig *)
(* [ParRule] carries no memory: [CrDslProperties.no_mem_ops_in_parb] rejects a
   program whose parallel rules contain loads or stores, so threading memory
   through here would only be dead weight.  See the comment on
   [CrTransformer.extract_targets] for why. *)
Definition eval_par_rule_concrete_mem (prule : ParRule)
  (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
  match prule with
  | ParCtr match_pattern action =>
      if (eval_match_concrete match_pattern ps) then
        eval_hdr_op_list_concrete_mem (proj1_sig action) mc ps
      else
        (mc, ps)
  end.

Definition eval_par_rule_concrete (prule : ParRule) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
  match prule with
  | ParCtr match_pattern action =>
      if (eval_match_concrete match_pattern ps) then
        eval_hdr_op_list_concrete (proj1_sig action) ps
      else
        ps
  end.

(* Function to evaluate a match-action rule,
   meaning header ops within an action are evaluated
   according to the type of the rule (sequential or parallel) *)
Definition eval_match_action_rule_concrete_mem (rule : MatchActionRule)
  (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
  match rule with
  | Seq srule => eval_seq_rule_concrete_mem srule mc ps
  | Par prule => eval_par_rule_concrete_mem prule mc ps
  end.

Definition eval_match_action_rule_concrete (rule : MatchActionRule) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
  match rule with
  | Seq srule => eval_seq_rule_concrete srule ps
  | Par prule => eval_par_rule_concrete prule ps
  end.

(* lookup header against each of the match-action rules in t to see if there is a match *)
Definition get_match_results (t : Transformer) (ps : ConcreteTransformerState) : list bool :=
  List.map (fun rule =>
                     match rule with
                       | Seq (SeqCtr match_pattern _) =>
                           eval_match_concrete match_pattern ps
                       | Par (ParCtr match_pattern _) =>
                           eval_match_concrete match_pattern ps
                     end) t.

(* Function to evaluate a transformer, which is a list of match-action rules *)
Definition eval_transformer_concrete_mem (t : Transformer)
  (mc : ConcreteMemCtx) (ps : ConcreteTransformerState)
  : ConcreteMemCtx * ConcreteTransformerState :=
    (* Combine match results with the rules to find the first matching rule *)
    let rules_with_match_results := List.combine (get_match_results t ps) t in
    let first_match := find_first_match rules_with_match_results in (* find_first_match is in ListUtils *)
        match first_match with
        | None => (mc, ps)  (* no match, return unchanged state *)
        | Some (rule) => eval_match_action_rule_concrete_mem rule mc ps (* evaluate the rule and update state accordingly *)
      end.

Definition eval_transformer_concrete (t : Transformer) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
    let rules_with_match_results := List.combine (get_match_results t ps) t in
    let first_match := find_first_match rules_with_match_results in
        match first_match with
        | None => ps
        | Some (rule) => eval_match_action_rule_concrete rule ps
      end.

(* Function to evaluate a Caracara program *)
Definition eval_cr_program_concrete (p : CaracaraProgram) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
  match p with
  | CaracaraProgramDef _ _ _ t => eval_transformer_concrete t ps
  (* TODO: Maybe do something with the various lists of headers, states, and ctrls *)
  end.

(* Could be useful to have a proof about sequential vs parallel *)
(* Relax notion of local state *)
(* filter database = naive program *)
