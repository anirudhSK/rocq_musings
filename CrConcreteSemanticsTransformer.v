(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import ListUtils.
From MyProject Require Import CrVal.
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
  end.

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
Definition eval_hdr_op_list_concrete (hol : list HdrOp) (ps : ConcreteTransformerState) : ConcreteTransformerState :=
  List.fold_left (fun acc op => eval_hdr_op_assign_concrete op acc) hol ps.

(* Evalaute a single HdrOp conditionally based on a match_pattern *)
Definition eval_hdr_op_assign_concrete_conditional
  (match_pattern : MatchPattern)
  (ho : HdrOp)
  (ps : ConcreteTransformerState)
  : ConcreteTransformerState :=
  if eval_match_concrete match_pattern ps then
    eval_hdr_op_assign_concrete ho ps
  else
    ps.
 
(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
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
Definition eval_transformer_concrete (t : Transformer) (ps : ConcreteTransformerState) : (ConcreteTransformerState) :=
    (* Combine match results with the rules to find the first matching rule *)
    let rules_with_match_results := List.combine (get_match_results t ps) t in
    let first_match := find_first_match rules_with_match_results in (* find_first_match is in ListUtils *)
        match first_match with
        | None => ps  (* no match, return unchanged state *)
        | Some (rule) => eval_match_action_rule_concrete rule ps (* evaluate the rule and update state accordingly *)
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
