(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Import CrTransformer.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrDsl.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import ListUtils.
From MyProject Require Import CrVal.

(* Apply binary operation *)
Definition apply_bin_op (f : BinaryOp) (arg1 : CrVal) (arg2 : CrVal) : CrVal :=
  match f with
  | AddOp => CrVal.add arg1 arg2
  | SubOp => CrVal.sub arg1 arg2
  | AndOp => CrVal.and arg1 arg2
  | OrOp =>  CrVal.or arg1 arg2
  | XorOp => CrVal.xor arg1 arg2
  | MulOp => CrVal.mul arg1 arg2
  | DivOp => CrVal.divu arg1 arg2
  | ModOp => CrVal.modu arg1 arg2
  end.

Definition lookup_concrete (arg : Operand) (ps : ConcreteState) : CrVal :=
  match arg with
  | OpCtrlPlane c => lookup_varlike_map (@map_from_ps Ctrl _ _ ps) c
  | OpHeader h    => lookup_varlike_map (@map_from_ps Header _ _ ps) h
  | OpConst n  => IntVal n
  | OpStateful s  => lookup_varlike_map (@map_from_ps State _ _ ps) s
  end.

(* Apply [f] at int type [ty]: read both operands at [ty] and produce the
   result at [ty] (mask operands and result to the operation's width). *)
Definition apply_bin_op_of (f : BinaryOp) (ty : CrIntType) (v1 v2 : CrVal) : CrVal :=
  coerce_to_type ty (apply_bin_op f (coerce_to_type ty v1) (coerce_to_type ty v2)).

(* Reinterpret [v] from int type [from] to [to] (truncate / zero-extend). *)
Definition apply_cast (from to : CrIntType) (v : CrVal) : CrVal :=
  coerce_to_type to (coerce_to_type from v).

Definition eval_hdr_op_expr_concrete (op : HdrOp) (ps : ConcreteState) : CrVal :=
  match op with
  | StatefulOp f ty arg1 arg2 _ => apply_bin_op_of f ty (lookup_concrete arg1 ps) (lookup_concrete arg2 ps)
  | StatelessOp f ty arg1 arg2 _ => apply_bin_op_of f ty (lookup_concrete arg1 ps) (lookup_concrete arg2 ps)
  | CastStateOp from to arg _ => apply_cast from to (lookup_concrete arg ps)
  | CastHeaderOp from to arg _ => apply_cast from to (lookup_concrete arg ps)
  end.

Definition eval_hdr_op_assign_concrete (op : HdrOp) (ps: ConcreteState) : ConcreteState :=
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

Definition eval_match_concrete (match_pattern : MatchPattern) (ps : ConcreteState) : bool :=
  List.forallb (fun '(h, c, v) =>
  let v' := match v with
  | MatchConst k' => (IntVal k')
  | MatchHeader h' => (lookup_varlike ps h')
  end in
  eval_cmp_concrete c (lookup_varlike ps h) v') match_pattern.

(* Define evaluation over a list of HdrOp *)
(* The list is evaluated left to right: the head of the list executes first. *)
Definition eval_hdr_op_list_concrete (hol : list HdrOp) (ps : ConcreteState) : ConcreteState :=
  List.fold_left (fun acc op => eval_hdr_op_assign_concrete op acc) hol ps.

(* Evalaute a single HdrOp conditionally based on a match_pattern *)
Definition eval_hdr_op_assign_concrete_conditional
  (match_pattern : MatchPattern)
  (ho : HdrOp)
  (ps : ConcreteState)
  : ConcreteState :=
  if eval_match_concrete match_pattern ps then
    eval_hdr_op_assign_concrete ho ps
  else
    ps.
 
(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_concrete (srule : SeqRule) (ps : ConcreteState) : (ConcreteState) :=
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
Definition eval_par_rule_concrete (prule : ParRule) (ps : ConcreteState) : (ConcreteState) :=
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
Definition eval_match_action_rule_concrete (rule : MatchActionRule) (ps : ConcreteState) : (ConcreteState) :=
  match rule with 
  | Seq srule => eval_seq_rule_concrete srule ps
  | Par prule => eval_par_rule_concrete prule ps
  end.

(* lookup header against each of the match-action rules in t to see if there is a match *)
Definition get_match_results (t : Transformer) (ps : ConcreteState) : list bool :=
  List.map (fun rule =>
                     match rule with
                       | Seq (SeqCtr match_pattern _) =>
                           eval_match_concrete match_pattern ps
                       | Par (ParCtr match_pattern _) =>
                           eval_match_concrete match_pattern ps
                     end) t.

(* Function to evaluate a transformer, which is a list of match-action rules *)
Definition eval_transformer_concrete (t : Transformer) (ps : ConcreteState) : (ConcreteState) :=
    (* Combine match results with the rules to find the first matching rule *)
    let rules_with_match_results := List.combine (get_match_results t ps) t in
    let first_match := find_first_match rules_with_match_results in (* find_first_match is in ListUtils *)
        match first_match with
        | None => ps  (* no match, return unchanged state *)
        | Some (rule) => eval_match_action_rule_concrete rule ps (* evaluate the rule and update state accordingly *)
      end.

(* Function to evaluate a Caracara program *)
Definition eval_cr_program_concrete (p : CaracaraProgram) (ps : ConcreteState) : (ConcreteState) :=
  match p with
  | CaracaraProgramDef _ _ _ t => eval_transformer_concrete t ps
  (* TODO: Maybe do something with the various lists of headers, states, and ctrls *)
  end.

(* Could be useful to have a proof about sequential vs parallel *)
(* Relax notion of local state *)
(* filter database = naive program *)
