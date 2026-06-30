From MyProject Require Import CrTransformer.
From MyProject Require Import CrVal.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrProgramState.
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

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) (ps : SymbolicTransformerState) : SmtArithExpr :=
    match h with
    | StatefulOp f ty arg1 arg2 _ => smt_binop_of f ty (lookup_smt ty arg1 ps) (lookup_smt ty arg2 ps)
    | StatelessOp f ty arg1 arg2 _ => smt_binop_of f ty (lookup_smt ty arg1 ps) (lookup_smt ty arg2 ps)
    | CastStateOp from to arg _ => smt_cast from to (lookup_smt from arg ps)
    | CastHeaderOp from to arg _ => smt_cast from to (lookup_smt from arg ps)
    end.

(* Apply SmtValuation f to every entry in the symbolic state across all 3 maps *)
Definition eval_sym_state (s: SymbolicTransformerState) (f : SmtValuation) : ConcreteTransformerState :=
   let sym_eval := fun e => eval_smt_arith e f in
   program_state_mapper sym_eval sym_eval sym_eval s.

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
    end.

(* Define evaluation over a list of HdrOp *)
(* The list is evaluated left to right: the head of the list executes first. *)
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
    | MatchConst k' => SmtArithConst k' u8  (* TODO: match constants typed u8 *)
    | MatchHeader h' => lookup_varlike ps h'
    end in
    SmtBoolAnd (eval_cmp_smt c (lookup_varlike ps h) v') acc) SmtTrue match_pattern.

(* Maybe there's an intermediate function that evaluates a *single* HdrOp conditionally? *)
Definition eval_hdr_op_assign_smt_conditional
  (match_condition : MatchPattern)
  (ho : HdrOp) (ps: SymbolicTransformerState) 
  : SymbolicTransformerState :=
  let condition := eval_match_smt match_condition ps in
    match ho with
    | StatefulOp _ _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (lookup_varlike ps target) in
                        update_varlike ps target op_output
    | StatelessOp _ _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (lookup_varlike ps target) in
                        update_varlike ps target op_output
    | CastStateOp _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (lookup_varlike ps target) in
                        update_varlike ps target op_output
    | CastHeaderOp _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (lookup_varlike ps target) in
                        update_varlike ps target op_output
    end.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_smt (srule : SeqRule) (ps : SymbolicTransformerState) : (SymbolicTransformerState) :=
  match srule with
  | SeqCtr match_pattern action =>
        let condition := eval_match_smt match_pattern ps in

        (* Second, evaluate all the hdr_ops contained in the action to get a new intermediate state ps' from ps *)
        let ps' := eval_hdr_op_list_smt (action) ps in

          (* Third, return the updated program state:
             ctrl_plane_map: same as what it was in the original state ps,
             header_map: for every header, its value is SmtConditional condition (value in ps') (value in ps)
             state_map: similar to header_map *)
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s))
  end.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel.
   This is identical to eval_seq_rule, except that the action is a list with some conditions: the targets are all unique
   these conditions are realized using subset types, that's why we need proj1_sig *)
Definition eval_par_rule_smt (prule : ParRule) (ps : SymbolicTransformerState) : (SymbolicTransformerState) :=
  match prule with
  | ParCtr match_pattern action =>
        (* First evaluate the match pattern by itself against the original state ps *)
        let condition := eval_match_smt match_pattern ps in

        (* Second, evaluate all the hdr_ops contained in the action to get a new intermediate state ps' from ps *)
        let ps' := eval_hdr_op_list_smt (proj1_sig action) ps in

          (* Third, return the updated program state:
             ctrl_plane_map: same as what it was in the original state ps,
             header_map: for every header, its value is SmtConditional condition (value in ps') (value in ps)
             state_map: similar to header_map *)
            update_all_varlike
            (update_all_varlike ps (fun (h : Header) => SmtConditional condition (lookup_varlike ps' h) (lookup_varlike ps h)))
            (fun (s : State) => SmtConditional condition (lookup_varlike ps' s) (lookup_varlike ps s))
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

Definition eval_transformer_smt (t : Transformer) (ps : SymbolicTransformerState) : SymbolicTransformerState :=
  (* get all future program states, one for each rule *)
  let program_states := List.map (fun rule => eval_match_action_rule_smt rule ps) t in
  (* map a header to all possible future exprs, one for each future state *)
  let header_exprs   := fun (h : Header) => List.map (fun ps => lookup_varlike ps h) program_states in
  (* same as above, for state variables *)
  let state_vars     := fun (s : State) => List.map (fun ps => lookup_varlike ps s) program_states in
    update_all_varlike
    (update_all_varlike ps (fun h => switch_case_expr (List.combine (get_match_results_smt t ps) (header_exprs h)) (lookup_varlike ps h)))
    (fun s => switch_case_expr (List.combine (get_match_results_smt t ps) (state_vars s)) (lookup_varlike ps s)).