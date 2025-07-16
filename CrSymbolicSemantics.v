From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrSemantics.
From MyProject Require Import SmtExpr.
Require Import ZArith.
Require Import Coq.Strings.String.
Require Import List.
Require Import Coq.Lists.List.
Import ListNotations.

(* Convert FunctionArgument to SmtArithExpr *)
Definition lookup_smt (arg : FunctionArgument) (ps : ProgramState SmtArithExpr) : SmtArithExpr :=
  match arg with
  | CtrlPlaneArg c => ctrl_plane_map ps c
  | HeaderArg h    => header_map ps h
  | ConstantArg n  => SmtConst n
  | StatefulArg s  => state_var_map ps s
  end.

(* Define the symbolic interpreter for header operation expressions *)
Definition eval_hdr_op_expr_smt (h : HdrOp) (ps : ProgramState SmtArithExpr) : SmtArithExpr :=
    match h with
    | StatefulOp f arg1 arg2 _ =>
       match f with 
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | SubOp => SmtBitSub (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | AndOp => SmtBitAnd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | OrOp => SmtBitOr (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | XorOp => SmtBitXor (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | MulOp => SmtBitMul (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | DivOp => SmtBitDiv (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | ModOp => SmtBitMod (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    | StatelessOp f arg1 arg2 _ =>
       match f with
         | AddOp => SmtBitAdd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | SubOp => SmtBitSub (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | AndOp => SmtBitAnd (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | OrOp => SmtBitOr (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | XorOp => SmtBitXor (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | MulOp => SmtBitMul (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | DivOp => SmtBitDiv (lookup_smt arg1 ps) (lookup_smt arg2 ps)
         | ModOp => SmtBitMod (lookup_smt arg1 ps) (lookup_smt arg2 ps)
       end
    end.

Definition eval_hdr_op_assign_smt (ho : HdrOp) (ps: ProgramState SmtArithExpr) : ProgramState SmtArithExpr :=
    match ho with
    | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_smt ho ps in update_state ps target op_output
    | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_smt ho ps in update_hdr ps target op_output
    end.

(* Define evaluation over a list of HdrOp *)
(* Note we are evaluating the list from right to left (fold_right) because it simplifies proving. *)
Definition eval_hdr_op_list_smt (hol : list HdrOp) (ps : ProgramState SmtArithExpr) : ProgramState SmtArithExpr :=
  List.fold_right (fun op acc => eval_hdr_op_assign_smt op acc) ps hol.

Definition eval_match_smt (match_pattern : MatchPattern) (ps : ProgramState SmtArithExpr) : SmtBoolExpr :=
  (* For every list element, check if the Header's current value (determined by ps) equals the uint8 *)
  (* Note that because SmtBoolAnd is associative and commutative, both fold_left and fold_right give the same answer. *)
  List.fold_right (fun '(h, v) acc =>
    match acc with
    | SmtTrue => SmtBoolEq (header_map ps h) (SmtConst v)
    | _ => SmtBoolAnd (SmtBoolEq (header_map ps h) (SmtConst v)) acc
    end) SmtTrue match_pattern.

(* Maybe there's an intermediate function that evaluates a *single* HdrOp conditionally? *)
Definition eval_hdr_op_assign_smt_conditional
  (match_condition : MatchPattern)
  (ho : HdrOp) (ps: ProgramState SmtArithExpr) 
  : ProgramState SmtArithExpr :=
  let condition := eval_match_smt match_condition ps in
    match ho with
    | StatefulOp _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (state_var_map ps target) in
                        update_state ps target op_output
    | StatelessOp _ _ _ target =>
        let op_output := SmtConditional condition (eval_hdr_op_expr_smt ho ps)
                        (header_map ps target) in
                        update_hdr ps target op_output
    end.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_smt (srule : SeqRule) (ps : ProgramState SmtArithExpr) : (ProgramState SmtArithExpr) :=
  match srule with
  | SeqCtr match_pattern action =>
        (* First evaluate the match pattern by itself against the original state ps *)
        let condition := eval_match_smt match_pattern ps in

        (* Second, evaluate all the hdr_ops contained in the action to get a new intermediate state ps' from ps *)
        let ps' := eval_hdr_op_list_smt (action) ps in

          (* Third, return the updated program state:
             ctrl_plane_map: same as what it was in the original state ps,
             header_map: for every header, its value is SmtConditional condition (value in ps') (value in ps)
             state_map: similar to header_map *)

          {| ctrl_plane_map := ctrl_plane_map ps;
             header_map := fun h => SmtConditional condition (header_map ps' h) (header_map ps h);
             state_var_map := fun s => SmtConditional condition (state_var_map ps' s) (state_var_map ps s) |}   
  end.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel.
   This is identical to eval_seq_rule, except that the action is a list with some conditions: the targets are all unique
   these conditions are realized using subset types, that's why we need proj1_sig *)
Definition eval_par_rule_smt (prule : ParRule) (ps : ProgramState SmtArithExpr) : (ProgramState SmtArithExpr) :=
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

          {| ctrl_plane_map := ctrl_plane_map ps;
             header_map := fun h => SmtConditional condition (header_map ps' h) (header_map ps h);
             state_var_map := fun s => SmtConditional condition (state_var_map ps' s) (state_var_map ps s) |}   
  end.

Definition eval_match_action_rule_smt (rule : MatchActionRule) (ps : ProgramState SmtArithExpr) : (ProgramState SmtArithExpr) :=
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
Definition get_match_results_smt (t : Transformer) (ps : ProgramState SmtArithExpr) : list SmtBoolExpr :=
  List.map (fun rule =>
                       match rule with 
                        | Seq (SeqCtr match_pattern _) => eval_match_smt match_pattern ps
                        | Par (ParCtr match_pattern _) => eval_match_smt match_pattern ps
                       end) t.

Definition eval_transformer_smt (t : Transformer) (ps : ProgramState SmtArithExpr) : ProgramState SmtArithExpr :=
  (* get all future program states, one for each rule *)
  let program_states := List.map (fun rule => eval_match_action_rule_smt rule ps) t in
  (* map a header to all possible future exprs, one for each future state *)
  let header_exprs   := fun h => List.map (fun ps => header_map ps h) program_states in
  (* same as above, for state variables *)
  let state_vars     := fun s => List.map (fun ps => state_var_map ps s) program_states in
      {| ctrl_plane_map := ctrl_plane_map ps; (* leave this unchanged *)
         header_map := fun h => switch_case_expr (List.combine (get_match_results_smt t ps) (header_exprs h)) (header_map ps h);
         state_var_map := fun s => switch_case_expr (List.combine (get_match_results_smt t ps) (state_vars s)) (state_var_map ps s) |}.

Instance Semantics_SmtArithExpr : Semantics SmtArithExpr := {
  (* Function to lookup arg in program state *)
  lookup_function_argument := lookup_smt;

  (* Function to evaluate header operation expression *)
  eval_hdr_op_expr := eval_hdr_op_expr_smt;

  (* Function to update header or state variable in program state *)
  eval_hdr_op_assign := eval_hdr_op_assign_smt;
}.