(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrSemantics.
From MyProject Require Export ListUtils.

(* Apply binary operation *)
Definition apply_bin_op (f : BinaryOp) (arg1 : uint8) (arg2 : uint8) : uint8 :=
  match f with
  | AddOp => Integers.add arg1 arg2
  | SubOp => Integers.sub arg1 arg2
  | AndOp => Integers.and arg1 arg2
  | OrOp => Integers.or arg1 arg2
  | XorOp => Integers.xor arg1 arg2
  | MulOp => Integers.mul arg1 arg2
  | DivOp => Integers.divu arg1 arg2
  | ModOp => Integers.modu arg1 arg2
  end.

Definition lookup_uint8 (arg : FunctionArgument) (ps : ProgramState uint8) : uint8 :=
  match arg with
  | CtrlPlaneArg c => ctrl_plane_map ps c
  | HeaderArg h    => header_map ps h
  | ConstantArg n  => n
  | StatefulArg s  => state_var_map ps s
  end.

Definition eval_hdr_op_expr_uint8 (op : HdrOp) (ps : ProgramState uint8) : uint8 :=
  match op with
  | StatefulOp f arg1 arg2 _ => apply_bin_op f (lookup_uint8 arg1 ps) (lookup_uint8 arg2 ps)
  | StatelessOp f arg1 arg2 _ => apply_bin_op f (lookup_uint8 arg1 ps) (lookup_uint8 arg2 ps)
  end.

Definition eval_hdr_op_assign_uint8 (op : HdrOp) (ps: ProgramState uint8) : ProgramState uint8 :=
  match op with
  | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_uint8 op ps in update_state ps target op_output
  | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_uint8 op ps in update_hdr ps target op_output
  end.

Definition eval_match_uint8 (match_pattern : MatchPattern) (ps : ProgramState uint8) : bool :=
  (* For every list element, check if the Header's current value (determined by ps) equals the uint8 *)
  List.forallb (fun '(h, v) => eq (header_map ps h) v) match_pattern.

(* Define evaluation over a list of HdrOp *)
(* Note we are evaluating the list from right to left (fold_right) because it simplifies proving. *)
Definition eval_hdr_op_list_uint8 (hol : list HdrOp) (ps : ProgramState uint8) : ProgramState uint8 :=
  List.fold_right (fun op acc => eval_hdr_op_assign_uint8 op acc) ps hol.

(* Evalaute a single HdrOp conditionally based on a match_pattern *)
Definition eval_hdr_op_assign_uint8_conditional
  (match_pattern : MatchPattern)
  (ho : HdrOp)
  (ps : ProgramState uint8)
  : ProgramState uint8 :=
  if eval_match_uint8 match_pattern ps then
    eval_hdr_op_assign_uint8 ho ps
  else
    ps.
 
(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Definition eval_seq_rule_uint8 (srule : SeqRule) (ps : ProgramState uint8) : (ProgramState uint8) :=
  match srule with
  | SeqCtr match_pattern action =>
      if (eval_match_uint8 match_pattern ps) then
        eval_hdr_op_list_uint8 action ps
      else
        ps
  end.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel *)
(* This is identical to eval_seq_rule,
   except that the action is a list with some conditions: the targets are all unique
   these conditions are realized using subset types, that's why we need proj1_sig *)
Definition eval_par_rule_uint8 (prule : ParRule) (ps : ProgramState uint8) : (ProgramState uint8) :=
  match prule with
  | ParCtr match_pattern action =>
      if (eval_match_uint8 match_pattern ps) then
        eval_hdr_op_list_uint8 (proj1_sig action) ps
      else
        ps
  end.

(* Function to evaluate a match-action rule,
   meaning header ops within an action are evaluated
   according to the type of the rule (sequential or parallel) *)
Definition eval_match_action_rule_uint8 (rule : MatchActionRule) (ps : ProgramState uint8) : (ProgramState uint8) :=
  match rule with 
  | Seq srule => eval_seq_rule_uint8 srule ps
  | Par prule => eval_par_rule_uint8 prule ps
  end.

(* lookup header against each of the match-action rules in t to see if there is a match *)
Definition get_match_results (t : Transformer) (ps : ProgramState uint8) : list bool :=
  List.map (fun rule =>
                     match rule with 
                       | Seq (SeqCtr match_pattern _) => eval_match_uint8 match_pattern ps
                       | Par (ParCtr match_pattern _) => eval_match_uint8 match_pattern ps
                     end) t.

(* Function to evaluate a transformer, which is a list of match-action rules *)
Definition eval_transformer_uint8 (t : Transformer) (ps : ProgramState uint8) : (ProgramState uint8) :=
    (* Combine match results with the rules to find the first matching rule *)
    let rules_with_match_results := List.combine (get_match_results t ps) t in
    let first_match := find_first_match rules_with_match_results in (* find_first_match is in ListUtils *)
        match first_match with
        | None => ps  (* no match, return unchanged state *)
        | Some (rule) => eval_match_action_rule_uint8 rule ps (* evaluate the rule and update state accordingly *)
      end.

Instance Semantics_uint8 : Semantics uint8 := {
  (* Function to lookup arg in program state *)
  lookup_function_argument := lookup_uint8;
  
  (* Function to evaluate header operation expression *)
  eval_hdr_op_expr := eval_hdr_op_expr_uint8;
  
  (* Function to update header or state variable in program state *)
  eval_hdr_op_assign := eval_hdr_op_assign_uint8;
}.