(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
From MyProject Require Export CrDsl.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export ListUtils.

(* Apply binary operation *)
Definition apply_bin_op (f : BinaryOp) (arg1 : InitStatus uint8) (arg2 : InitStatus uint8) : InitStatus uint8 :=
 match arg1, arg2 with
  | Initialized a1, Initialized a2 =>
      let result := match f with
      | AddOp => Integers.add a1 a2
      | SubOp => Integers.sub a1 a2
      | AndOp => Integers.and a1 a2
      | OrOp =>  Integers.or a1 a2
      | XorOp => Integers.xor a1 a2
      | MulOp => Integers.mul a1 a2
      | DivOp => Integers.divu a1 a2
      | ModOp => Integers.modu a1 a2
      end
      in Initialized uint8 result
  | _, _ => Uninitialized uint8
  end.

Definition lookup_concrete (arg : FunctionArgument) (ps : ConcreteState) : InitStatus uint8 :=
  match arg with
  | CtrlPlaneArg c => lookup_ctrl ps c
  | HeaderArg h    => lookup_hdr ps h
  | ConstantArg n  => Initialized uint8 n
  | StatefulArg s  => lookup_state ps s
  end.

Definition eval_hdr_op_expr_concrete (op : HdrOp) (ps : ConcreteState) : InitStatus uint8 :=
  match op with
  | StatefulOp f arg1 arg2 _ => apply_bin_op f (lookup_concrete arg1 ps) (lookup_concrete arg2 ps)
  | StatelessOp f arg1 arg2 _ => apply_bin_op f (lookup_concrete arg1 ps) (lookup_concrete arg2 ps)
  end.

Definition eval_hdr_op_assign_concrete (op : HdrOp) (ps: ConcreteState) : ConcreteState :=
  match op with
  | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_concrete op ps in update_state ps target op_output
  | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_concrete op ps in update_hdr ps target op_output
  end.

Definition eval_match_concrete (match_pattern : MatchPattern) (ps : ConcreteState) : bool :=
  (* For every list element, check if the Header's current value (determined by ps) equals the uint8 *)
  List.forallb (fun '(h, v) => initstatus_uint8_equal (lookup_hdr ps h) (Initialized uint8 v))
                               match_pattern.

(* Define evaluation over a list of HdrOp *)
(* Note we are evaluating the list from right to left (fold_right) because it simplifies proving. *)
Definition eval_hdr_op_list_concrete (hol : list HdrOp) (ps : ConcreteState) : ConcreteState :=
  List.fold_right (fun op acc => eval_hdr_op_assign_concrete op acc) ps hol.

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
                       | Seq (SeqCtr match_pattern _) => eval_match_concrete match_pattern ps
                       | Par (ParCtr match_pattern _) => eval_match_concrete match_pattern ps
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