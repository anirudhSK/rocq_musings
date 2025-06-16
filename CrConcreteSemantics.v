(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrSemantics.

(* TODO: fill out eval_transformer body at the end,
   right now, we are just specifying it as a function that
   goes from previous valuation to new one *)
Parameter eval_transformer : Transformer -> ProgramState uint8 -> ProgramState uint8.

(* A Transformer is a list of match-action rules,
   where each rule is either sequential or parallel,
   so let's first evaluate a single rule *)

(* Function to evaluate a match-action rule,
   meaning header ops within an action are evaluated
   according to the type of the rule (sequential or parallel) *)
Parameter eval_match_action_rule : MatchActionRule -> ProgramState uint8 -> ProgramState uint8.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Parameter eval_seq_rule : MatchActionRule -> ProgramState uint8 -> ProgramState uint8.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel *)
Parameter eval_par_rule : MatchActionRule -> ProgramState uint8 -> ProgramState uint8.

(* Apply binary operation *)
Definition apply_bin_op (f : BinaryOp) (arg1 : uint8) (arg2 : uint8) : uint8 :=
  match f with
  | AddOp => Integers.add arg1 arg2
  end.

Definition lookup_uint8 (arg : FunctionArgument) (ps : ProgramState uint8) : uint8 :=
  match arg with
  | CtrlPlaneArg c => ctrl_plane_map uint8 ps c
  | HeaderArg h    => header_map uint8 ps h
  | ConstantArg n  => n
  | StatefulArg s  => state_var_map uint8 ps s
  end.

Definition eval_hdr_op_expr_uint8 (op : HdrOp) (ps : ProgramState uint8) : uint8 :=
  match op with
  | StatefulOp f arg1 arg2 _ => apply_bin_op f (lookup_uint8 arg1 ps) (lookup_uint8 arg2 ps)
  | StatelessOp f arg1 arg2 _ => apply_bin_op f (lookup_uint8 arg1 ps) (lookup_uint8 arg2 ps)
  end.

Instance Semantics_uint8 : Semantics uint8 := {
  (* Function to lookup arg in program state *)
  lookup_function_argument := lookup_uint8;
  
  (* Function to evaluate header operation expression *)
  eval_hdr_op_expr := eval_hdr_op_expr_uint8;
  
  (* Function to update header or state variable in program state *)
  eval_hdr_op_assign := fun op ps =>
    match op with
    | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr_uint8 op ps in update_state ps target op_output
    | StatelessOp f arg1 arg2 target => 
        let op_output := eval_hdr_op_expr_uint8 op ps in update_hdr ps target op_output
    end; 
}.