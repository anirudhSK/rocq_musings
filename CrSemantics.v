(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.

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

(* Expression version of a header operation, meaning side-effect-free and stateless *)
Definition eval_hdr_op_expr (op : HdrOp) (v : ProgramState uint8) : uint8 :=
    match op with
    | StatefulOp f arg1 arg2 target => apply_bin_op f (function_argument_to_uint8 arg1 v) (function_argument_to_uint8 arg2 v)
    | StatelessOp f arg1 arg2 target => apply_bin_op f (function_argument_to_uint8 arg1 v) (function_argument_to_uint8 arg2 v)
    end.

(* Function to evaluate a header operation,
   meaning we apply the operation to a previous valuation to get a new one *)
Definition eval_hdr_op (op : HdrOp) (input_valuation : ProgramState uint8) : ProgramState uint8 :=
    match op with
    | StatefulOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr op input_valuation in
            update_state input_valuation target op_output
    | StatelessOp f arg1 arg2 target =>
        let op_output := eval_hdr_op_expr op input_valuation in
            update_hdr input_valuation target op_output
    end.