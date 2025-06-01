(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.


(* Headers and states (or rather their valuations) are both represented
   as maps from names of headers and state variables to their values expressed as integers *)
Definition HeaderMap := string -> nat.
Definition StateMap := string -> nat.

(* InputType is the input to the transformer, which is a pair of previous header and previous state *)
(* OutputType is the output of the transformer, which is a pair of new header and new state *)
Definition InputType := (HeaderMap * StateMap)%type.
Definition OutputType := (HeaderMap * StateMap)%type.

(* TODO: fill out eval_transformer body at the end,
   right now, we are just specifying it as a function that
   goes from previous value of header+state
   to new value of header+state *)
Parameter eval_transformer : Transformer -> InputType -> OutputType.

(* A Transformer is a list of match-action rules,
   where each rule is either sequential or parallel,
   so let's first evaluate a single rule *)

(* Function to evaluate a match-action rule,
   meaning header ops within an action are evaluated
   according to the type of the rule (sequential or parallel) *)
Parameter eval_match_action_rule : MatchActionRule -> InputType -> OutputType.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Parameter eval_seq_rule : MatchActionRule -> InputType -> OutputType.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel *)
Parameter eval_par_rule : MatchActionRule -> InputType -> OutputType.

(* Function to evaluate a header operation,
   meaning we apply the operation to the header and state *)
Parameter eval_hdr_op : HdrOp -> InputType -> OutputType.