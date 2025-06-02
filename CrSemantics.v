(* Provide semantics for a Transformer by providing an evaluation function *)
From MyProject Require Export CrTransformer.
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.

(* Code below is for efficient finite maps from the Rocq stdlib *)
Require Import Coq.FSets.FMapAVL.
Require Import Coq.Structures.OrderedTypeEx.
Module StringMap := FMapAVL.Make(String_as_OT).
Definition Dict := StringMap.t nat.

(* Headers and states (or rather their valuations) are both represented
   as maps from names of headers and state variables to their values expressed as integers *)
   (* TODO: See if we can make HeaderMap map from Header to nat, rather than string to nat,
      and similar for StateMap as well. This requires some level of playing around with UsualOrderedType,
      which is where I got stuck: https://rocq-prover.org/doc/master/stdlib/Stdlib.Structures.OrderedTypeEx.html *)
Definition HeaderMap := Dict.
Definition StateMap := Dict.

(* InputType is the input to the transformer, which is a pair of previous header and previous state *)
(* OutputType is the output of the transformer, which is a pair of new header and new state *)
Definition HeaderStatePair := (HeaderMap * StateMap)%type.
Example header_state_pair_example : HeaderStatePair :=
  (StringMap.empty nat, StringMap.empty nat).
(* TODO: fill out eval_transformer body at the end,
   right now, we are just specifying it as a function that
   goes from previous value of header+state
   to new value of header+state *)
Parameter eval_transformer : Transformer -> HeaderStatePair -> HeaderStatePair.

(* A Transformer is a list of match-action rules,
   where each rule is either sequential or parallel,
   so let's first evaluate a single rule *)

(* Function to evaluate a match-action rule,
   meaning header ops within an action are evaluated
   according to the type of the rule (sequential or parallel) *)
Parameter eval_match_action_rule : MatchActionRule -> HeaderStatePair -> HeaderStatePair.

(* Function to evaluate a sequential match-action rule,
   meaning header ops within an action are evaluated sequentially *)
Parameter eval_seq_rule : MatchActionRule -> HeaderStatePair -> HeaderStatePair.

(* Function to evaluate a parallel match-action rule,
   meaning header ops within an action are evaluated in parallel *)
Parameter eval_par_rule : MatchActionRule -> HeaderStatePair -> HeaderStatePair.

(* Function to evaluate a header operation,
   meaning we apply the operation to the header and state *)
Definition eval_hdr_op (op : HdrOp) (input : HeaderStatePair) : HeaderStatePair :=
    match op with
    | StatefulOp f arg1 arg2 target => header_state_pair_example (* Placeholder for actual evaluation logic *)
    | StatelessOp f arg1 arg2 target => header_state_pair_example (* Placeholder for actual evaluation logic *)
    end.

(*TODO: Maybe figure out a way to unify parsing and header manipulation into seq and par transformers respectively. *)