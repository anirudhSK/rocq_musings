(* Parser section below *)
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Strings.String.
From MyProject Require Import CrIdentifiers.

(* A parser is a list of parser states *)
Definition Parser : Type := list ParserState.

(* An ExtractOp pulls out a Header starting at index Start and ending at index End *)
Inductive ExtractOp : Type := 
  | ExtractOpConstructor (h : Header) (start_index : nat) (end_index : nat).

(* A Transition is either:
   (1) an unconditional jump to another parser state
   (2) a conditional jump to another parser state,
       conditional on the bits between index Start and index End of a particular Header matching a bit-pattern Pat *)
Inductive Transition : Type :=
  | Unconditional (target : ParserState)
  | Conditional (h : Header) (start_index : nat) (end_index : nat) (pattern : list bool) (target : ParserState).

(* A ParserStateDef is a pair consisting of 
 (1) an ExtractOp in that state, AND
 (2) a Transition out of that state *)
Inductive ParserStateDef : Type := 
  | ParserStateDefConstructor (s : ParserState) (e : ExtractOp) (t: Transition).