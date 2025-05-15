(* Parser section below *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CaracaraIdentifiers.

(* A parser is a list of parser states *)
Definition ParserStates : Type := list ParserState.

(* An ExtractOp pulls out a Header starting at index Start and ending at index End *)
Inductive ExtractOp : Type := 
  | ExtractOpConstructor : Header -> nat -> nat -> ExtractOp.

(* A Transition is either:
   (1) an unconditional jump to another parser state
   (2) a conditional jump to another parser state,
       conditional on the bits between index Start and index End of a particular Header matching a bit-pattern Pat *)
Inductive Transition : Type :=
  | Unconditional : ParserState -> Transition
  | Conditional : Header -> nat -> nat -> string -> ParserState -> Transition.

(* A ParserStateDef is a pair consisting of 
 (1) an ExtractOp in that state, AND
 (2) a Transition out of that state *)
Inductive ParserStateDef : Type := 
  | ParserStateDefConstructor : ParserState -> ExtractOp -> Transition -> ParserStateDef.