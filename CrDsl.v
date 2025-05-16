(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrParser.
From MyProject Require Export CrTransformer.
From MyProject Require Export CrScheduler.

(* A Module has a module name and either a parser or transformer definition *)
Inductive Module : Type := 
  | ParserModule (m : ModuleName) (p : Parser)
  | TransformerModule (m : ModuleName) (t : Transformer)
  | SchedulerModule (m : ModuleName) (s : Scheduler).

(* A Connection is a pair of module names *)
(* and a connection name *)
Inductive Connection : Type := 
  | ConnectionDef : ModuleName -> ModuleName -> ConnectionName -> Connection.

Definition CaracaraProgram : Type := (list Module) * (list Connection).