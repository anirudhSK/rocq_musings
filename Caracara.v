(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.

(* Define the different types of expressions in the Caracara DSL *)
Definition CaracaraProgram : Type := (list ModuleName) * (list ConnectionName).

(* A ModuleDef has a module name and either a parser or transformer definition *)
Inductive ModuleDef : Type := 
  | ParserDefConstructor : ModuleName -> ModuleType -> ParserDef
  | TransformerDefConstructor : ModuleName -> TransformerType -> TransformerDef.

(* A ConnectionDef is a pair of module names *)
(* and a connection name *)
Inductive ConnectionDef : Type := 
  | ConnectionDefConstructor : ModuleName -> ModuleName -> ConnectionName -> ConnectionDef.

(* Transformer section below *)
(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

(* A TransformerDef has a transformer name and a transformer type *)
Inductive TransformerDef : Type := 
  | TransformerDefConstructor : ModuleName -> TransformerType -> TransformerDef.

(* A header operation represents some computation on a header *)