(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrTransformer.
From MyProject Require Import ListUtils.
From MyProject Require Import Coqlib.
Require Import Coq.Bool.Bool.
Require Import ZArith.

(* A Module has a module name and either a parser or transformer definition *)
Inductive CrModule : Type := 
  | ParserModule (m : ModuleName) (p : Parser)
  | TransformerModule (m : ModuleName) (t : Transformer).

(* A Connection is a pair of module names *)
(* and a connection name *)
Inductive Connection : Type := 
  | ConnectionDef : ModuleName -> ModuleName -> ConnectionName -> Connection.

Inductive CaracaraProgram : Type := 
  | CaracaraProgramDef : 
      list Header -> 
      list State -> 
      list Ctrl -> 
      Transformer -> (* TODO: Currently just a single transformer *)
                     (* TODO: Generalize to list of transformers with
                              connections between them specified by a list of type (list Connection) *)
      CaracaraProgram.

Definition get_headers_from_prog (p : CaracaraProgram) : list Header :=
  match p with
  | CaracaraProgramDef h _ _ _ => h
  end.

Definition get_states_from_prog (p : CaracaraProgram) : list State :=
  match p with
  | CaracaraProgramDef _ s _ _ => s
  end.

Definition get_ctrls_from_prog (p : CaracaraProgram) : list Ctrl :=
  match p with
  | CaracaraProgramDef _ _ c _ => c
  end.

Definition get_transformer_from_prog (p : CaracaraProgram) : Transformer :=
  match p with
  | CaracaraProgramDef _ _ _ t => t
  end.