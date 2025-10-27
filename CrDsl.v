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

(* Check for duplicate identifiers in the header, state, and control lists *)
Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef h s c _ =>
      has_duplicates header_equal h ||
      has_duplicates state_equal s ||
      has_duplicates ctrl_equal c
  end.

From Coq Require Import Sorting.Sorted.
Check Sorted.

(* Compare two headers based on their uids *)
Definition header_lt (h1 h2 : Header) : Prop :=
  match hdr_var h1, hdr_var h2 with
  | CrHdr uid1, CrHdr uid2 => Pos.lt uid1 uid2
  | _, _ => False  (* TODO: This case should not happen if headers are well-formed *)
  end.

(* Compare two states based on their uids *)
Definition state_lt (s1 s2 : State) : Prop :=
  match st_var s1, st_var s2 with
  | CrState uid1, CrState uid2 => Pos.lt uid1 uid2
  | _, _ => False  (* TODO: This case should not happen if states are well-formed *)
  end.

(* Compare two ctrls based on their uids *)
Definition ctrl_lt (c1 c2 : Ctrl) : Prop :=
  match ctrl_var c1, ctrl_var c2 with
  | CrCtrl uid1, CrCtrl uid2 => Pos.lt uid1 uid2
  | _, _ => False  (* TODO: This case should not happen if ctrls are well-formed *)
  end.

(* No duplicates in Caracara Program *)
Definition well_formed_program (p : CaracaraProgram) : Prop :=
  match p with
  | CaracaraProgramDef h s c _ =>
      Coqlib.list_norepet h /\ Coqlib.list_norepet s /\ Coqlib.list_norepet c /\
      Sorted header_lt h /\ Sorted state_lt s /\ Sorted ctrl_lt c
  end.

(* TODO: Write a program to check for the well_formed_program property *)
(* TODO: This would involve checking for duplicates and sorting the lists *)
(* TODO: And then verifying the well_formed_program property holds *)