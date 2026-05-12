From MyProject Require Import CrDsl.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrModule.
From MyProject Require Import ListUtils.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Import List.
Import ListNotations.

(* Check for duplicate identifiers in the header, state, and control lists *)
Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef h s c _ =>
      (* TODO: can probably adjust has_duplicates *)
      has_duplicates varlike_equal h ||
      has_duplicates varlike_equal s ||
      has_duplicates varlike_equal c
  end.

From Stdlib Require Import Sorting.Sorted.
Check Sorted.

(* Compare two headers based on their uids *)
Section VarlikeCmp.
Context {A : Type} {CrVarLike_A : CrVarLike A}.
Definition varlike_lt (v1 v2: A) : Prop :=
  Pos.lt (get_key v1) (get_key v2).
End VarlikeCmp.

(* No duplicates in Caracara Program *)
Definition well_formed_program (p : CaracaraProgram) : Prop :=
  match p with
  | CaracaraProgramDef h s c _ =>
      Coqlib.list_norepet h /\ Coqlib.list_norepet s /\ Coqlib.list_norepet c /\
      Sorted varlike_lt h /\ Sorted varlike_lt s /\ Sorted varlike_lt c
  end.

(* TODO: Write a program to check for the well_formed_program property *)
(* TODO: This would involve checking for duplicates and sorting the lists *)
(* TODO: And then verifying the well_formed_program property holds *)

(* Per-module analogue of well_formed_program. *)
(* TODO: Needs extension once parser semantics are fleshed out *)
Definition well_formed_module (m : CrModule) : Prop :=
  match m with
  | ParserModule _ _ => True
  | TransformerModule _ states ctrls _ =>
      Coqlib.list_norepet states /\ Coqlib.list_norepet ctrls /\
      Sorted varlike_lt states /\ Sorted varlike_lt ctrls
  end.

Definition module_states (m : CrModule) : list State :=
  match m with
  | ParserModule _ _ => []
  | TransformerModule _ s _ _ => s
  end.
Definition all_network_states (net : ModuleNetwork) : list State :=
  List.flat_map module_states (all_modules net).

Definition module_ctrls (m : CrModule) : list Ctrl :=
  match m with
  | ParserModule _ _ => []
  | TransformerModule _ _ c _ => c
  end.
Definition all_network_ctrls (net : ModuleNetwork) : list Ctrl :=
  List.flat_map module_ctrls (all_modules net).

(* extend well-formedness to GeneralCaracaraProgram *)
(* NOTE: depending on the extent to which sortedness actually matters,
 * it could be possible to remove the 3rd and 4th clauses *)
Definition well_formed_general_program (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  let headers := get_headers_from_general p in
  wf_module_network net /\
  Coqlib.list_norepet headers /\
  Sorted varlike_lt headers /\
  List.Forall well_formed_module (all_modules net) /\
  Coqlib.list_norepet (all_network_states net) /\
  Coqlib.list_norepet (all_network_ctrls net).