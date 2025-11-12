From MyProject Require Import CrDsl.
From MyProject Require Import CrVarLike.
From MyProject Require Import ListUtils.
From Coq Require Import PArith.BinPos.

(* Check for duplicate identifiers in the header, state, and control lists *)
Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef h s c _ =>
      (* TODO: can probably adjust has_duplicates *)
      has_duplicates varlike_equal h ||
      has_duplicates varlike_equal s ||
      has_duplicates varlike_equal c
  end.

From Coq Require Import Sorting.Sorted.
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