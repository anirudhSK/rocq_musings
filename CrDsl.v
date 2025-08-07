(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrParser.
From MyProject Require Export CrTransformer.
From MyProject Require Export ListUtils.
From MyProject Require Export Coqlib.
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

(* No duplicates in Caracara Program *)
Definition well_formed_program (p : CaracaraProgram) : Prop :=
  match p with
  | CaracaraProgramDef h s c _ =>
      Coqlib.list_norepet h /\ Coqlib.list_norepet s /\ Coqlib.list_norepet c
  end.

(* Check if any of the identifier lists in the CR program has duplicates.
   Use the check_for_duplicate_identifiers function above.
   If it returns false, it implies there are no duplicates. *)
Lemma check_for_duplicates_in_cr_program :
    forall (p : CaracaraProgram),
      check_for_duplicate_identifiers (p) = false ->
      well_formed_program p.
Proof.
    intros p.
    intros H.
    destruct p.
    unfold well_formed_program.
    simpl in H.
    apply orb_false_iff in H as [H' H3].
    apply orb_false_iff in H' as [H'' H2].
    (* Now H'' is the first, H2 is the second, H3 is the last *)
    repeat split.
    - apply has_duplicates_correct with (eqb := header_equal);
      intros; try destruct a; try destruct b; simpl; try apply Pos.eqb_refl; try apply Pos.eqb_sym; try apply H''.
    - apply has_duplicates_correct with (eqb := state_equal);
      intros; try destruct a; try destruct b; simpl; try apply Pos.eqb_refl; try apply Pos.eqb_sym; try apply H2.
    - apply has_duplicates_correct with (eqb := ctrl_equal);
      intros; try destruct a; try destruct b; simpl; try apply Pos.eqb_refl; try apply Pos.eqb_sym; try apply H3.
Qed.