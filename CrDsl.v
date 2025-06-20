(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrTransformer.
From MyProject Require Export ListUtils.
Require Import Coq.Bool.Bool.

(* A Module has a module name and either a parser or transformer definition *)
Inductive Module : Type := 
  | TransformerModule (m : ModuleName) (t : Transformer).

(* A Connection is a pair of module names *)
(* and a connection name *)
Inductive Connection : Type := 
  | ConnectionDef : ModuleName -> ModuleName -> ConnectionName -> Connection.

Inductive CaracaraProgram : Type := 
  | CaracaraProgramDef : 
      list ParserState -> 
      list Header -> 
      list StateVar -> 
      list ModuleName -> 
      list FunctionName -> 
      list ConnectionName -> 
      list CtrlPlaneConfigName -> 
      list Module -> 
      list Connection -> 
      CaracaraProgram.

Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef p h s m f c cc _ _ =>
      has_duplicates parser_state_equal p ||
      has_duplicates header_equal h ||
      has_duplicates state_var_equal s ||
      has_duplicates module_name_equal m ||
      has_duplicates function_name_equal f ||
      has_duplicates connection_name_equal c ||
      has_duplicates ctrl_plane_config_name_equal cc
  end.

  (* No duplicates in Caracara Program *)
  Definition CaracaraNoDup (p : CaracaraProgram) : Prop :=
  match p with
  | CaracaraProgramDef ps hs svs mns fns cns cpns _ _  =>
      NoDup ps /\ NoDup hs /\ NoDup svs /\ NoDup mns /\
      NoDup fns /\ NoDup cns /\ NoDup cpns
  end.

  (* Check if any of the identifier lists in the CR program has duplicates.
     Use the check_for_duplicate_identifiers function above.
     If it returns false, it implies there are no duplicates. *)
Lemma check_for_duplicates_in_cr_program :
    forall (p : CaracaraProgram),
      check_for_duplicate_identifiers (p) = false ->
        CaracaraNoDup p.
Proof.
    intros p.
    intros H.
    destruct p.
    unfold CaracaraNoDup.
    simpl in H.
    apply orb_false_iff in H as [H' H7].
    apply orb_false_iff in H' as [H'' H6].
    apply orb_false_iff in H'' as [H''' H5].
    apply orb_false_iff in H''' as [H'''' H4].
    apply orb_false_iff in H'''' as [H''''' H3].
    apply orb_false_iff in H''''' as [H1 H2].
    (* Now H'''''' is the first, H2 is the second, ..., H7 is the last *)
    repeat split.
    - apply has_duplicates_correct with (eqb := parser_state_equal). apply H1.
    - apply has_duplicates_correct with (eqb := header_equal). apply H2.
    - apply has_duplicates_correct with (eqb := state_var_equal). apply H3.
    - apply has_duplicates_correct with (eqb := module_name_equal). apply H4.
    - apply has_duplicates_correct with (eqb := function_name_equal). apply H5.
    - apply has_duplicates_correct with (eqb := connection_name_equal). apply H6.
    - apply has_duplicates_correct with (eqb := ctrl_plane_config_name_equal). apply H7.
Qed.