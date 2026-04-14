From MyProject Require Import CrTransformer.
From MyProject Require Import CrDsl.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import Maps.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrConcreteSemanticsTransformer.

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
Import ListNotations.

Definition Class := uint8. (* TODO: there's probably a better rep. *)
Definition FilterDatabase := list (MatchPattern * Class).

Definition PacketHeader := PMap.t CrVal.
Definition Classifier :=
  FilterDatabase -> PacketHeader -> option Class.

Definition Interpretation := ConcreteState -> option Class.

Fixpoint db_to_simple_helper (f : FilterDatabase) (p : CaracaraProgram) : CaracaraProgram :=
  match f with
  | [] => p
  | (mp, cls) :: rest =>
      let new_rule := Seq (SeqCtr mp [StatefulOp AddOp (ConstantArg (CrUInt8 cls)) (ConstantArg (CrUInt8 (repr 0))) (StateCtr 1)]) in
      let t := get_transformer_from_prog p in
      let new_transformer := new_rule :: t in
      let new_prog := CaracaraProgramDef [] [] [] new_transformer in
      db_to_simple_helper rest new_prog
  end.
Definition db_to_simple_classifier (f : FilterDatabase) : CaracaraProgram :=
  let prog := db_to_simple_helper f (CaracaraProgramDef [] [] [] []) in
  let t := get_transformer_from_prog prog in
  let t' := List.rev t in
  CaracaraProgramDef [] [] [] t'.

Definition pkt_does_match (mp : MatchPattern) (pkt_h : PacketHeader) : bool :=
  List.forallb (fun '(h, v) =>
    CrVal.eqb (pkt_h !! (get_key h)) (IntVal v)) mp.
Definition run_filter_db (f : FilterDatabase) (pkt_h : PacketHeader) : option Class :=
  match List.find (fun '(mp, _) => pkt_does_match mp pkt_h) f with
  | Some (_, cls) => Some cls
  | None => None
  end.

Definition db_classifier : Classifier := run_filter_db.

(* A program, p, is a packet classifier under an interpretation, i, if
 *   when a packet with a given header is processed by p,
 *   the interpretation of the resulting state is the same as
 *   the class assigned by running that filter db on said packet header.
 *)
Definition is_classifier
  (p : CaracaraProgram)
  (i : Interpretation)
  (f : FilterDatabase) : Prop :=
  forall (pkt_h : PacketHeader) (ps : ConcreteState),
    (header_map ps) = pkt_h ->
    i (eval_cr_program_concrete p ps) = run_filter_db f pkt_h.

Definition simple_interpreter (ps : ConcreteState) : option Class :=
  match (state_map ps) !! 1 with
  | IntVal n => match n with
    | CrUInt8 cls => Some cls
    | _ => None
    end
  | _ => None
  end.

Theorem db_to_simple_classifier_correct :
  forall (f : FilterDatabase),
    is_classifier (db_to_simple_classifier f) simple_interpreter f.
Proof.
Admitted.