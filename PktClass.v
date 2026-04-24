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

(*
IR_l := Linear Packet Classifier IR Program
IR_t := TSS Packet Classifier IR Program

IR_l and IR_t are generated according to a parameter filter database

WANT to prove:
IR_l == IR_t in a general sense
i.e. for arbitrary filter database, the IR_l and IR_t programs are equivalent
However, the equivalence checker is only able to make an assertion about
the equivalence of two specific programs (e.g. IR_l and IR_t generated with
a specific filter database).

So to prove IR_l == IR_t using the equivalence checker,
we would need to run the equivalence checker for every possible filter database
This is not tractable
*)

Definition Label := uint8. (* TODO: there's probably a better rep. *)
Record PacketFilter := {
  src_ip : MatchPattern;
  dst_ip : MatchPattern;
  src_port : MatchPattern;
  dst_port : MatchPattern;
  protocol : MatchPattern;
  key : positive;
  priority : positive;
}.
Definition set_filter_key (f : PacketFilter) (k : positive) : PacketFilter := {|
  src_ip := src_ip f;
  dst_ip := dst_ip f;
  src_port := src_port f;
  dst_port := dst_port f;
  protocol := protocol f;
  key := k;
  priority := priority f;
|}.
Definition FlattenFilter (f : PacketFilter) : MatchPattern :=
  (src_ip f) ++ (dst_ip f) ++ (src_port f) ++ (dst_port f) ++ (protocol f).
Definition filter_ltb (f1 f2 : PacketFilter) :=
  Pos.ltb (priority f1) (priority f2).
Definition FilterDatabase := list (PacketFilter * Label).
Definition sort_db (db : FilterDatabase) : FilterDatabase :=
  db. (* TODO *)

Definition PacketHeader := PMap.t CrVal.
Definition Classifier :=
  FilterDatabase -> PacketHeader -> option Label.

Definition Interpretation := ConcreteState -> option Label.

Fixpoint lindb_helper (db : FilterDatabase) (p : CaracaraProgram) : CaracaraProgram :=
  match db with
  | [] => p
  | (f, lbl) :: rest =>
      let mp := FlattenFilter f in
      let new_rule := Seq (SeqCtr mp [StatefulOp AddOp (ConstantArg (CrUInt8 lbl)) (ConstantArg (CrUInt8 (repr 0))) (StateCtr 1)]) in
      let t := get_transformer_from_prog p in
      let new_transformer := new_rule :: t in
      let new_prog := CaracaraProgramDef [] [] [] new_transformer in
      lindb_helper rest new_prog
  end.
Definition linear_db (db : FilterDatabase) : CaracaraProgram :=
  let db' := sort_db db in
  let prog := lindb_helper db' (CaracaraProgramDef [] [] [] []) in
  let t := get_transformer_from_prog prog in
  let t' := List.rev t in
  CaracaraProgramDef [] [] [] t'.

(* The program output is state 1. That is, we want equivalence over state 1. *)
Definition interp (ps : ConcreteState) : option Label :=
  match (state_map ps) !! 1 with
  | IntVal n => match n with
    | CrUInt8 lbl => Some lbl
    | _ => None
    end
  | _ => None
  end.

Definition net_tuple : Type := nat * nat * nat * nat *nat.

(* TODO
 * e.g. something reminiscent of Godel numbering(?)
 * like 2^t1 + 3^t2 + 5^t3 + 7^t4 + 11^t5 *)
Definition pos_of_nat' (x : nat) : positive :=
  Pos.of_nat (S x).
Definition tup_to_key (t : net_tuple) : positive :=
  match t with
  | (t1, _, _, _, _) => pos_of_nat' t1
  end.

Definition GetTuple (f : PacketFilter) : net_tuple :=
  (List.length (src_ip f),
   List.length (dst_ip f),
   List.length (src_port f),
   List.length (dst_port f),
   List.length (protocol f)).

(* TODO : Finish this *)
Definition tss_db (db : FilterDatabase) : CaracaraProgram :=
  let db' : FilterDatabase := List.map (fun fxl =>
    match fxl with
    | (f, lbl) =>
      let t := GetTuple f in
      let k := tup_to_key t in
      let f' := set_filter_key f k in
      (f', lbl)
    end) db in
  let empty_ht : PMap.t (option (PacketFilter * Label)) := PMap.init None in
  let hashtables := List.fold_left
    (fun acc '(f, lbl) =>
      let k := key f in
      let prev := acc !! k in
      let new_entry := PMap.set (priority f) (Some (f, lbl)) prev in
      PMap.set k new_entry acc) db' (PMap.init empty_ht) in
  CaracaraProgramDef [] [] [] [].

(* theorem of tss correctness considers IR implementation detail *)
(* draw theorem DAG and send over *)
