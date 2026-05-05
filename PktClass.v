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
From MyProject Require Import CrModule.
From MyProject Require Import PosWrapper.

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
      let new_rule := Seq (SeqCtr mp GTrue [StatefulOp AddOp (ConstantArg (CrUInt8 lbl)) (ConstantArg (CrUInt8 (repr 0))) (StateCtr 1)]) in
      let t := get_transformer_from_prog p in
      let new_transformer := new_rule :: t in
      let new_prog := CaracaraProgramDef [] [StateCtr 1] [] new_transformer in
      lindb_helper rest new_prog
  end.
Definition linear_db (db : FilterDatabase) : GeneralCaracaraProgram :=
  let db' := sort_db db in
  let prog := lindb_helper db' (CaracaraProgramDef [] [] [] []) in
  let t := get_transformer_from_prog prog in
  let t' := List.rev t in
  let p := CaracaraProgramDef [] [] [] t' in
  let net := empty_net in
  let (net, start_id) := add_program_to_network net p in
  let net := set_start_module net start_id in (* technically unnecessary but here for readability or in case empty_net changes *)
  init_general_from_net net.

(* The program output is state 1. That is, we want equivalence over state 1. *)
Definition interp (ps : ConcreteState) : option Label :=
  match (state_map ps) !! 1 with
  | IntVal n => match n with
    | CrUInt8 lbl => Some lbl
    | _ => None
    end
  | _ => None
  end.

(* WLoG, assume tuple size of 5 *)
Definition tup5 {T : Type} : Type := T * T * T * T * T.
Definition net_tuple : Type := @tup5 nat.
Definition map_t {T T' : Type} (f : T -> T') (t : @tup5 T) : @tup5 T' :=
  match t with
  | (t1, t2, t3, t4, t5) => (f t1, f t2, f t3, f t4, f t5)
  end.
(* Helpers that we assume correct *)
Fixpoint pow (base exp : positive) : positive :=
  match exp with
  | xH => base
  | xO e => let r := pow base e in r * r
  | xI e => let r := pow base e in base * r * r
  end.
Definition pos_of_nat' (x : nat) : positive :=
  Pos.of_nat (S x).
Definition tup_to_key (t : net_tuple) : positive :=
  let t' := map_t pos_of_nat' t in
  match t' with
  | (t1, t2, t3, t4, t5) =>
    (pow 2 t1) * (pow 3 t2) * (pow 5 t3) * (pow 7 t4) * (pow 11 t5)
  end.

Definition GetTuple (f : PacketFilter) : net_tuple :=
  (List.length (src_ip f),
   List.length (dst_ip f),
   List.length (src_port f),
   List.length (dst_port f),
   List.length (protocol f)).

(* TODO : Finish this *)
(* Build the transformer for one hash table.
   Each rule: if the filter matches AND the new priority beats the current best,
   update (label_slot, priority_slot) — exactly P4's set_if_best action. *)

(* Assume that h_body > max(Header of MatchPattern) *)
Definition make_table_transformer (table : FilterDatabase) (h_body : Header): Transformer :=
  let sorted := sort_db table in
  List.map (fun '(f, lbl) =>
    Seq (SeqCtr (FlattenFilter f) GTrue
      [StatelessOp
        AddOp
        (ConstantArg (CrUInt8 lbl))
        (ConstantArg (CrUInt8 (repr 0)))
        (h_body);
      StatelessOp
        AddOp
        (ConstantArg (CrUInt8 (repr (Zpos (priority f)))))
        (ConstantArg (CrUInt8 (repr 0)))
        (incr h_body)])
  ) sorted.

Fixpoint make_merge_rules (n : nat) (h_base : Header) : list MatchActionRule :=
  match n with
  | O => []
  | S k =>
      let h_label    := h_base in
      let h_priority := incr h_base in
      let rule :=
        Seq (SeqCtr
               []  (* no MatchPattern: gating is purely on the guard *)
               (GCmp CmpLt (StatefulArg (StateCtr 2)) (HeaderArg h_priority))
               [ StatefulOp AddOp (HeaderArg h_label)
                            (ConstantArg (CrUInt8 (repr 0))) (StateCtr 1);
                 StatefulOp AddOp (HeaderArg h_priority)
                            (ConstantArg (CrUInt8 (repr 0))) (StateCtr 2) ]) in
      rule :: make_merge_rules k (incr (incr h_base))
  end.

Definition make_merge_transformer (n : nat) (h_base : Header) : Transformer :=
  make_merge_rules n h_base.

(* tss_db: one TransformerModule per tuple-group (hash table), chained in
   sequence, terminated by a merge module that picks the highest-priority
   match across all tables and writes its label into StateCtr 1. *)
Definition tss_db (db : FilterDatabase) : GeneralCaracaraProgram :=
  let db' : FilterDatabase := List.map (fun '(f, lbl) =>
    (set_filter_key f (tup_to_key (GetTuple f)), lbl)) db in
  let hashtables := List.fold_left
    (fun acc '(f, lbl) =>
      let k := key f in
      PMap.set k ((f, lbl) :: acc !! k) acc)
    db' (PMap.init []) in
  let ht_list : list (positive * FilterDatabase) :=
    PTree.elements (snd hashtables) in
  let h_base : Header := HeaderCtr 128 in
  let '(net, first_opt, prev_opt, _) := List.fold_left
    (fun '(net, first_opt, prev_opt, header_io) '(_, table) =>
      let t := make_table_transformer table header_io in
      let p := CaracaraProgramDef [] [] [] t in
      let (net', cur) := add_program_to_network net p in
      let net'' := match prev_opt with
        | None      => net'
        | Some prev => add_connection_to_network net' prev cur
        end in
      let first' := match first_opt with
        | None => Some cur
        | x    => x
        end in
      (net'', first', Some cur, (incr (incr header_io))))
    ht_list (empty_net, None, None, h_base) in
  let n := List.length ht_list in
  let merge_t := make_merge_transformer n h_base in
  let merge_p := CaracaraProgramDef [] [StateCtr 1; StateCtr 2] [] merge_t in
  let '(net', merge_id) := add_program_to_network net merge_p in
  let net'' := match prev_opt with
    | None      => net' (* no tables: merge module stands alone *)
    | Some prev => add_connection_to_network net' prev merge_id
    end in
  let tss_net := match first_opt with
    | Some fst => set_start_module net'' fst
    | None     => set_start_module net'' merge_id (* no tables: start at merge *)
    end in
  GeneralCaracaraProgramDef [] tss_net.
