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

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Sorting.Mergesort.
From Stdlib Require Import Sorting.Permutation.
From Stdlib Require Import Orders.
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

(* Order on (PacketFilter * Label) by ascending [priority] of the filter.
   Exposed as a [TotalLeBool] so we can plug it into [Sorting.Mergesort],
   which provides a verified O(n log n) stable sort. *)
Module FilterPriOrder <: TotalLeBool.
  Definition t := (PacketFilter * Label)%type.
  Definition leb (x y : t) : bool :=
    Pos.leb (priority (fst x)) (priority (fst y)).
  Theorem leb_total : forall x y, leb x y = true \/ leb y x = true.
  Proof.
    intros [f1 l1] [f2 l2]; unfold leb; simpl.
    destruct (Pos.leb_spec (priority f1) (priority f2)) as [H|H];
      [ left; reflexivity | right ].
    apply Pos.leb_le; apply Pos.lt_le_incl; exact H.
  Qed.
End FilterPriOrder.

Module FilterSort := Sort FilterPriOrder.

(* Stable mergesort of a FilterDatabase in ascending order of [priority]. *)
Definition sort_db (db : FilterDatabase) : FilterDatabase :=
  FilterSort.sort db.

Definition PacketHeader := PMap.t CrVal.
Definition Classifier :=
  FilterDatabase -> PacketHeader -> option Label.

Definition Interpretation := ConcreteState -> option Label.

(* The output label is written to (HeaderCtr 1).  A StatelessOp targets a
   Header (StatefulOp targets a State), so each rule uses StatelessOp. *)
(* ------------------------------------------------------------------ *)
(*  Collect the input Headers read by a FilterDatabase.  These become   *)
(*  the input-header list of the resulting GeneralCaracaraProgram --    *)
(*  i.e. the program's "parameters".                                     *)
(* ------------------------------------------------------------------ *)

Definition header_eqb (h1 h2 : Header) : bool :=
  match h1, h2 with HeaderCtr a, HeaderCtr b => Pos.eqb a b end.

(* Headers mentioned in one MatchPattern: every left-hand h, plus the rhs
   header when the comparand is MatchHeader. *)
Definition headers_in_mp (mp : MatchPattern) : list Header :=
  List.flat_map
    (fun '(h1, _, mv) =>
      match mv with
      | MatchHeader h2 => [h1; h2]
      | MatchConst _   => [h1]
      end)
    mp.

Definition headers_in_filter (f : PacketFilter) : list Header :=
  headers_in_mp (src_ip f) ++
  headers_in_mp (dst_ip f) ++
  headers_in_mp (src_port f) ++
  headers_in_mp (dst_port f) ++
  headers_in_mp (protocol f).

(* Stable de-duplication: keep the first occurrence of each Header. *)
Definition dedup_headers (hs : list Header) : list Header :=
  List.fold_right
    (fun h acc => if existsb (header_eqb h) acc then acc else h :: acc)
    [] hs.

(* Every Header read anywhere in the database, in first-appearance order. *)
Definition headers_in_db (db : FilterDatabase) : list Header :=
  dedup_headers (List.flat_map (fun '(f, _) => headers_in_filter f) db).

(* ------------------------------------------------------------------ *)
(*  Compute h_base / h_out dynamically: pick Header uids strictly greater *)
(*  than every Header uid mentioned in any MatchPattern of [db].  This    *)
(*  guarantees the (label, priority) header pairs written by              *)
(*  make_table_transformer (and the linear-program output) never collide  *)
(*  with the headers tested by the filter match patterns.                  *)
(* ------------------------------------------------------------------ *)

Definition max_pos (a b : positive) : positive :=
  if Pos.ltb a b then b else a.

Definition max_header_in_mp (mp : MatchPattern) : positive :=
  List.fold_left
    (fun acc '(h1, _, h2) =>
      let x := match h1 with HeaderCtr p => max_pos acc p end in
      match h2 with
      | MatchHeader (HeaderCtr h2') => max_pos x h2'
      | _ => x
      end)
    mp 1%positive.

Definition max_header_in_filter (f : PacketFilter) : positive :=
  max_pos (max_header_in_mp (src_ip f))
  (max_pos (max_header_in_mp (dst_ip f))
  (max_pos (max_header_in_mp (src_port f))
  (max_pos (max_header_in_mp (dst_port f))
           (max_header_in_mp (protocol f))))).

Definition max_header_in_db (db : FilterDatabase) : positive :=
  List.fold_left
    (fun acc '(f, _) => max_pos acc (max_header_in_filter f))
    db 1%positive.

(* Output label is written to h_out.  We also reserve (h_out + 1) as the
   accumulator-priority slot used by the tss_db merger.  Table label/priority
   pairs then start at h_base = h_out + 2. *)
Definition compute_h_out (db : FilterDatabase) : Header :=
  HeaderCtr ((max_header_in_db db) + 1).

Definition compute_h_base (db : FilterDatabase) : Header :=
  HeaderCtr ((max_header_in_db db) + 3).

(* ------------------------------------------------------------------ *)

Definition linear_db (db : FilterDatabase) : GeneralCaracaraProgram :=
  let h_out := compute_h_out db in
  let db' := sort_db db in
  let t := List.fold_right
    (fun '(f, lbl) acc =>
      let mp := FlattenFilter f in
      let new_rule := Seq (SeqCtr mp [StatelessOp AddOp u8 (OpConst (CrInt (repr (unsigned lbl)))) (OpConst (CrInt (repr 0))) h_out]) in
      new_rule :: acc)
    [] db' in
  let p := CaracaraProgramDef [h_out] [] [] t in
  let net := empty_net in
  let (net, start_id) := add_program_to_network net p in
  let net := set_start_module net start_id in (* technically unnecessary but here for readability or in case empty_net changes *)
  GeneralCaracaraProgramDef (headers_in_db db) net [h_out].

(* The program output is (HeaderCtr 1).  That is, we want equivalence over
   (HeaderCtr 1). *)
Definition interp (ps : ConcreteState) : option Label :=
  match (header_map ps) !! 1 with
  | IntVal n => match n with
    | CrInt lbl => Some (repr (unsigned lbl))
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

(* Build the transformer for one hash table.
   Each rule: if the filter matches AND the new priority beats the current best,
   update (label_slot, priority_slot) — exactly P4's set_if_best action.
   Caller must pass h_body strictly greater than every Header uid mentioned in
   any MatchPattern of [table]; tss_db enforces this via [compute_h_base]. *)
Definition make_table_transformer (table : FilterDatabase) (h_body : Header): Transformer :=
  let sorted := sort_db table in
  List.map (fun '(f, lbl) =>
    Seq (SeqCtr (FlattenFilter f)
      [StatelessOp
        AddOp u8
        (OpConst (CrInt (repr (unsigned lbl))))
        (OpConst (CrInt (repr 0)))
        (h_body);
      StatelessOp
        AddOp u8
        (OpConst (CrInt (repr (Zpos (priority f)))))
        (OpConst (CrInt (repr 0)))
        (incr h_body)])
  ) sorted.

(* One merger rule: if (incr acc_base) < (incr filter_base) (i.e. the current
   best priority is below this table's priority), overwrite acc_base / (incr
   acc_base) with that table's (label, priority). *)
Definition check_match (acc_base : Header) (filter_base : Header) : Transformer :=
  [Seq (SeqCtr
    [((incr acc_base), CmpLt, MatchHeader (incr filter_base))]
    [StatelessOp
      AddOp u8
      (OpHeader filter_base)
      (OpConst (CrInt (repr 0)))
      acc_base;
    StatelessOp
      AddOp u8
      (OpHeader (incr filter_base))
      (OpConst (CrInt (repr 0)))
      (incr acc_base)
    ])].

(* The set of (label, priority) header pairs that each table writes into.
   Table i (0-indexed) writes its best match at (h_base + 2i, h_base + 2i + 1).
   table_offsets returns the list of label-slot Headers, one per table, in the
   same order tss_db chains the tables. *)
Fixpoint table_offsets (h_base : Header) (n : nat) : list Header :=
  match n with
  | O    => []
  | S n' => h_base :: table_offsets (incr (incr h_base)) n'
  end.

(* Append one merger transformer per offset to [net], chaining them after
   [prev_opt].  Returns (net, last_module_opt). *)
Fixpoint add_mergers
    (h_out : Header)
    (net : ModuleNetwork)
    (prev_opt : option ModuleName)
    (offsets : list Header)
    : ModuleNetwork * option ModuleName :=
  match offsets with
  | []       => (net, prev_opt)
  | h_off :: rest =>
    let t := check_match h_out h_off in
    let p := CaracaraProgramDef
               [h_out; incr h_out; h_off; incr h_off] [] [] t in
    let (net', cur) := add_program_to_network net p in
    let net'' := match prev_opt with
      | None      => net'
      | Some prev => add_connection_to_network net' prev cur
      end in
    add_mergers h_out net'' (Some cur) rest
  end.

Definition tss_db (db : FilterDatabase) : GeneralCaracaraProgram :=
  let h_out := compute_h_out db in
  let db' : FilterDatabase := List.map (fun '(f, lbl) =>
    (set_filter_key f (tup_to_key (GetTuple f)), lbl)) db in
  let hashtables := List.fold_left
    (fun acc '(f, lbl) =>
      let k := key f in
      PMap.set k ((f, lbl) :: acc !! k) acc)
    db' (PMap.init []) in
  let ht_list : list (positive * FilterDatabase) :=
    PTree.elements (snd hashtables) in
  (* h_base is one past the largest Header uid mentioned in any MatchPattern,
     guaranteeing the (label, priority) headers don't collide with match-tested ones *)
  let h_base : Header := compute_h_base db in
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
  (* n merger modules, one per table to conditionally overwrite the
     final output (HeaderCtr 1, HeaderCtr 2). *)
  let offsets := table_offsets h_base n in
  let '(net, last_opt) := add_mergers h_out net prev_opt offsets in
  let tss_net :=
    match first_opt, last_opt with
    | Some fst, _      => set_start_module net fst
    | None,     Some f => set_start_module net f
    | None,     None   => net (* db was empty *)
    end in
  GeneralCaracaraProgramDef (headers_in_db db) tss_net [h_out].

Definition SimpleDB : FilterDatabase :=
  [({|
      src_ip := [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 0)))];
      dst_ip := [(HeaderCtr 5, CmpEq, MatchConst (CrInt (repr 0)))];
      src_port := [(HeaderCtr 9, CmpEq, MatchConst (CrInt (repr 0)))];
      dst_port := [(HeaderCtr 11, CmpEq, MatchConst (CrInt (repr 0)))];
      protocol := [(HeaderCtr 13, CmpEq, MatchConst (CrInt (repr 1)))];
      key := 1%positive;
      priority := 1%positive |}, (repr 42));
    ({|
      src_ip := [(HeaderCtr 1, CmpEq, MatchConst (CrInt (repr 0)));
                 (HeaderCtr 2, CmpEq, MatchConst (CrInt (repr 0)))];
      dst_ip := [(HeaderCtr 5, CmpEq, MatchConst (CrInt (repr 0)))];
      src_port := [(HeaderCtr 9, CmpEq, MatchConst (CrInt (repr 0)))];
      dst_port := [(HeaderCtr 11, CmpEq, MatchConst (CrInt (repr 0)))];
      protocol := [(HeaderCtr 13, CmpEq, MatchConst (CrInt (repr 2)))];
      key := 2%positive;
      priority := 2%positive
    |}, (repr 67))
  ].
Definition ex_lin_prog : GeneralCaracaraProgram := linear_db SimpleDB.
Definition ex_tss_prog : GeneralCaracaraProgram := tss_db SimpleDB.
