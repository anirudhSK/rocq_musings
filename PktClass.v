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
From MyProject Require Import CrParser.
From MyProject Require Import CrDeparser.

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

Definition Interpretation := ConcreteTransformerState -> option Label.

(* The output label is written to (HeaderCtr 1).  A StatelessOp targets a
   Header (StatefulOp targets a State), so each rule uses StatelessOp. *)
(* ------------------------------------------------------------------ *)
(*  Collect the input Headers read by a FilterDatabase.  These become *)
(*  the input-header list of the resulting GeneralCaracaraProgram --  *)
(*  i.e. the program's "parameters".                                  *)
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
      | MatchConst _ _ => [h1]
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

(* ---------------------------------------------------------------------- *)
(*  Compute h_base / h_out dynamically: pick Header uids strictly greater *)
(*  than every Header uid mentioned in any MatchPattern of [db].  This    *)
(*  guarantees the (label, priority) header pairs written by              *)
(*  make_table_transformer (and the linear-program output) never collide  *)
(*  with the headers tested by the filter match patterns.                 *)
(* ---------------------------------------------------------------------- *)

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

(* The header slots [field_extractor] populates.  A filter database is only
   meaningful against this mapping: every Header a MatchPattern tests must be
   one of these, and must be tested at the same CrIntType the extract wrote,
   because [CrVal.eqb]/[ltb] compare the int type before the value. *)
Definition h_src_ip   : Header := HeaderCtr 1.
Definition h_dst_ip   : Header := HeaderCtr 2.
Definition h_protocol : Header := HeaderCtr 5.
Definition h_src_port : Header := HeaderCtr 9.
Definition h_dst_port : Header := HeaderCtr 11.

(* Total bits consumed: 72 + 8 + 16 + 32 + 32 + 16 + 16. *)
Definition field_extractor_width : nat := 192.

Definition field_extractor : CrModule :=
ParserModule (ModuleNameCtr 1) {|
  parser_start := ParserStateLabelCtr 1;
  parser_states := [{| (* move to protocol @ bit 72 *)
    psd_action := Some (SeekForward 72);
    psd_label := ParserStateLabelCtr 1; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 2))
  |}; {| (* extract protocol *)
    psd_action := Some (ExtractOpConstructor h_protocol 8 u8);
    psd_label := ParserStateLabelCtr 2; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 3))
  |}; {| (* move to src ip @ bit 96 *)
    psd_action := Some (SeekForward 16);
    psd_label := ParserStateLabelCtr 3; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 4))
  |}; {| (* extract src ip *)
    psd_action := Some (ExtractOpConstructor h_src_ip 32 u32);
    psd_label := ParserStateLabelCtr 4; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 5))
  |}; {| (* extract dst ip *)
    psd_action := Some (ExtractOpConstructor h_dst_ip 32 u32);
    psd_label := ParserStateLabelCtr 5; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 6))
  |}; {| (* extract src port *)
    psd_action := Some (ExtractOpConstructor h_src_port 16 u16);
    psd_label := ParserStateLabelCtr 6; psd_trans := Unconditional (TargetState (ParserStateLabelCtr 7))
  |}; {| (* extract dst port *)
    psd_action := Some (ExtractOpConstructor h_dst_port 16 u16);
    psd_label := ParserStateLabelCtr 7; psd_trans := Unconditional Accept
  |}]
|}.

(* Copy the classified label from [h_out] into (HeaderCtr 1), the header
   [dump_label] emits.  Both constructions need this as their last transformer:
   the label is accumulated in [h_out] (chosen disjoint from the match-tested
   headers), but the program's observable is what the deparser emits. *)
Definition copy_to_out (h_out : Header) : Transformer :=
  [Seq (SeqCtr []
    [StatelessOp AddOp u8 (OpHeader h_out) (OpConst (repr 0)) (HeaderCtr 1)])].

Definition dump_label : CrModule :=
  DeparserModule (ModuleNameCtr 2) {|
    deparser_emits := [EmitOpConstructor (HeaderCtr 1) 8]
  |}.

Definition linear_db (db : FilterDatabase) : GeneralCaracaraProgram :=
  let h_out := compute_h_out db in
  let db' := sort_db db in
  let t := List.fold_right
    (fun '(f, lbl) acc =>
      let mp := FlattenFilter f in
      let new_rule := Seq (SeqCtr mp [StatelessOp AddOp u8 (OpConst (repr (unsigned lbl))) (OpConst (repr 0)) h_out]) in
      new_rule :: acc)
    [] db' in
  GeneralCaracaraProgramDef
    field_extractor_width
    []
    {|
      net_modules := [
        field_extractor;
        TransformerModule (ModuleNameCtr 3) [] [] t;
        (* Same [copy_to_out] step tss_db uses: without it the label sits in
           h_out and the deparser emits whatever (HeaderCtr 1) still holds,
           which is the parser's src_ip. *)
        TransformerModule (ModuleNameCtr 4) [] [] (copy_to_out h_out);
        dump_label
      ];
      net_edges := fun from to =>
        match unwrap from, unwrap to with
        | 1%positive, 3%positive => true
        | 3%positive, 4%positive => true
        | 4%positive, 2%positive => true
        | _, _ => false
        end;
      start_module := ModuleNameCtr 1;
    |}.

(* The program output is (HeaderCtr 1).  That is, we want equivalence over
   (HeaderCtr 1). *)
Definition interp (ps : ConcreteTransformerState) : option Label :=
  match (t_header_map ps) !! 1 with
  | IntVal lbl _ => Some (repr (unsigned lbl))
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
        (OpConst (repr (unsigned lbl)))
        (OpConst (repr 0))
        (h_body);
      StatelessOp
        AddOp u8
        (OpConst (repr (Zpos (priority f))))
        (OpConst (repr 0))
        (incr h_body)])
  ) sorted.

(* One merger rule.  A LOWER priority number means HIGHER precedence, so this
   table's match displaces the running best exactly when
   (incr filter_base) < (incr acc_base).

   This is the convention linear_db already implements: its rules are ordered by
   ascending priority and [eval_transformer_concrete] takes the FIRST match, so
   the smallest priority number wins.  [make_table_transformer] does the same
   within a table.  Comparing the other way round here would make tss_db pick
   the largest priority number across tables and disagree with linear_db on any
   packet matching filters in two different tables.

   A table that did not match leaves its priority slot uninitialized, and
   [CrVal.ltb] is false on UninitVal, so a non-matching table never displaces
   the accumulator. *)
Definition check_match (acc_base : Header) (filter_base : Header) : Transformer :=
  [Seq (SeqCtr
    [((incr filter_base), CmpLt, MatchHeader (incr acc_base))]
    [StatelessOp
      AddOp u8
      (OpHeader filter_base)
      (OpConst (repr 0))
      acc_base;
    StatelessOp
      AddOp u8
      (OpHeader (incr filter_base))
      (OpConst (repr 0))
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
  (* Seed the network with the shared parser (field_extractor, name 1) and
     deparser (dump_label, name 2).  Their fixed names mean
     add_program_to_network allocates every table/merger/copy module at name
     >= 3, so there are no collisions and both modules can be reused as-is.
     The parser is the start module; the chain feeds into the deparser. *)
  let net_init : ModuleNetwork := {|
    net_modules  := [field_extractor; dump_label];
    net_edges    := fun _ _ => false;
    start_module := get_mod_name field_extractor;
  |} in
  (* Seed the accumulator's priority slot before any merger runs.  Without this
     it is UninitVal, [CrVal.ltb] is false on UninitVal, and no merger can ever
     fire -- h_out would never be written at all.

     The seed is the WORST precedence, so that any real match displaces it.
     Since lower numbers win, that is the largest u8, 255.  Consequence: a
     filter with priority 255 can never win a merge (255 < 255 is false), so
     priorities must stay in [1, 254].  The priority slot is u8 because
     [make_table_transformer] writes priorities with [AddOp u8] and [CrVal.ltb]
     requires both operands to share an int type.

     Only the priority slot is seeded, not h_out itself: that way a packet
     matching no filter leaves h_out uninitialized and the deparser rejects,
     exactly as it does in linear_db. *)
  let init_acc : Transformer :=
    [Seq (SeqCtr []
      [StatelessOp AddOp u8 (OpConst (repr 255)) (OpConst (repr 0)) (incr h_out)])] in
  let (net_init, acc_id) :=
    add_program_to_network net_init (CaracaraProgramDef [] [] [] init_acc) in
  let net_init :=
    add_connection_to_network net_init (get_mod_name field_extractor) acc_id in
  let '(net, prev_opt, _) := List.fold_left
    (fun '(net, prev_opt, header_io) '(_, table) =>
      let t := make_table_transformer table header_io in
      let p := CaracaraProgramDef [] [] [] t in
      let (net', cur) := add_program_to_network net p in
      let net'' := match prev_opt with
        | None      => net'
        | Some prev => add_connection_to_network net' prev cur
        end in
      (net'', Some cur, (incr (incr header_io))))
    ht_list (net_init, Some acc_id, h_base) in
  let n := List.length ht_list in
  (* n merger modules, one per table, that accumulate the best (label,
     priority) match into (h_out, incr h_out) -- slots deliberately disjoint
     from the match-tested headers. *)
  let offsets := table_offsets h_base n in
  let '(net, last_opt) := add_mergers h_out net prev_opt offsets in
  (* Copy the accumulated label from h_out into HeaderCtr 1, the header that
     dump_label emits as the program output.  Equivalence is checked over the
     deparser's emitted header, so the result must land there. *)
  let (net, copy_id) :=
    add_program_to_network net (CaracaraProgramDef [] [] [] (copy_to_out h_out)) in
  let net := match last_opt with
    | None      => net
    | Some last => add_connection_to_network net last copy_id
    end in
  let net := add_connection_to_network net copy_id (get_mod_name dump_label) in
  GeneralCaracaraProgramDef field_extractor_width [] net.

(* Every pattern tests a header [field_extractor] populates, at the int type
   that extract wrote.  Both are required: [CrVal.eqb] compares the CrIntType
   before the value, so a u32 src_ip tested at u8 can never match, and a header
   the parser never writes stays UninitVal and can never match either. *)
Definition SimpleDB : FilterDatabase :=
  [({|
      src_ip := [(h_src_ip, CmpEq, MatchConst (repr 0) u32)];
      dst_ip := [(h_dst_ip, CmpEq, MatchConst (repr 0) u32)];
      src_port := [(h_src_port, CmpEq, MatchConst (repr 0) u16)];
      dst_port := [(h_dst_port, CmpEq, MatchConst (repr 0) u16)];
      protocol := [(h_protocol, CmpEq, MatchConst (repr 1) u8)];
      key := 1%positive;
      priority := 1%positive |}, (repr 42));
    ({|
      (* Two src_ip components, so this filter's GetTuple shape is (2,1,1,1,1)
         rather than (1,1,1,1,1) and tss_db hashes it into a second table --
         which is the point of the example.  The parser exposes src_ip as one
         32-bit header, so the second component re-tests it; the redundancy is
         what gives the filter its distinct tuple shape. *)
      src_ip := [(h_src_ip, CmpEq, MatchConst (repr 0) u32);
                 (h_src_ip, CmpEq, MatchConst (repr 0) u32)];
      dst_ip := [(h_dst_ip, CmpEq, MatchConst (repr 0) u32)];
      src_port := [(h_src_port, CmpEq, MatchConst (repr 0) u16)];
      dst_port := [(h_dst_port, CmpEq, MatchConst (repr 0) u16)];
      protocol := [(h_protocol, CmpEq, MatchConst (repr 2) u8)];
      key := 2%positive;
      priority := 2%positive
    |}, (repr 67))
  ].
Definition ex_lin_prog : GeneralCaracaraProgram := linear_db SimpleDB.
Definition ex_tss_prog : GeneralCaracaraProgram := tss_db SimpleDB.

(* SimpleDB's two filters are mutually exclusive (protocol 1 vs 2), so it never
   exercises precedence.  OverlapDB's two filters match the SAME packet -- all
   fields zero, protocol 1 -- but have different tuple shapes, so tss_db hashes
   them into different tables and the merger has to arbitrate.  Lower priority
   number wins, so the expected label is 42, not 67. *)
Definition OverlapDB : FilterDatabase :=
  [({|
      src_ip := [(h_src_ip, CmpEq, MatchConst (repr 0) u32)];
      dst_ip := [(h_dst_ip, CmpEq, MatchConst (repr 0) u32)];
      src_port := [(h_src_port, CmpEq, MatchConst (repr 0) u16)];
      dst_port := [(h_dst_port, CmpEq, MatchConst (repr 0) u16)];
      protocol := [(h_protocol, CmpEq, MatchConst (repr 1) u8)];
      key := 1%positive;
      priority := 1%positive |}, (repr 42));
    ({|
      (* Same match conditions, distinct tuple shape (2,1,1,1,1), worse
         priority. *)
      src_ip := [(h_src_ip, CmpEq, MatchConst (repr 0) u32);
                 (h_src_ip, CmpEq, MatchConst (repr 0) u32)];
      dst_ip := [(h_dst_ip, CmpEq, MatchConst (repr 0) u32)];
      src_port := [(h_src_port, CmpEq, MatchConst (repr 0) u16)];
      dst_port := [(h_dst_port, CmpEq, MatchConst (repr 0) u16)];
      protocol := [(h_protocol, CmpEq, MatchConst (repr 1) u8)];
      key := 2%positive;
      priority := 2%positive
    |}, (repr 67))
  ].
Definition ex_lin_overlap : GeneralCaracaraProgram := linear_db OverlapDB.
Definition ex_tss_overlap : GeneralCaracaraProgram := tss_db OverlapDB.

(* A filter keyed on a NONZERO src_ip: 0x0A0B0C0D.  Its label is 42, while the
   low byte of that src_ip is 0x0D = 13, so "emitted the label" and "emitted
   whatever the parser left in (HeaderCtr 1)" are distinguishable outputs.

   That distinction is the one linear_db used to get wrong.  It accumulated its
   label in h_out but never copied it into (HeaderCtr 1), the header dump_label
   emits, so it emitted the low byte of the parsed src_ip and looked like a
   classifier returning plausible-but-wrong labels.  With SimpleDB, whose
   filters all require src_ip = 0, that bug emits 0 and is easy to mistake for
   "no match"; here it emits 13 and cannot be mistaken for anything. *)
Definition DistinctDB : FilterDatabase :=
  [({|
      src_ip := [(h_src_ip, CmpEq, MatchConst (repr 168496141) u32)]; (* 0x0A0B0C0D *)
      dst_ip := [(h_dst_ip, CmpEq, MatchConst (repr 0) u32)];
      src_port := [(h_src_port, CmpEq, MatchConst (repr 0) u16)];
      dst_port := [(h_dst_port, CmpEq, MatchConst (repr 0) u16)];
      protocol := [(h_protocol, CmpEq, MatchConst (repr 1) u8)];
      key := 1%positive;
      priority := 1%positive |}, (repr 42))
  ].
Definition ex_lin_distinct : GeneralCaracaraProgram := linear_db DistinctDB.
Definition ex_tss_distinct : GeneralCaracaraProgram := tss_db DistinctDB.
