From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.

From MyProject Require Import CrDsl.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import CrModule.
From MyProject Require Import CrParser.
From MyProject Require Import CrDeparser.
From MyProject Require Import Integers.
From MyProject Require Import Maps.
From MyProject Require Import CrVarLike.
From Stdlib Require Import Strings.String.

(* A target of the simple parser generator: extract [width] bits, found at
   [bit_pos] in the packet, into header [dst], coercing the value into type
   [ty]. *)
Record SimpleParserTarget : Type := SParserTgt {
  bit_pos : nat;
  width   : nat;
  dst     : positive;
  ty      : CrIntType;
}.

(* Insertion sort of targets by ascending bit position. *)
Fixpoint spg_insert (t : SimpleParserTarget) (ts : list SimpleParserTarget)
  : list SimpleParserTarget :=
  match ts with
  | [] => [t]
  | t' :: ts' =>
    if Nat.ltb (bit_pos t) (bit_pos t')
    then t :: ts
    else t' :: spg_insert t ts'
  end.
Fixpoint spg_sort (ts : list SimpleParserTarget) : list SimpleParserTarget :=
  match ts with
  | [] => []
  | t :: ts' => spg_insert t (spg_sort ts')
  end.

(* Flatten the sorted targets into the ordered list of parser ops, inserting a
   [SeekForward] to skip any gap between the cursor and the next target. *)
Fixpoint spg_ops (cursor : nat) (ts : list SimpleParserTarget) : list ParserOp :=
  match ts with
  | [] => []
  | t :: ts' =>
    let seek := if Nat.ltb cursor (bit_pos t)
                then [SeekForward (bit_pos t - cursor)]
                else [] in
    seek
      ++ ExtractOpConstructor (HeaderCtr (dst t)) (width t) (ty t)
      :: spg_ops (bit_pos t + width t) ts'
  end.

(* Turn a linear list of ops into a chain of parser states labelled [idx],
   [idx+1], ...  Each state performs one op and unconditionally transitions to
   the next; the final state accepts. *)
Fixpoint spg_states (idx : positive) (ops : list ParserOp)
  : list ParserStateDef :=
  match ops with
  | [] => []
  | op :: [] =>
    [mkParserStateDef (ParserStateLabelCtr idx) (Some op) (Unconditional Accept)]
  | op :: rest =>
    mkParserStateDef (ParserStateLabelCtr idx) (Some op)
      (Unconditional (TargetState (ParserStateLabelCtr (idx + 1))))
    :: spg_states (idx + 1) rest
  end.

Definition simple_parser_generator (targets : list SimpleParserTarget)
  : Parser :=
  (* sort targets by ascending bit position *)
  let sorted_targets := spg_sort targets in
  (* build a straight-line parser that extracts each header in order *)
  let states :=
    match spg_ops 0 sorted_targets with
    | [] =>
      (* no targets: a single accepting state that extracts nothing *)
      [mkParserStateDef (ParserStateLabelCtr 1) None (Unconditional Accept)]
    | ops => spg_states 1 ops
    end in
  mkParser (ParserStateLabelCtr 1) states.

Definition linear_dump_headers (hdrs : list (Header * nat)) : Deparser :=
  mkDeparser (List.map (fun '(h, w) => EmitOpConstructor h w) hdrs).

(* Single-module: unconditionally adds 3 to h1.
   h1=5 → h1=8. *)
Definition mod_prog_single_add3 : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      TransformerModule (ModuleNameCtr 2) [] [] [
        Seq (SeqCtr [] [
          StatelessOp AddOp u8
            (OpHeader (HeaderCtr 1))
            (OpConst (repr 3))
            (HeaderCtr 1)])];
      DeparserModule (ModuleNameCtr 3)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Two-module pipeline: module 1 adds 1, module 2 multiplies by 2.
   h1=5 → (5+1)*2 = 12. *)
Definition mod_prog_add1_then_mul2 : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      TransformerModule (ModuleNameCtr 2) [] [] [
        Seq (SeqCtr [] [
          StatelessOp AddOp u8
            (OpHeader (HeaderCtr 1))
            (OpConst (repr 1))
            (HeaderCtr 1)])];
      TransformerModule (ModuleNameCtr 3) [] [] [
        Seq (SeqCtr [] [
          StatelessOp MulOp u8
            (OpHeader (HeaderCtr 1))
            (OpConst (repr 2))
            (HeaderCtr 1)])];
      DeparserModule (ModuleNameCtr 4)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | ModuleNameCtr 3, ModuleNameCtr 4 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Two-module pipeline with conditional in the first module.
   Module 1: if h1 = 7 then h1 := 1 (no-op otherwise).
   Module 2: h1 := h1 + 10.
   h1=7 → 1 → 11.  h1=3 → 3 → 13. *)
Definition mod_prog_conditional_pipeline : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      TransformerModule (ModuleNameCtr 2) [] [] [
        Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchConst (repr 7) u8)] [
          StatelessOp AddOp u8
            (OpConst (repr 1))
            (OpConst (repr 0))
            (HeaderCtr 1)]);
        Seq (SeqCtr [] [])];
      TransformerModule (ModuleNameCtr 3) [] [] [
        Seq (SeqCtr [] [
          StatelessOp AddOp u8
            (OpHeader (HeaderCtr 1))
            (OpConst (repr 10))
            (HeaderCtr 1)])];
      DeparserModule (ModuleNameCtr 4)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | ModuleNameCtr 3, ModuleNameCtr 4 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Two-module pipeline exercising CmpLt with MatchHeader.
   Module 1: if h1 < h2 then h1 := h1 + h2.
   Module 2: h1 := h1 + 1.
   h1=3, h2=5 → 3<5 fires → h1=8 → h1=9.
   h1=5, h2=3 → no match  → h1=5 → h1=6. *)
Definition mod_prog_cmplt_matchheader : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 16 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8; SParserTgt 8 8 2 u8]);
      TransformerModule (ModuleNameCtr 2) [] [] [
        Seq (SeqCtr [(HeaderCtr 1, CmpLt, MatchHeader (HeaderCtr 2))] [
          StatelessOp AddOp u8
            (OpHeader (HeaderCtr 1))
            (OpHeader (HeaderCtr 2))
            (HeaderCtr 1)]);
        Seq (SeqCtr [] [])];
      TransformerModule (ModuleNameCtr 3) [] [] [
        Seq (SeqCtr [] [
          StatelessOp AddOp u8
            (OpHeader (HeaderCtr 1))
            (OpConst (repr 1))
            (HeaderCtr 1)])];
      DeparserModule (ModuleNameCtr 4)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | ModuleNameCtr 3, ModuleNameCtr 4 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).


(* Two parser modules in a pipeline: parser 1 extracts a byte into h1, parser 2
   extracts a byte (from its own packet) into h2, carrying h1 forward. *)
Definition mod_prog_two_parsers : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 16 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      ParserModule (ModuleNameCtr 2)
        (simple_parser_generator [SParserTgt 0 8 2 u8]);
      DeparserModule (ModuleNameCtr 3)
        (linear_dump_headers [(HeaderCtr 1, 8); (HeaderCtr 2, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Bitstream I/O pipeline: a parser extracts two bytes into h1, h2; a deparser
   re-emits h1, h2 (prepending them to any residual payload).  This is the
   inverse-pair pipeline used to exercise the bitstream [modnet_equivalence_checker]:
   parse-then-deparse reproduces the input packet, so the pipeline is
   equivalent to itself over any input bitstream. *)
Definition mod_prog_parse_deparse : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 16 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8; SParserTgt 8 8 2 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8); (HeaderCtr 2, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Same parser, but the deparser emits the two headers in swapped order.  This
   pipeline is NOT equivalent to [mod_prog_parse_deparse]: on any input whose two
   bytes differ, the emitted output packets differ. *)
Definition mod_prog_parse_deparse_swapped : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 16 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8; SParserTgt 8 8 2 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 2, 8); (HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Bitstream pipeline whose parser REJECTS the one-byte packet 0xFF (via a
   [select] case) and otherwise accepts, extracting the byte into h1; a deparser
   re-emits h1.  Paired with [mod_prog_parse_accept_deparse] below (identical but
   always-accepting) to exercise accept/reject handling in the bitstream
   [modnet_equivalence_checker]: the two agree on every packet except 0xFF, where
   one rejects and the other accepts.  The old swallow-the-reject symbolic
   semantics wrongly called them equivalent. *)
Definition mod_prog_parse_reject_deparse : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (mkParser (ParserStateLabelCtr 1) [
          mkParserStateDef (ParserStateLabelCtr 1)
            (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
            (Select [mkSelectCase (HeaderCtr 1) 0 8
                       [true;true;true;true;true;true;true;true] Reject]
                    Accept)]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Always-accepting counterpart of [mod_prog_parse_reject_deparse]. *)
Definition mod_prog_parse_accept_deparse : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Residual-packet pipelines.  These consume a nonzero number of bits and emit
   fewer than they consume, so the deparser output = emitted ++ (unconsumed tail).
   They exercise the cursor/residual: the old "reset the cursor to 0, hand the
   whole packet downstream" symbolic semantics would give the wrong output. *)

(* Consume one byte into h1, emit h1: output = byte0 ++ (input past byte 0). *)
Definition mod_prog_consume1_emit1 : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 24 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Consume TWO bytes (h1, h2) but emit only h1: output = byte0 ++ (input past
   byte 1) — it drops byte 1.  Not equivalent to [mod_prog_consume1_emit1], which
   keeps byte 1; the old whole-packet residual wrongly called them equivalent. *)
Definition mod_prog_consume2_emit1 : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 24 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8; SParserTgt 8 8 2 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* DATA-DEPENDENT consumption: extract h1, then if h1 = 0 accept (consumed one
   byte), else extract h2 and accept (consumed two bytes).  Emit h1.  The
   unconsumed-tail length depends on the input, so its residual is a genuinely
   variable-length bitstream (exercises [merge_bitstream]). *)
Definition mod_prog_varlen_emit1 : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 24 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (mkParser (ParserStateLabelCtr 1) [
          mkParserStateDef (ParserStateLabelCtr 1)
            (Some (ExtractOpConstructor (HeaderCtr 1) 8 u64))
            (Select [mkSelectCase (HeaderCtr 1) 0 8
                       [false;false;false;false;false;false;false;false] Accept]
                    (TargetState (ParserStateLabelCtr 2)));
          mkParserStateDef (ParserStateLabelCtr 2)
            (Some (ExtractOpConstructor (HeaderCtr 2) 8 u64))
            (Unconditional Accept)]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* ---------------------------------------------------------------------- *)
(* Why a match-action rule silently never fires.                          *)
(*                                                                        *)
(* Both of the ways below made every filter in PktClass's databases       *)
(* match nothing, which is what let linear_db and tss_db disagree while   *)
(* still looking plausible: neither classifier was classifying at all.    *)
(* They are properties of the IR's match semantics, not of PktClass, so   *)
(* they are pinned down here on the smallest programs that exhibit them.  *)
(*                                                                        *)
(* All three share a shape: parse byte 0 into a header, run one guarded   *)
(* rule that would set h2 := 99, and emit h2.  They differ only in        *)
(* whether the guard can fire.  When it does not, h2 is never written, so *)
(* the (total) deparser emits it as zero bits.                            *)
(* ---------------------------------------------------------------------- *)

Definition set_h2_when (guard : MatchPattern) : Transformer :=
  [Seq (SeqCtr guard
     [StatelessOp AddOp u8 (OpConst (repr 99)) (OpConst (repr 0)) (HeaderCtr 2)])].

Definition guarded_parse_emit (extract_ty : CrIntType) (guard : MatchPattern)
  : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 extract_ty]);
      TransformerModule (ModuleNameCtr 2) [] [] (set_h2_when guard);
      DeparserModule (ModuleNameCtr 3)
        (linear_dump_headers [(HeaderCtr 2, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* Baseline: the guard tests h1 against a u8 constant and the parser extracted
   h1 at u8, so the types agree and the rule fires on the packet [5]. *)
Definition mod_prog_guard_type_agrees : GeneralCaracaraProgram :=
  guarded_parse_emit u8 [(HeaderCtr 1, CmpEq, MatchConst (repr 5) u8)].

(* Same guard and same packet, but h1 is extracted at u64.  [CrVal.eqb] compares
   the CrIntType before the value, so this rule can never fire for ANY packet.
   This is the bug that made every PktClass filter dead: field_extractor wrote
   u64 and the databases matched at u8. *)
Definition mod_prog_guard_type_differs : GeneralCaracaraProgram :=
  guarded_parse_emit u64 [(HeaderCtr 1, CmpEq, MatchConst (repr 5) u8)].

(* The guard tests h3, which no module in the network ever writes.  It stays
   UninitVal, and [CrVal.eqb] is false on UninitVal, so again the rule can never
   fire.  PktClass's databases tested a protocol header the parser never
   populated, which failed exactly this way. *)
Definition mod_prog_guard_unwritten : GeneralCaracaraProgram :=
  guarded_parse_emit u8 [(HeaderCtr 3, CmpEq, MatchConst (repr 0) u8)].

(* Two deparsers in a chain: parser reads two bytes into h1, h2; deparser 2
   emits h1; deparser 3 emits h2.  Both write the network's shared write tape,
   so this pins down whether a second deparser appends to the first's output or
   replaces it. *)
Definition mod_prog_two_deparsers : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 16 []
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8; SParserTgt 8 8 2 u8]);
      DeparserModule (ModuleNameCtr 2)
        (linear_dump_headers [(HeaderCtr 1, 8)]);
      DeparserModule (ModuleNameCtr 3)
        (linear_dump_headers [(HeaderCtr 2, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

(* ------------------------------------------------------------------ *)
(* Memory programs.

   All of these share one shape -- parse a byte into h1, run a transformer that
   touches memory and leaves its result in h2, emit h2 -- and one declared
   region: [region_1], four cells, so offsets 0..3 are in bounds and 4 is not.
   h2 is written only by the transformer -- no parser extracts it -- which
   deliberately exercises header seeding ([CrVarLike.collect_write_headers]).

   A cell that was never written reads [UninitVal], which fails the load's type
   check and lands as ErrorVal; a deparser is total and emits a non-integer
   header as zero bits of its full width.  So a program that only ever loads
   emits a zero byte, and two such programs agree on their output -- which is
   why the extent conjunct is what separates several of these pairs. *)
Definition region_1 : MemRegion := MemRegionCtr 1.
Definition mem_regions_4 : list MemRegionDecl := [mkMemRegionDecl region_1 4].

Definition mem_prog_rules (rules : Transformer) : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 8 mem_regions_4
    (mkModuleNetwork [
      ParserModule (ModuleNameCtr 1)
        (simple_parser_generator [SParserTgt 0 8 1 u8]);
      TransformerModule (ModuleNameCtr 2) [] [] rules;
      DeparserModule (ModuleNameCtr 3)
        (linear_dump_headers [(HeaderCtr 2, 8)])]
      (fun m1 m2 =>
        match m1, m2 with
        | ModuleNameCtr 1, ModuleNameCtr 2 => true
        | ModuleNameCtr 2, ModuleNameCtr 3 => true
        | _, _ => false
        end)
      (ModuleNameCtr 1)).

Definition mem_prog (ops : list HdrOp) : GeneralCaracaraProgram :=
  mem_prog_rules [Seq (SeqCtr [] ops)].

(* Store the parsed byte at offset 2, read it straight back. *)
Definition mod_prog_mem_store_load : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u8 region_1 (OpConst (repr 2)) (OpHeader (HeaderCtr 1));
    LoadOp  u8 region_1 (OpConst (repr 2)) (HeaderCtr 2)].

(* Same, but the offset is computed into h3 rather than written literally.
   Equivalent to the above: which header holds the address is not observable. *)
Definition mod_prog_mem_store_load_alias : GeneralCaracaraProgram :=
  mem_prog [
    StatelessOp AddOp u64 (OpConst (repr 0)) (OpConst (repr 2)) (HeaderCtr 3);
    StoreOp u8 region_1 (OpConst (repr 2)) (OpHeader (HeaderCtr 1));
    LoadOp  u8 region_1 (OpHeader (HeaderCtr 3)) (HeaderCtr 2)].

(* Stores a different value: same extent, same shape, differing contents. *)
Definition mod_prog_mem_store_load_differs : GeneralCaracaraProgram :=
  mem_prog [
    StatelessOp AddOp u8 (OpHeader (HeaderCtr 1)) (OpConst (repr 1)) (HeaderCtr 4);
    StoreOp u8 region_1 (OpConst (repr 2)) (OpHeader (HeaderCtr 4));
    LoadOp  u8 region_1 (OpConst (repr 2)) (HeaderCtr 2)].

(* A dead load at offset 1 before the real one at offset 0.  Reaches further
   into the region than [mem_load0] while emitting the same packet. *)
Definition mod_prog_mem_load1_load0 : GeneralCaracaraProgram :=
  mem_prog [
    LoadOp u8 region_1 (OpConst (repr 1)) (HeaderCtr 3);
    LoadOp u8 region_1 (OpConst (repr 0)) (HeaderCtr 2)].

(* The same, into a different scratch header: internal, so equivalent. *)
Definition mod_prog_mem_load1_load0_alt : GeneralCaracaraProgram :=
  mem_prog [
    LoadOp u8 region_1 (OpConst (repr 1)) (HeaderCtr 4);
    LoadOp u8 region_1 (OpConst (repr 0)) (HeaderCtr 2)].

Definition mod_prog_mem_load0 : GeneralCaracaraProgram :=
  mem_prog [LoadOp u8 region_1 (OpConst (repr 0)) (HeaderCtr 2)].

(* In bounds, the order of a load and a store to the same cell is observable. *)
Definition mod_prog_mem_ib_load_store : GeneralCaracaraProgram :=
  mem_prog [
    LoadOp  u8 region_1 (OpConst (repr 2)) (HeaderCtr 2);
    StoreOp u8 region_1 (OpConst (repr 2)) (OpHeader (HeaderCtr 1))].

(* Out of bounds (offset 4 in a 4-cell region), it is not: the store is dropped
   and the load yields ErrorVal either way.  This pair is equivalent only if
   the Z3 lowering guards [select] with the declared length -- Z3's array
   theory is total, so an unguarded encoding would let the second program read
   its own out-of-bounds store back and the checker would report a difference
   the concrete semantics cannot produce. *)
Definition mod_prog_mem_oob_load_store : GeneralCaracaraProgram :=
  mem_prog [
    LoadOp  u8 region_1 (OpConst (repr 4)) (HeaderCtr 2);
    StoreOp u8 region_1 (OpConst (repr 4)) (OpHeader (HeaderCtr 1))].

Definition mod_prog_mem_oob_store_load : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u8 region_1 (OpConst (repr 4)) (OpHeader (HeaderCtr 1));
    LoadOp  u8 region_1 (OpConst (repr 4)) (HeaderCtr 2)].

(* Multi-byte access.  A region is an array of bytes, so a u16 store covers two
   cells little-endian and is EXACTLY the two u8 stores an optimiser coalesces
   it from.  Under the old one-value-per-cell model these two were reported
   inequivalent -- a real false positive on -O0 vs -O2 pairs, since -O2 merges
   adjacent narrow stores. *)
Definition mod_prog_mem_two_u8_stores : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u8 region_1 (OpConst (repr 0)) (OpConst (repr 52));   (* 0x34 *)
    StoreOp u8 region_1 (OpConst (repr 1)) (OpConst (repr 18));   (* 0x12 *)
    LoadOp  u8 region_1 (OpConst (repr 0)) (HeaderCtr 2)].

Definition mod_prog_mem_one_u16_store : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u16 region_1 (OpConst (repr 0)) (OpConst (repr 4660));  (* 0x1234 *)
    LoadOp  u8  region_1 (OpConst (repr 0)) (HeaderCtr 2)].

(* Storing a header that was never written.  [apply_cast ty ty] rejects a
   non-integer, and [byte_of_val] sends the result to ErrorVal, so EVERY cell
   the store covers ends up holding a poisoned value rather than a number --
   [Init ErrorVal], which the region printer shows as [!] and which no other
   program here produces.  The load then reads one back, so h2 is poisoned too
   and the deparser emits a zero byte. *)
Definition mod_prog_mem_store_poisoned : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u16 region_1 (OpConst (repr 0)) (OpHeader (HeaderCtr 9));
    LoadOp  u8  region_1 (OpConst (repr 0)) (HeaderCtr 2)].

(* And the other direction: two byte stores read back as one u16 reassemble
   little-endian.  The low byte reaches the deparser. *)
Definition mod_prog_mem_u16_readback : GeneralCaracaraProgram :=
  mem_prog [
    StoreOp u8 region_1 (OpConst (repr 0)) (OpConst (repr 52));
    StoreOp u8 region_1 (OpConst (repr 1)) (OpConst (repr 18));
    LoadOp  u16 region_1 (OpConst (repr 0)) (HeaderCtr 3);
    CastHeaderOp u16 u8 (OpHeader (HeaderCtr 3)) (HeaderCtr 2)].

(* A guard that cannot fail is the same as no guard.  [CrVal.eqb] is reflexive
   on every constructor -- including [UninitVal] and [ErrorVal] -- so comparing
   a header to itself always holds, and this must be equivalent to
   [mem_store_load], which runs the same ops unguarded.

   This replaces the retired memory IR's "a branch on a constant collapses"
   (a [BrzOp] on 0 against its taken arm inlined).  There is no direct
   translation: the unified IR has no nested conditional, so the analogue of a
   statically-true branch is a tautological match pattern. *)
Definition mod_prog_mem_guard_tautology : GeneralCaracaraProgram :=
  mem_prog_rules [
    Seq (SeqCtr [(HeaderCtr 1, CmpEq, MatchHeader (HeaderCtr 1))] [
      StoreOp u8 region_1 (OpConst (repr 2)) (OpHeader (HeaderCtr 1));
      LoadOp  u8 region_1 (OpConst (repr 2)) (HeaderCtr 2)]);
    Seq (SeqCtr [] [])].

(* Port of the spec that ParserHawk uses for sai:
   https://github.com/ParserHawk/ParserHawk/blob/17be2c8a65a72dac59b2d33642a026d4ef9e90e3/z3/cegis_loop/one_short_revision/P4_examples/sai_v4_pkt_eth_v46_inv4_udp_tcp_icmp_arp/sai_v4_pkt_eth_v46_inv4_udp_tcp_icmp_arp_tofino_op.py#L165 *)
Definition parserhawk_sai_spec_parser : Parser := {|
  parser_start := ParserStateLabelCtr 1;
  parser_states := [
    mkParserStateDef (ParserStateLabelCtr 1)
        (Some (ExtractOpConstructor (HeaderCtr 1) 1 u8))
        (Unconditional (TargetState (ParserStateLabelCtr 2)));
    mkParserStateDef (ParserStateLabelCtr 2)
      (Some (ExtractOpConstructor (HeaderCtr 2) 16 u16))
      (Select [
        mkSelectCase (HeaderCtr 2) 0 16
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false; false; false; false] (* 0x0800 *)
          (TargetState (ParserStateLabelCtr 3));
        mkSelectCase (HeaderCtr 2) 0 16
          [ true; false; false; false; false;  true;  true; false;
            true;  true; false;  true;  true;  true; false;  true] (* 0x86dd *)
          (TargetState (ParserStateLabelCtr 4));
        mkSelectCase (HeaderCtr 2) 0 16
          [false; false; false; false;  true; false; false; false;
            false; false; false; false; false;  true;  true; false] (* 0x0806 *)
          (TargetState (ParserStateLabelCtr 5))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 3)
      (Some (ExtractOpConstructor (HeaderCtr 3) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false;  true; false; false] (* 0x04 *)
          (TargetState (ParserStateLabelCtr 6));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 3) 0 8
          [false; false; false; false; false; false; false;  true] (* 0x01 *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 4)
      (Some (ExtractOpConstructor (HeaderCtr 4) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 4) 0 8
          [false; false;  true;  true;  true; false;  true; false] (* 0x3a *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 5)
      (Some (ExtractOpConstructor (HeaderCtr 9) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 6)
      (Some (ExtractOpConstructor (HeaderCtr 5) 8 u8))
      (Select [
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false;  true; false; false; false;  true] (* 0x11 *)
          (TargetState (ParserStateLabelCtr 7));
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false; false; false;  true;  true; false] (* 0x06 *)
          (TargetState (ParserStateLabelCtr 8));
        mkSelectCase (HeaderCtr 5) 0 8
          [false; false; false; false; false; false; false;  true] (* 0x01 *)
          (TargetState (ParserStateLabelCtr 9))
      ] Accept);
    mkParserStateDef (ParserStateLabelCtr 7)
      (Some (ExtractOpConstructor (HeaderCtr 6) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 8)
      (Some (ExtractOpConstructor (HeaderCtr 7) 1 u8))
      (Unconditional Accept);
    mkParserStateDef (ParserStateLabelCtr 9)
      (Some (ExtractOpConstructor (HeaderCtr 8) 1 u8))
      (Unconditional Accept)
  ];
|}.

Record sai_headers := {
  h1 : Header; h2 : Header; h3 : Header;
  h4 : Header; h5 : Header; h6 : Header;
  h7 : Header; h8 : Header; h9 : Header
}.
Definition sai_dump_headers (p : Parser) (ordering : sai_headers) : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef 34 [] {|
    net_modules := [
      ParserModule (ModuleNameCtr 1) p;
      DeparserModule (ModuleNameCtr 2) (mkDeparser [
        EmitOpConstructor (h1 ordering) 1;
        EmitOpConstructor (h2 ordering) 16;
        EmitOpConstructor (h3 ordering) 8;
        EmitOpConstructor (h4 ordering) 8;
        EmitOpConstructor (h5 ordering) 8;
        EmitOpConstructor (h6 ordering) 1;
        EmitOpConstructor (h7 ordering) 1;
        EmitOpConstructor (h8 ordering) 1;
        EmitOpConstructor (h9 ordering) 1
      ])
    ];
    net_edges := fun a b => 
      match a, b with
      | ModuleNameCtr 1, ModuleNameCtr 2 => true
      | _, _ => false
      end;
    start_module := ModuleNameCtr 1;
  |}.

(* dumps 9 header fields next to one another *)
Definition parserhawk_sai_spec :=
  sai_dump_headers parserhawk_sai_spec_parser {|
    h1 := HeaderCtr 1; h2 := HeaderCtr 2; h3 := HeaderCtr 3;
    h4 := HeaderCtr 4; h5 := HeaderCtr 5; h6 := HeaderCtr 6;
    h7 := HeaderCtr 7; h8 := HeaderCtr 8; h9 := HeaderCtr 9
  |}.

(* The single registry of module test programs, keyed by name.

   [Extraction.v] extracts this tree rather than each program individually, so
   adding a program to the association list below is all that is needed to
   reach it from OCaml, as [ModProgs.find "<name>"].  Order does not matter and
   there are no indices to keep in step: the key is [string_to_pos] of the name.

   A [PTree] rather than a [PMap] because [PTree.get] returns an option --
   asking for a name that is not here should fail, not silently hand back some
   default program. *)
Local Open Scope string_scope.
Definition mod_test_program_list
  : list (string * GeneralCaracaraProgram) := [
  ("single_add3",          mod_prog_single_add3);
  ("add1_then_mul2",       mod_prog_add1_then_mul2);
  ("conditional_pipeline", mod_prog_conditional_pipeline);
  ("cmplt_matchheader",    mod_prog_cmplt_matchheader);
  ("two_parsers",          mod_prog_two_parsers);
  ("parse_deparse",        mod_prog_parse_deparse);
  ("parse_deparse_swapped",mod_prog_parse_deparse_swapped);
  ("parse_reject_deparse", mod_prog_parse_reject_deparse);
  ("parse_accept_deparse", mod_prog_parse_accept_deparse);
  ("consume1_emit1",       mod_prog_consume1_emit1);
  ("consume2_emit1",       mod_prog_consume2_emit1);
  ("varlen_emit1",         mod_prog_varlen_emit1);
  ("guard_type_agrees",    mod_prog_guard_type_agrees);
  ("guard_type_differs",   mod_prog_guard_type_differs);
  ("guard_unwritten",      mod_prog_guard_unwritten);
  ("two_deparsers",        mod_prog_two_deparsers);
  ("mem_store_load",         mod_prog_mem_store_load);
  ("mem_store_load_alias",   mod_prog_mem_store_load_alias);
  ("mem_store_load_differs", mod_prog_mem_store_load_differs);
  ("mem_load1_load0",        mod_prog_mem_load1_load0);
  ("mem_load1_load0_alt",    mod_prog_mem_load1_load0_alt);
  ("mem_load0",              mod_prog_mem_load0);
  ("mem_ib_load_store",      mod_prog_mem_ib_load_store);
  ("mem_oob_load_store",     mod_prog_mem_oob_load_store);
  ("mem_oob_store_load",     mod_prog_mem_oob_store_load);
  ("mem_guard_tautology",    mod_prog_mem_guard_tautology);
  ("mem_two_u8_stores",      mod_prog_mem_two_u8_stores);
  ("mem_one_u16_store",      mod_prog_mem_one_u16_store);
  ("mem_store_poisoned",     mod_prog_mem_store_poisoned);
  ("mem_u16_readback",       mod_prog_mem_u16_readback)
].

Definition mod_test_programs : PTree.t GeneralCaracaraProgram :=
  List.fold_left
    (fun acc np => PTree.set (string_to_pos (fst np)) (snd np) acc)
    mod_test_program_list
    (PTree.empty GeneralCaracaraProgram).

(* The exported interface to the registry.  OCaml calls this rather than
   reaching into the tree itself, so the key encoding stays entirely on this
   side -- there is no [string_to_pos] to re-apply, and no way for the two sides
   to disagree about how a name maps to a key.  [None] for an unknown name. *)
Definition lookup_mod_test_program (name : string)
  : option GeneralCaracaraProgram :=
  PTree.get (string_to_pos name) mod_test_programs.

(* Exported alongside the lookup so the OCaml side can tell whether a program
   was added to the registry but never given a binding. *)
Definition mod_test_program_names : list string :=
  List.map fst mod_test_program_list.
Local Close Scope string_scope.
