(* Every module network starts with a parser and ends in a deparser, so the only
   way in is the network's input packet: [seed] injects it into the initial
   general state's read tape, and the start parser extracts the headers from it.
   Programs are addressed by name via ModProgs, which looks them up in the Rocq
   registry. *)
let run_named_prog name p seed =
  Shim.print_malformed_gprog p name;
  let gcs0 = CrVarLike.init_general_concrete_state p in
  match CrConcreteSemanticsModule.eval_general_program_concrete p (seed gcs0) with
  | None -> failwith ("eval_general_program_concrete returned None for " ^ name)
  | Some s -> s

let run_net name seed = run_named_prog name (Shim.find_modprog name) seed

let run name bytes = run_net name (Shim.set_net_packet bytes)

(* ------------------------------------------------------------------ *)
(* mod_prog_single_add3 (pid 0): parser byte0 -> h1; h1 := h1 + 3     *)
(* ------------------------------------------------------------------ *)

let%expect_test "single_add3: packet [5] -> h1=8" =
  Shim.print_general_state (run "single_add3" [5]);
  [%expect {|
    Module 1:
      h1=5
    Module 2:
      h1=8
    Module 3:
      h1=8
  |}]

let%expect_test "single_add3: packet [0] -> h1=3" =
  Shim.print_general_state (run "single_add3" [0]);
  [%expect {|
    Module 1:
      h1=0
    Module 2:
      h1=3
    Module 3:
      h1=3
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_add1_then_mul2 (pid 1): h1 -> (h1+1)*2                    *)
(* ------------------------------------------------------------------ *)

let%expect_test "add1_then_mul2: packet [5] -> 12" =
  Shim.print_general_state (run "add1_then_mul2" [5]);
  [%expect {|
    Module 1:
      h1=5
    Module 2:
      h1=6
    Module 3:
      h1=12
    Module 4:
      h1=12
  |}]

let%expect_test "add1_then_mul2: packet [0] -> 2 (0+1)*2" =
  Shim.print_general_state (run "add1_then_mul2" [0]);
  [%expect {|
    Module 1:
      h1=0
    Module 2:
      h1=1
    Module 3:
      h1=2
    Module 4:
      h1=2
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_conditional_pipeline (pid 2)                              *)
(*   Module 2: h1=7 -> h1:=1, else no-op.  Module 3: h1 := h1+10.     *)
(* ------------------------------------------------------------------ *)

let%expect_test "conditional_pipeline: packet [7] hits guard -> 11" =
  Shim.print_general_state (run "conditional_pipeline" [7]);
  [%expect {|
    Module 1:
      h1=7
    Module 2:
      h1=1
    Module 3:
      h1=11
    Module 4:
      h1=11
  |}]

let%expect_test "conditional_pipeline: packet [3] misses guard -> 13" =
  Shim.print_general_state (run "conditional_pipeline" [3]);
  [%expect {|
    Module 1:
      h1=3
    Module 2:
      h1=3
    Module 3:
      h1=13
    Module 4:
      h1=13
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_cmplt_matchheader (pid 3)                                 *)
(*   Module 2: h1<h2 -> h1:=h1+h2.  Module 3: h1 := h1+1.             *)
(* ------------------------------------------------------------------ *)

let%expect_test "cmplt_matchheader: packet [3;5] fires -> h1=9" =
  Shim.print_general_state (run "cmplt_matchheader" [3; 5]);
  [%expect {|
    Module 1:
      h1=3, h2=5
    Module 2:
      h1=8, h2=5
    Module 3:
      h1=9, h2=5
    Module 4:
      h1=9, h2=5
  |}]

let%expect_test "cmplt_matchheader: packet [5;3] no match -> h1=6" =
  Shim.print_general_state (run "cmplt_matchheader" [5; 3]);
  [%expect {|
    Module 1:
      h1=5, h2=3
    Module 2:
      h1=5, h2=3
    Module 3:
      h1=6, h2=3
    Module 4:
      h1=6, h2=3
  |}]

let%expect_test "cmplt_matchheader: packet [4;4] equal, no match -> h1=5" =
  Shim.print_general_state (run "cmplt_matchheader" [4; 4]);
  [%expect {|
    Module 1:
      h1=4, h2=4
    Module 2:
      h1=4, h2=4
    Module 3:
      h1=5, h2=4
    Module 4:
      h1=5, h2=4
  |}]

(* e2e: packet threading through two parser modules.  The single network packet
   [7;42] flows through: parser 1 consumes byte 7 into h1, hands the residual
   [42] to parser 2, which consumes 42 into h2 (carrying h1 forward). *)
let%expect_test "two_parsers: packet [7;42] threads -> h1=7, h2=42" =
  Shim.print_general_state (run "two_parsers" [7; 42]);
  [%expect {|
    Module 1:
      h1=7, h2=0
    Module 2:
      h1=7, h2=42
    Module 3:
      h1=7, h2=42
    |}]

(* ------------------------------------------------------------------ *)
(* sh_bits_read: how much of the input packet the network consumed.   *)
(* ------------------------------------------------------------------ *)

(* One parser, one 8-bit extract. *)
let%expect_test "bits_read: single_add3 consumes one byte" =
  Shim.print_net_bits_read (run "single_add3" [5]);
  [%expect {| bits_read=8 |}]

(* Two 8-bit extracts in the same parser. *)
let%expect_test "bits_read: cmplt_matchheader consumes two bytes" =
  Shim.print_net_bits_read (run "cmplt_matchheader" [3; 5]);
  [%expect {| bits_read=16 |}]

(* Chained parsers: the count accumulates across the chain -- parser 1 reads a
   byte and parser 2 reads a byte of the residual. *)
let%expect_test "bits_read: two_parsers accumulates across the chain" =
  Shim.print_net_bits_read (run "two_parsers" [7; 42]);
  [%expect {| bits_read=16 |}]

(* e2e: parse-then-deparse reproduces the input packet.  The deparser's output
   packet is the network's write tape, so this pins down the bitstream I/O the
   [modnet_equivalence_checker] reasons about symbolically. *)
let%expect_test "parse_deparse: packet [0x12;0x34] round-trips" =
  Shim.print_net_output (run "parse_deparse" [0x12; 0x34]);
  [%expect {| [18, 52] 16b |}]

(* Same parser, deparser emits the two headers in the other order. *)
let%expect_test "parse_deparse_swapped: packet [0x12;0x34] -> bytes swapped" =
  Shim.print_net_output (run "parse_deparse_swapped" [0x12; 0x34]);
  [%expect {| [52, 18] 16b |}]

(* --------------------------------------------------------------------- *)
(* PktClass: linear-scan vs tuple-space-search classifiers.              *)
(*                                                                       *)
(* These are concrete on purpose.  Test 13 in TestEquality runs the same *)
(* two programs through modnet_equivalence_checker, and it reported      *)
(* Equivalent throughout a period when tss_db rejected every packet and  *)
(* linear_db emitted a label -- a symbolic checker comparing output      *)
(* packets cannot pin down WHICH label a classifier produces.  Checking  *)
(* concrete labels here is what makes these two constructions actually   *)
(* agree rather than merely fail to be distinguished.                    *)
(* --------------------------------------------------------------------- *)

(* Run a standalone GeneralCaracaraProgram on a byte packet; print the emitted
   output packet, or "reject" if the network invalidated.  Only a parser can
   invalidate a network now -- a deparser is total, so emitting a header that
   holds no integer yields zero bits rather than a reject. *)
let run_prog p bytes =
  let gcs0 = CrVarLike.init_general_concrete_state p in
  match CrConcreteSemanticsModule.eval_general_program_concrete p
          (Shim.set_net_packet bytes gcs0) with
  | None -> print_endline "reject (None)"
  | Some s ->
    (match s.CrGeneralProgramState.gps_valid with
     | Datatypes.Coq_false -> print_endline "reject"
     | Datatypes.Coq_true -> Shim.print_net_output s)

(* field_extractor's layout: protocol @ byte 9, src_ip @ 12-15, dst_ip @ 16-19,
   src_port @ 20-21, dst_port @ 22-23.  SimpleDB's filters want every field zero
   and select on protocol: 1 -> label 42, 2 -> label 67. *)
let pkt ?(src_ip0 = 0) proto =
  Stdlib.List.init 24 (fun i ->
    if i = 9 then proto else if i = 12 then src_ip0 else 0)

let both bytes =
  print_string "lin: "; run_prog PktClass.ex_lin_prog bytes;
  print_string "tss: "; run_prog PktClass.ex_tss_prog bytes

let%expect_test "pktclass: protocol 1 classifies to label 42 in both" =
  both (pkt 1);
  [%expect {|
    lin: [42] 8b
    tss: [42] 8b
    |}]

let%expect_test "pktclass: protocol 2 classifies to label 67 in both" =
  both (pkt 2);
  [%expect {|
    lin: [67] 8b
    tss: [67] 8b
    |}]

(* No filter matches: h_out is never written, so the copy-to-output leaves
   (HeaderCtr 1) non-integer.  A deparser is total (see
   [eval_deparser_concrete]), so emitting a non-integer header yields zero bits
   rather than rejecting -- hence 0 rather than a reject.  What matters is that
   both constructions agree, which is why tss_db seeds only the priority
   accumulator and not h_out itself. *)
let%expect_test "pktclass: unknown protocol emits 0 in both" =
  both (pkt 3);
  [%expect {|
    lin: [0] 8b
    tss: [0] 8b
    |}]

(* Protocol matches a filter but another field does not. *)
let%expect_test "pktclass: nonzero src_ip emits 0 in both" =
  both (pkt ~src_ip0:7 1);
  [%expect {|
    lin: [0] 8b
    tss: [0] 8b
    |}]

(* Precedence: OverlapDB's two filters both match a protocol-1 packet but sit in
   different tables (different tuple shapes).  A LOWER priority number means
   HIGHER precedence, so the priority-1 filter's label 42 must win in both
   constructions -- linear_db by taking the first rule in ascending-priority
   order, tss_db by the merger only displacing the accumulator on a strictly
   smaller priority. *)
let both_overlap bytes =
  print_string "lin: "; run_prog PktClass.ex_lin_overlap bytes;
  print_string "tss: "; run_prog PktClass.ex_tss_overlap bytes

let%expect_test "pktclass precedence: lower priority number wins in both" =
  both_overlap (pkt 1);
  [%expect {|
    lin: [42] 8b
    tss: [42] 8b
    |}]

let%expect_test "pktclass precedence: no match emits 0 in both" =
  both_overlap (pkt 3);
  [%expect {|
    lin: [0] 8b
    tss: [0] 8b
    |}]

(* --------------------------------------------------------------------- *)
(* Why a match-action rule silently never fires.                         *)
(*                                                                       *)
(* These are the two root causes behind the PktClass divergence, reduced *)
(* to the smallest networks that show them.  Both are silent: the rule   *)
(* simply never fires, the guarded header is never written, and the      *)
(* deparser emits zeros -- there is no error anywhere to notice.         *)
(* --------------------------------------------------------------------- *)

(* Baseline: guard type matches the extract type, so the rule fires. *)
let%expect_test "match guard: u8 extract vs u8 constant fires" =
  run_prog (Shim.find_modprog "guard_type_agrees") [5];
  [%expect {| [99] 8b |}]

(* Same packet, same constant, only the extract type differs.  CrVal.eqb
   compares the CrIntType before the value, so this never fires -- for any
   packet, not just this one. *)
let%expect_test "match guard: u64 extract vs u8 constant never fires" =
  run_prog (Shim.find_modprog "guard_type_differs") [5];
  [%expect {| [0] 8b |}]

(* And it really is type, not value: the packet whose byte IS 5 still fails. *)
let%expect_test "match guard: u64/u8 mismatch fails on every packet" =
  Stdlib.List.iter
    (fun b -> run_prog (Shim.find_modprog "guard_type_differs") [b])
    [0; 5; 255];
  [%expect {|
    [0] 8b
    [0] 8b
    [0] 8b
    |}]

(* Guarding on a header no module writes: it stays UninitVal, and CrVal.eqb is
   false on UninitVal, so the rule cannot fire even though the constant it is
   compared against is 0. *)
let%expect_test "match guard: unwritten header never matches" =
  run_prog (Shim.find_modprog "guard_unwritten") [0];
  [%expect {| [0] 8b |}]

(* --------------------------------------------------------------------- *)
(* Packet width: a parser that runs off the end rejects the network.     *)
(*                                                                       *)
(* field_extractor consumes 192 bits (72 + 8 + 16 + 32 + 32 + 16 + 16).  *)
(* The PktClass programs used to declare a 160-bit input, so every       *)
(* packet failed mid-parse and BOTH classifiers rejected everything --   *)
(* which is why modnet_equivalence_checker called them Equivalent while  *)
(* they were in fact both broken.  A vacuous pass is the failure mode to *)
(* watch for here.                                                       *)
(* --------------------------------------------------------------------- *)

let%expect_test "packet width: 192 bits is exactly enough for field_extractor" =
  run_prog PktClass.ex_lin_prog (pkt 1);
  [%expect {| [42] 8b |}]

(* ------------------------------------------------------------------ *)
(* A reject is a STATE, not an absence.                               *)
(*                                                                    *)
(* [pr_accept] made rejection a value at the parser level; these pin  *)
(* the same thing at the network level.  The distinction only shows   *)
(* up through [print_net_outcome] -- [run_prog] renders both [None]   *)
(* and an invalid state as the word "reject".                         *)
(* ------------------------------------------------------------------ *)

let run_outcome name bytes =
  let p = Shim.find_modprog name in
  let gcs0 = CrVarLike.init_general_concrete_state p in
  Shim.print_net_outcome
    (CrConcreteSemanticsModule.eval_general_program_concrete p
       (Shim.set_net_packet bytes gcs0))

(* 0xFF takes the parser's Reject transition.  The network still runs to
   completion and hands back a state; the verdict is in gps_valid.  This
   returned [None] before -- the deparser downstream never ran, so there was no
   final state to inspect and no way to tell this from a broken program. *)
let%expect_test "reject is a state: parse_reject_deparse on 0xFF" =
  run_outcome "parse_reject_deparse" [0xFF];
  [%expect {| rejected, bits_read=8, residual=0b |}]

(* The same pipeline on a packet it accepts, for contrast. *)
let%expect_test "reject is a state: parse_reject_deparse on 0x07 accepts" =
  run_outcome "parse_reject_deparse" [0x07];
  [%expect {| accepted, bits_read=8, residual=0b |}]

(* Because the run no longer stops at the rejection, the deparser downstream
   still executes and still appends to the write tape -- it emits h1, which the
   parser had already extracted before taking the Reject transition.  That is
   what the symbolic side has always done (no validity guard there either), so
   this is the two evaluators agreeing rather than a new quirk.  The tape is not
   junk to be read as output: gps_valid is false, and check_sym_pkt_out's
   both-rejected disjunct is what governs a pair like this. *)
let%expect_test "reject is a state: the deparser downstream still runs" =
  let p = Shim.find_modprog "parse_reject_deparse" in
  let gcs0 = CrVarLike.init_general_concrete_state p in
  (match CrConcreteSemanticsModule.eval_general_program_concrete p
           (Shim.set_net_packet [0xFF] gcs0) with
   | None -> print_endline "incomplete (None)"
   | Some s -> Shim.print_net_output s);
  [%expect {| [255] 8b |}]

(* Running off the end of the packet is the same kind of verdict as an explicit
   Reject transition, and reports the same way. *)
let%expect_test "reject is a state: running off the end of the packet" =
  run_outcome "consume2_emit1" [0xAA];
  [%expect {| rejected, bits_read=8, residual=0b |}]

(* ------------------------------------------------------------------ *)
(* The module-local parser state records the run.                     *)
(* ------------------------------------------------------------------ *)

(* two_parsers: parser 1 consumes one byte of three and leaves two; parser 2
   consumes one of those and leaves one.  Both used to report residual=24b at
   cursor 0 -- the packet each was handed, at the cursor each started from --
   however much they had actually consumed. *)
let%expect_test "module-local state: each parser holds its own residual" =
  Shim.print_parser_residuals (run "two_parsers" [0x07; 0x2A; 0xCC]);
  [%expect {|
    Module 1: residual=16b, cursor=0
    Module 2: residual=8b, cursor=0
    |}]

(* A rejecting parser leaves no residual, matching the symbolic side, whose
   four non-accepting exits all produce an empty one. *)
let%expect_test "module-local state: a rejecting parser leaves nothing" =
  let p = Shim.find_modprog "parse_reject_deparse" in
  let gcs0 = CrVarLike.init_general_concrete_state p in
  (match CrConcreteSemanticsModule.eval_general_program_concrete p
           (Shim.set_net_packet [0xFF] gcs0) with
   | None -> print_endline "incomplete (None)"
   | Some s -> Shim.print_parser_residuals s);
  [%expect {| Module 1: residual=0b, cursor=0 |}]

let%expect_test "packet width: one byte short rejects mid-parse" =
  (* 23 bytes = 184 bits: the final dst_port extract runs past the end. *)
  let short = Stdlib.List.filteri (fun i _ -> i < 23) (pkt 1) in
  run_prog PktClass.ex_lin_prog short;
  [%expect {| reject |}]

let%expect_test "packet width: bits_read confirms the full 192 are consumed" =
  let gcs0 = CrVarLike.init_general_concrete_state PktClass.ex_lin_prog in
  (match CrConcreteSemanticsModule.eval_general_program_concrete
           PktClass.ex_lin_prog (Shim.set_net_packet (pkt 1) gcs0) with
   | None -> print_endline "reject"
   | Some s -> Shim.print_net_bits_read s);
  [%expect {| bits_read=192 |}]

(* The sharpest form of the linear_db bug.  DistinctDB's filter matches
   src_ip = 0x0A0B0C0D and assigns label 42.  The low byte of that src_ip is
   0x0D = 13, so the two candidate behaviours give different bytes:

     42  -- emitted the classified label (correct)
     13  -- emitted the parser's src_ip, i.e. h_out was never copied into
            (HeaderCtr 1), which is what linear_db did before the fix

   With SimpleDB this bug emits 0 and reads as "no match"; here it cannot be
   confused with anything else. *)
let%expect_test "pktclass: emits the label, not the parsed src_ip" =
  let p = Stdlib.List.init 24 (fun i ->
    if i = 9 then 1
    else if i = 12 then 0x0A else if i = 13 then 0x0B
    else if i = 14 then 0x0C else if i = 15 then 0x0D
    else 0) in
  print_string "lin: "; run_prog PktClass.ex_lin_distinct p;
  print_string "tss: "; run_prog PktClass.ex_tss_distinct p;
  [%expect {|
    lin: [42] 8b
    tss: [42] 8b
    |}]

(* ------------------------------------------------------------------ *)
(* Write tape: several deparsers concatenate, they do not clobber.    *)
(* ------------------------------------------------------------------ *)

(* mod_prog_two_deparsers parses two bytes into h1, h2, then chains a deparser
   emitting h1 into one emitting h2.  Each appends to the shared write tape, so
   the network's output packet is both bytes in run order.  Were the tape
   replaced rather than appended, only the last deparser's byte would survive. *)
let%expect_test "two_deparsers: write tape is the concatenation, in run order" =
  run_prog (Shim.find_modprog "two_deparsers") [0xAA; 0xBB];
  [%expect {| [170, 187] 16b |}]

(* --------------------------------------------------------------------- *)
(* Memory.                                                               *)
(*                                                                       *)
(* These check the concrete semantics directly rather than trusting the  *)
(* equivalence checker, which by design accepts any pair of programs     *)
(* that both reject or both emit the same nothing -- and a memory        *)
(* program that only ever reads uninitialized cells emits a zero byte.   *)
(* Region 1 is declared with 4 cells, so offsets 0..3 are in bounds and  *)
(* 4 is not.  The packet is one byte, parsed into h1; h2 is written only *)
(* by the transformer.                                                   *)
(* --------------------------------------------------------------------- *)

let run_mem name bytes seed =
  run_net name (fun gcs -> seed (Shim.set_net_packet bytes gcs))

let report gcs =
  Shim.print_net_output gcs;
  Shim.print_net_mem_region 1 gcs;
  Shim.print_net_mem_extent 1 gcs

(* Store the parsed byte at cell 2 and read it straight back: it comes out of
   the deparser unchanged, cell 2 holds it, and the extent records that three
   bytes of the region were needed -- one PAST the byte touched, not its
   offset. *)
let%expect_test "mem_store_load: round-trips a byte through cell 2" =
  report (run "mem_store_load" [0x2A]);
  [%expect {|
    [42] 8b
    mem1=[0, 0, 42, 0]
    extent1=3
    |}]

(* A declared region starts as [len] ZERO BYTES ([CrVal.mk_region_zero]), so
   an unwritten cell reads as an honest [0:u8] and the load succeeds.  The
   output is one zero byte.

   It used to read [UninitVal], fail the load's [cast u8 _] and land as
   ErrorVal, which the TOTAL deparser then emitted as zeroed bits -- the same
   output for a quite different reason, and an instance of the "two broken
   programs agree" trap.  That reading went away with the region model: a
   region's contents are an input, and a real input is bytes (see
   [CrVal.to_byte]).  The trap itself has not: [mem_oob_store_load] below still
   reads ErrorVal, out of bounds this time, and still emits zeros for it. *)
let%expect_test "mem_load0: an unwritten cell reads as a zero byte" =
  report (run "mem_load0" [0x2A]);
  [%expect {|
    [0] 8b
    mem1=[0, 0, 0, 0]
    extent1=1
    |}]

(* Same zero-byte output as [mem_load0] -- both programs are, observably,
   equally broken -- but this one reached one cell further in.  The extent is the only
   thing that separates them, which is what it is for. *)
let%expect_test "mem_load1_load0: a dead load still widens the extent" =
  report (run "mem_load1_load0" [0x2A]);
  [%expect {|
    [0] 8b
    mem1=[0, 0, 0, 0]
    extent1=2
    |}]

(* The individual ACCESS is still total -- the store is dropped, the load
   yields ErrorVal, and the run completes rather than stopping -- but the RUN
   is not valid: [eval_general_program_concrete] conjoins
   [mem_extents_in_bounds_concrete] into [gps_valid] at the end, and this run
   required five bytes of a four-byte region.  The extent is what carries that
   to the end of the network; the fault is reported once, there. *)
let%expect_test "mem_oob_store_load: the access is dropped, the run rejects" =
  let gcs = run "mem_oob_store_load" [0x2A] in
  report gcs;
  Printf.printf "valid=%b\n" (gcs.CrGeneralProgramState.gps_valid = Datatypes.Coq_true);
  [%expect {|
    [0] 8b
    mem1=[0, 0, 0, 0]
    extent1=5
    valid=false
    |}]

(* A store is not atomic, and this is where that shows: the u16 at offset 3
   puts its low byte in cell 3 and drops the high one, so the region really is
   half-written -- and the run is rejected all the same. *)
let%expect_test "mem_oob_mb_store_load: extent1 = 5, and the run rejects" =
  let gcs = run "mem_oob_mb_store_load" [0x2A] in
  report gcs;
  Printf.printf "valid=%b\n" (gcs.CrGeneralProgramState.gps_valid = Datatypes.Coq_true);
  [%expect {|
    [0] 8b
    mem1=[0, 0, 0, 42]
    extent1=5
    valid=false
    |}]

(* A pre-seeded cell reads back out, and reading it does not disturb the rest
   of the region.  This is also the only test that exercises a load whose
   result is a genuine value rather than an ErrorVal from an unwritten cell. *)
let%expect_test "mem_load0: a seeded cell reads back" =
  report (run_mem "mem_load0" [0x2A] (Shim.set_net_mem_cell 1 0 CrVal.W8 0x7F));
  [%expect {|
    [127] 8b
    mem1=[127, 0, 0, 0]
    extent1=1
    |}]

(* In bounds, a load before a store sees the old contents; the store still
   happens.  Compare [mem_store_load] above, where the order is reversed and
   the byte does come out. *)
let%expect_test "mem_ib_load_store: load-then-store sees the old cell" =
  report (run_mem "mem_ib_load_store" [0x2A] (Shim.set_net_mem_cell 1 2 CrVal.W8 0x11));
  [%expect {|
    [17] 8b
    mem1=[0, 0, 42, 0]
    extent1=3
    |}]

(* Names cannot drift the way indices could -- a renamed or removed program
   makes find_modprog raise at initialisation.  This catches the quieter
   direction: a program added to the Rocq registry but never bound in ModProgs,
   which nothing else would notice.  Listing the names rather than counting them
   also doubles as documentation of what the registry holds, and exercises the
   Coq-string decode on names built on the Rocq side. *)
let%expect_test "ModProgs: registry contents" =
  let names =
    Stdlib.List.map Shim.coq_str_to_str
      (Shim.listify_coq_list TestModulePrograms.mod_test_program_names) in
  let count = Stdlib.List.length names in
  Stdlib.List.iter print_endline names;
  Printf.printf "(%d programs)\n" count;
  [%expect {|
    single_add3
    add1_then_mul2
    conditional_pipeline
    cmplt_matchheader
    two_parsers
    parse_deparse
    parse_deparse_swapped
    parse_reject_deparse
    parse_accept_deparse
    peek0_reject
    extract_reject
    peek8_reject
    consume1_emit1
    consume2_emit1
    varlen_emit1
    guard_type_agrees
    guard_type_differs
    guard_unwritten
    two_deparsers
    mem_store_load
    mem_store_load_alias
    mem_store_load_differs
    mem_load1_load0
    mem_load1_load0_alt
    mem_load0
    mem_cmp_gt
    mem_cmp_lt
    hdr_init_sel
    hdr_init_nosel
    mem_ib_load_store
    mem_oob_load_store
    mem_oob_store_load
    mem_oob_mb_store_load
    mem_guard_tautology
    mem_two_u8_stores
    mem_u8_into_u16_load
    mem_one_u16_store
    mem_store_poisoned
    mem_u16_readback
    mem_u16_load
    mem_two_u8_loads
    (41 programs)
    |}]

(* A u16 store lands in two byte cells, little-endian: 0x1234 -> [0x34, 0x12].
   This is what makes it the same thing as the two u8 stores it coalesces
   from, and it is the whole point of memory being an array of bytes. *)
let%expect_test "mem_one_u16_store: 0x1234 decomposes little-endian" =
  report (run "mem_one_u16_store" [0x2A]);
  [%expect {|
    [52] 8b
    mem1=[52, 18, 0, 0]
    extent1=2
    |}]

(* And reassembles on the way back out: the u16 load sees 0x1234, whose low
   byte is what the deparser emits. *)
let%expect_test "mem_u16_readback: two bytes reassemble into a u16" =
  report (run "mem_u16_readback" [0x2A]);
  [%expect {|
    [52] 8b
    mem1=[52, 18, 0, 0]
    extent1=2
    |}]

(* -------------------------------------------------------------------- *)
(* The transpiled eBPF programs (../test/bpf_O{0,2}.ir).                *)
(*                                                                      *)
(* TestEquality proves these two equivalent, and on its own that proves *)
(* very little: a deparser emits a header holding no integer as zeroed  *)
(* bits, so two programs that both fail to compute anything also agree. *)
(* These runs are what say the translation actually does the XDP        *)
(* program's work.                                                      *)
(*                                                                      *)
(* Region 1 is the ctx (xdp_md): u32 `data` at offset 0 and `data_end`  *)
(* at 4.  Region 2 is the packet.  bpf_ref.c bounds-checks              *)
(* data + sizeof(ethhdr) + 1 against data_end, then reads the 2-byte    *)
(* ethertype at packet offsets 12/13 and, if it is IP, writes 0xff at   *)
(* offset 14 and returns XDP_PASS (2).                                  *)
(* -------------------------------------------------------------------- *)

let bpf_prog f = Shim.load_general_program f

(* data = 0, data_end = 24: 24 bytes of packet, enough for the check to pass. *)
let seed_ctx gcs =
  gcs
  |> Shim.set_net_mem_cell 1 0 CrVal.W32 0
  |> Shim.set_net_mem_cell 1 4 CrVal.W32 24

(* The ethertype the program loads is byte 13 shifted up over byte 12. *)
let seed_ethertype hi lo gcs =
  gcs
  |> Shim.set_net_mem_cell 2 12 CrVal.W8 lo
  |> Shim.set_net_mem_cell 2 13 CrVal.W8 hi

let run_bpf name f seed = run_named_prog name (bpf_prog f) seed

let report_bpf gcs =
  Shim.print_net_output gcs;
  Shim.print_net_mem_region 2 gcs;
  Shim.print_net_mem_extent 2 gcs

(* An IP packet: 0x0800 as the program reads it, so the write happens and the
   verdict is XDP_PASS.  The output byte is r0's low 8 bits. *)
let%expect_test "bpf O2: an IP packet is stamped and passed" =
  report_bpf (run_bpf "bpf_O2" "../test/bpf_O2.ir"
                (fun gcs -> gcs |> seed_ctx |> seed_ethertype 0x08 0x00));
  [%expect {|
    [0, 0, 0, 2] 32b
    mem2=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    extent2=15
    |}]

(* -O0 is a different instruction sequence -- it spills every value to the
   stack -- and has to produce the same thing.  This is the concrete half of
   the equivalence result. *)
let%expect_test "bpf O0: same packet, same stamp and verdict" =
  report_bpf (run_bpf "bpf_O0" "../test/bpf_O0.ir"
                (fun gcs -> gcs |> seed_ctx |> seed_ethertype 0x08 0x00));
  [%expect {|
    [0, 0, 0, 2] 32b
    mem2=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 8, 255, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    extent2=15
    |}]

(* A non-IP ethertype takes the other arm: nothing is written and the verdict
   is XDP_DROP (1).  The extent still reaches 13, because the ethertype was
   read on this path too. *)
let%expect_test "bpf: a non-IP packet is dropped, untouched" =
  report_bpf (run_bpf "bpf_O2" "../test/bpf_O2.ir"
                (fun gcs -> gcs |> seed_ctx |> seed_ethertype 0x86 0xDD));
  [%expect {|
    [0, 0, 0, 1] 32b
    mem2=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 221, 134, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    extent2=14
    |}]

(* Too short for an ethernet header plus a byte: the bounds check fails and the
   program returns XDP_ABORTED (0) without reading the ethertype at all. *)
let%expect_test "bpf: a short packet is aborted before any packet read" =
  report_bpf (run_bpf "bpf_O2" "../test/bpf_O2.ir"
                (fun gcs ->
                   gcs
                   |> Shim.set_net_mem_cell 1 0 CrVal.W32 0
                   |> Shim.set_net_mem_cell 1 4 CrVal.W32 8));
  [%expect {|
    [0, 0, 0, 0] 32b
    mem2=[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
    extent2=0
    |}]

(* Coq's [Ascii b0 .. b7] takes b0 as the least significant bit.  [char_to_ascii]
   once passed the bits the other way round, so an OCaml-built Coq string was
   bit-reversed and never equal to the Coq-built string for the same text.  That
   silently broke two things: ModProgs' lookup by name, and the SAT valuation
   returned by Z3Solver, whose keys are built this way and are compared against
   Coq-built variable names by coq_TraverseMap -- every lookup missed, so the
   valuation answered UninitVal for every variable. *)
let%expect_test "Shim: Coq string conversion round-trips" =
  Stdlib.List.iter
    (fun s -> Printf.printf "%b " (Shim.coq_str_to_str (Shim.str_to_coq_str s) = s))
    [""; "a"; "parse_deparse"; "hdr_1"; "~!@ 0x7F"];
  print_newline ();
  [%expect {| true true true true true |}]

(* The name key must agree with the one Rocq computed when building the
   registry, which is what makes lookup by name work at all. *)
let%expect_test "ModProgs: unknown names are a clean failure" =
  (try ignore (Shim.find_modprog "no_such_program"); print_endline "no failure"
   with Failure m -> print_endline m);
  [%expect {| find_modprog: no module test program named no_such_program |}]

(* A store whose offset is a *header* rather than a constant, aliasing a
   constant-offset store to the same cell.  Equivalence against
   [mem_store_load] is checked in [TestEquality]; this pins the concrete state
   the two are supposed to share. *)
let%expect_test "mem_store_load_alias: a computed offset hits the same cell" =
  report (run "mem_store_load_alias" [0x2A]);
  [%expect {|
    [42] 8b
    mem1=[0, 0, 42, 0]
    extent1=3
    |}]

(* A guard that cannot fail should leave exactly the state of no guard at all.
   [CrVal.eqb] is reflexive, so the rule fires; the second (empty) rule is the
   default. Same state as [mem_store_load] above. *)
let%expect_test "mem_guard_tautology: a guard that always holds is no guard" =
  report (run "mem_guard_tautology" [0x2A]);
  [%expect {|
    [42] 8b
    mem1=[0, 0, 42, 0]
    extent1=3
    |}]

(* The coalescing pair, run as a pair.  [TestEquality] checks the CHECKER calls
   these equivalent; this checks they actually agree cell for cell, which is
   the property the byte-addressed memory model exists to give.  A model where
   a u16 store occupied one address would show mem1=[4660, -, -, -] on the
   right and diverge here while the checker still said Equivalent. *)
let%expect_test "mem: a u16 store and the two u8 stores agree concretely" =
  report (run "mem_two_u8_stores" [0x2A]);
  report (run "mem_one_u16_store" [0x2A]);
  [%expect {|
    [52] 8b
    mem1=[52, 18, 0, 0]
    extent1=2
    [52] 8b
    mem1=[52, 18, 0, 0]
    extent1=2
    |}]

(* Storing a header that was never written.  Every cell the store covers holds
   [Init ErrorVal] -- printed [!], distinct from [-] for never-written -- and
   the load reads one back, so the deparser emits a zero byte.  This is the
   only program that puts a poisoned value in a region, and the concrete
   counterpart of the tag-0 cells a SAT model reports as "err". *)
let%expect_test "mem_store_poisoned: storing an unwritten header poisons cells" =
  report (run "mem_store_poisoned" [0x2A]);
  [%expect {|
    [0] 8b
    mem1=[!, !, 0, 0]
    extent1=2
    |}]

(* -------------------------------------------------------------------- *)
(* bpf_map_ref.ir: a bpf_map_lookup_elem program (~/proj/ect/ex/map_ref.c) *)
(*                                                                      *)
(* Region 10 is the map: 4 presence bytes, then four 8-byte values, so   *)
(* slot i's presence is at offset i and its value at 4 + 8*i.  The slot  *)
(* is key % 4, the key is ctx->ingress_ifindex (u32 at ctx offset 12).   *)
(*                                                                      *)
(* The checker verdicts in TestEquality say the two arms of a lookup are *)
(* distinguishable; these say what each arm actually does, on cells that *)
(* are well-formed bytes.  r0 is emitted as 32 bits, so the last output  *)
(* byte is the return value.                                            *)
(* -------------------------------------------------------------------- *)

let map_prog = "../test/bpf_map_ref.ir"

(* key -> ctx, then the slot's presence byte and (if present) its value. *)
let seed_map key present value gcs =
  let slot = key mod 4 in
  let gcs = Shim.set_net_mem_cell 1 12 CrVal.W32 key gcs in
  let gcs = Shim.set_net_mem_cell 10 slot CrVal.W8 present gcs in
  Shim.set_net_mem_cell 10 (4 + 8 * slot) CrVal.W64 value gcs

let run_map key present value =
  let gcs = run_named_prog "bpf_map_ref" (bpf_prog map_prog)
              (seed_map key present value) in
  Shim.print_net_output gcs;
  Shim.print_net_mem_extent 10 gcs

let%expect_test "bpf map: a miss returns 1 and never reads the value" =
  run_map 2 0 999;
  [%expect {|
    [0, 0, 0, 1] 32b
    extent10=3
    |}]

let%expect_test "bpf map: a hit over the threshold returns 2" =
  run_map 2 1 200;
  [%expect {|
    [0, 0, 0, 2] 32b
    extent10=28
    |}]

let%expect_test "bpf map: a hit under the threshold returns 0" =
  run_map 2 1 50;
  [%expect {|
    [0, 0, 0, 0] 32b
    extent10=28
    |}]

(* nslots is 4 where the map declares 64 entries, so keys 2 and 6 share a
   slot.  That conflation is the map model's one real abstraction; this test
   is what makes it visible rather than a claim in a comment. *)
let%expect_test "bpf map: key 6 lands in the same slot as key 2" =
  run_map 6 1 200;
  [%expect {|
    [0, 0, 0, 2] 32b
    extent10=28
    |}]

(* -------------------------------------------------------------------- *)
(* Suricata's vlan_filter: accept (-1) VLAN 2 and 4, drop (0) the rest.  *)
(* vlan_tci is a u32 at ctx offset 24 and the filter masks it with       *)
(* 0x0fff.  r0 is emitted as 32 bits, so -1 prints as four 255s.         *)
(* -------------------------------------------------------------------- *)

let run_vlan tci =
  Shim.print_net_output
    (run_named_prog "vlan_filter" (bpf_prog "../test/bpf_vlan_filter.ir")
       (Shim.set_net_mem_cell 1 24 CrVal.W32 tci))

let%expect_test "vlan_filter: VLAN 2 is accepted" =
  run_vlan 2; [%expect {| [255, 255, 255, 255] 32b |}]

let%expect_test "vlan_filter: VLAN 4 is accepted" =
  run_vlan 4; [%expect {| [255, 255, 255, 255] 32b |}]

let%expect_test "vlan_filter: VLAN 3 is dropped" =
  run_vlan 3; [%expect {| [0, 0, 0, 0] 32b |}]

(* The filter masks off the PCP/DEI bits, so 0x2002 is still VLAN 2. *)
let%expect_test "vlan_filter: the priority bits are masked off" =
  run_vlan 0x2002; [%expect {| [255, 255, 255, 255] 32b |}]



(* -------------------------------------------------------------------- *)
(* ex/pkt_load.c: the classic-BPF packet loads and BPF_END, one per arm  *)
(* of a switch on skb->mark so each is checked on its own.               *)
(*                                                                      *)
(* load_byte/half/word convert from NETWORK byte order, and BPF_END is a *)
(* plain byte swap; neither is a primitive the IR has, so both are built *)
(* from multiply/divide by powers of two.  These values are hand-        *)
(* computed from the seeded bytes -- an arithmetic byte swap is exactly  *)
(* the kind of thing that is wrong in a way no verdict test would show.  *)
(* -------------------------------------------------------------------- *)

let pkt_bytes = [0x00;0x11;0x22;0x33;0x44;0x55;0x66;0x77;
                 0x88;0x99;0xAA;0xBB;0xCC;0xDD;0xEE;0xFF]

let run_pkt_load mark =
  let seed gcs =
    let g = Stdlib.List.fold_left
              (fun g (i, v) -> Shim.set_net_mem_cell 2 i CrVal.W8 v g)
              gcs (Stdlib.List.mapi (fun i v -> (i, v)) pkt_bytes) in
    g |> Shim.set_net_mem_cell 1 8 CrVal.W32 mark        (* skb->mark    *)
      |> Shim.set_net_mem_cell 1 48 CrVal.W32 2          (* skb->cb[0]   *)
      |> Shim.set_net_mem_cell 1 68 CrVal.W32 0x01020304 (* skb->hash    *)
  in
  Shim.print_net_output
    (run_named_prog "pkt_load" (bpf_prog "../test/bpf_pkt_load.ir") seed)

(* packet[4..7] = 44 55 66 77, big-endian *)
let%expect_test "pkt_load: LD_ABS at 32 bits" =
  run_pkt_load 0; [%expect {| [68, 85, 102, 119] 32b |}]

(* packet[2..3] = 22 33, and the upper half of r0 stays zero *)
let%expect_test "pkt_load: LD_ABS at 16 bits" =
  run_pkt_load 1; [%expect {| [0, 0, 34, 51] 32b |}]

(* packet[1] = 0x11; a single byte needs no swap *)
let%expect_test "pkt_load: LD_ABS at 8 bits" =
  run_pkt_load 2; [%expect {| [0, 0, 0, 17] 32b |}]

(* cb[0] = 2, so the offset is 2 + 8 = 10: packet[10..13] = AA BB CC DD *)
let%expect_test "pkt_load: LD_IND at a runtime offset" =
  run_pkt_load 3; [%expect {| [170, 187, 204, 221] 32b |}]

(* BPF_END on skb->hash = 0x01020304 *)
let%expect_test "pkt_load: BPF_END swaps 32 bits" =
  run_pkt_load 9; [%expect {| [4, 3, 2, 1] 32b |}]

(* -------------------------------------------------------------------- *)
(* ex/sur_filter.c: Suricata's filter.c.  IPv4 over ethernet, so         *)
(* h_proto (packet 12..13) is 0x0800 and nhoff is 14; saddr is then at   *)
(* packet 26..29 and daddr at 30..33.  Map region 10 has 4 presence      *)
(* bytes then four 4-byte values, and the slot is address % 4.           *)
(* -------------------------------------------------------------------- *)

let run_sur_filter ~saddr ~daddr ~drop_saddr ~drop_daddr =
  let put_be32 off v g =
    Stdlib.List.fold_left (fun g (i, sh) ->
        Shim.set_net_mem_cell 2 (off + i) CrVal.W8 ((v lsr sh) land 0xff) g)
      g [(0,24);(1,16);(2,8);(3,0)] in
  let seed gcs =
    gcs
    |> Shim.set_net_mem_cell 2 12 CrVal.W8 0x08     (* h_proto = ETH_P_IP *)
    |> Shim.set_net_mem_cell 2 13 CrVal.W8 0x00
    |> put_be32 26 saddr
    |> put_be32 30 daddr
    |> Shim.set_net_mem_cell 10 (saddr mod 4) CrVal.W8 (if drop_saddr then 1 else 0)
    |> Shim.set_net_mem_cell 10 (daddr mod 4) CrVal.W8 (if drop_daddr then 1 else 0)
  in
  Shim.print_net_output
    (run_named_prog "sur_filter" (bpf_prog "../test/bpf_sur_filter.ir") seed)

(* Neither address is in the drop map: the filter passes the packet (-1). *)
let%expect_test "sur_filter: an address in neither drop list passes" =
  run_sur_filter ~saddr:0 ~daddr:1 ~drop_saddr:false ~drop_daddr:false;
  [%expect {| [255, 255, 255, 255] 32b |}]

(* The source address is in the drop map: dropped (0), on the first lookup. *)
let%expect_test "sur_filter: a dropped source address returns 0" =
  run_sur_filter ~saddr:0 ~daddr:1 ~drop_saddr:true ~drop_daddr:false;
  [%expect {| [0, 0, 0, 0] 32b |}]

(* Only the DESTINATION is in the drop map, so this is decided by the second
   lookup -- the one that was unreachable while the packet region was 32
   bytes and the daddr read at offset 30..33 overran it. *)
let%expect_test "sur_filter: a dropped destination address returns 0" =
  run_sur_filter ~saddr:0 ~daddr:1 ~drop_saddr:false ~drop_daddr:true;
  [%expect {| [0, 0, 0, 0] 32b |}]
