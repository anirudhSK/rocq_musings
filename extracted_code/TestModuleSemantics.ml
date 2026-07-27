(* Every module network starts with a parser and ends in a deparser, so the only
   way in is the network's input packet: [seed] injects it into the initial
   general state's read tape, and the start parser extracts the headers from it.
   Programs are addressed by name via ModProgs, which looks them up in the Rocq
   registry. *)
let run_net name seed =
  let p = Shim.find_modprog name in
  Shim.print_malformed_gprog p name;
  let gcs0 = CrVarLike.init_general_concrete_state p in
  match CrConcreteSemanticsModule.eval_general_program_concrete p (seed gcs0) with
  | None -> failwith ("eval_general_program_concrete returned None for " ^ name)
  | Some s -> s

let run name bytes = run_net name (Shim.set_net_packet bytes)

(* ------------------------------------------------------------------ *)
(* mod_prog_single_add3 (pid 0): parser byte0 -> h1; h1 := h1 + 3      *)
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
(* mod_prog_add1_then_mul2 (pid 1): h1 -> (h1+1)*2                     *)
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
(* mod_prog_conditional_pipeline (pid 2)                               *)
(*   Module 2: h1=7 -> h1:=1, else no-op.  Module 3: h1 := h1+10.      *)
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
(* mod_prog_cmplt_matchheader (pid 3)                                  *)
(*   Module 2: h1<h2 -> h1:=h1+h2.  Module 3: h1 := h1+1.              *)
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
      h1=7
    Module 2:
      h1=7, h2=42
    Module 3:
      h1=7, h2=42
  |}]

(* ------------------------------------------------------------------ *)
(* sh_bits_read: how much of the input packet the network consumed.     *)
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
  [%expect {| 18, 52 |}]

(* Same parser, deparser emits the two headers in the other order. *)
let%expect_test "parse_deparse_swapped: packet [0x12;0x34] -> bytes swapped" =
  Shim.print_net_output (run "parse_deparse_swapped" [0x12; 0x34]);
  [%expect {| 52, 18 |}]

(* ------------------------------------------------------------------ *)
(* PktClass: linear-scan vs tuple-space-search classifiers.             *)
(*                                                                      *)
(* These are concrete on purpose.  Test 13 in TestEquality runs the same *)
(* two programs through modnet_equivalence_checker, and it reported      *)
(* Equivalent throughout a period when tss_db rejected every packet and   *)
(* linear_db emitted a label -- a symbolic checker comparing output       *)
(* packets cannot pin down WHICH label a classifier produces.  Checking   *)
(* concrete labels here is what makes these two constructions actually    *)
(* agree rather than merely fail to be distinguished.                     *)
(* ------------------------------------------------------------------ *)

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
    lin: 42
    tss: 42
  |}]

let%expect_test "pktclass: protocol 2 classifies to label 67 in both" =
  both (pkt 2);
  [%expect {|
    lin: 67
    tss: 67
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
    lin: 0
    tss: 0
  |}]

(* Protocol matches a filter but another field does not. *)
let%expect_test "pktclass: nonzero src_ip emits 0 in both" =
  both (pkt ~src_ip0:7 1);
  [%expect {|
    lin: 0
    tss: 0
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
    lin: 42
    tss: 42
  |}]

let%expect_test "pktclass precedence: no match emits 0 in both" =
  both_overlap (pkt 3);
  [%expect {|
    lin: 0
    tss: 0
  |}]

(* ------------------------------------------------------------------ *)
(* Why a match-action rule silently never fires.                        *)
(*                                                                      *)
(* These are the two root causes behind the PktClass divergence, reduced *)
(* to the smallest networks that show them.  Both are silent: the rule    *)
(* simply never fires, the guarded header is never written, and the       *)
(* deparser emits zeros -- there is no error anywhere to notice.          *)
(* ------------------------------------------------------------------ *)

(* Baseline: guard type matches the extract type, so the rule fires. *)
let%expect_test "match guard: u8 extract vs u8 constant fires" =
  run_prog (Shim.find_modprog "guard_type_agrees") [5];
  [%expect {| 99 |}]

(* Same packet, same constant, only the extract type differs.  CrVal.eqb
   compares the CrIntType before the value, so this never fires -- for any
   packet, not just this one. *)
let%expect_test "match guard: u64 extract vs u8 constant never fires" =
  run_prog (Shim.find_modprog "guard_type_differs") [5];
  [%expect {| 0 |}]

(* And it really is type, not value: the packet whose byte IS 5 still fails. *)
let%expect_test "match guard: u64/u8 mismatch fails on every packet" =
  Stdlib.List.iter
    (fun b -> run_prog (Shim.find_modprog "guard_type_differs") [b])
    [0; 5; 255];
  [%expect {|
    0
    0
    0
  |}]

(* Guarding on a header no module writes: it stays UninitVal, and CrVal.eqb is
   false on UninitVal, so the rule cannot fire even though the constant it is
   compared against is 0. *)
let%expect_test "match guard: unwritten header never matches" =
  run_prog (Shim.find_modprog "guard_unwritten") [0];
  [%expect {| 0 |}]

(* ------------------------------------------------------------------ *)
(* Packet width: a parser that runs off the end rejects the network.    *)
(*                                                                      *)
(* field_extractor consumes 192 bits (72 + 8 + 16 + 32 + 32 + 16 + 16). *)
(* The PktClass programs used to declare a 160-bit input, so every       *)
(* packet failed mid-parse and BOTH classifiers rejected everything --   *)
(* which is why modnet_equivalence_checker called them Equivalent while  *)
(* they were in fact both broken.  A vacuous pass is the failure mode to *)
(* watch for here.                                                       *)
(* ------------------------------------------------------------------ *)

let%expect_test "packet width: 192 bits is exactly enough for field_extractor" =
  run_prog PktClass.ex_lin_prog (pkt 1);
  [%expect {| 42 |}]

let%expect_test "packet width: one byte short rejects mid-parse" =
  (* 23 bytes = 184 bits: the final dst_port extract runs past the end. *)
  let short = Stdlib.List.filteri (fun i _ -> i < 23) (pkt 1) in
  run_prog PktClass.ex_lin_prog short;
  [%expect {| reject (None) |}]

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
    lin: 42
    tss: 42
  |}]

(* ------------------------------------------------------------------ *)
(* Write tape: several deparsers concatenate, they do not clobber.      *)
(* ------------------------------------------------------------------ *)

(* mod_prog_two_deparsers parses two bytes into h1, h2, then chains a deparser
   emitting h1 into one emitting h2.  Each appends to the shared write tape, so
   the network's output packet is both bytes in run order.  Were the tape
   replaced rather than appended, only the last deparser's byte would survive. *)
let%expect_test "two_deparsers: write tape is the concatenation, in run order" =
  run_prog (Shim.find_modprog "two_deparsers") [0xAA; 0xBB];
  [%expect {| 170, 187 |}]

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
    consume1_emit1
    consume2_emit1
    varlen_emit1
    guard_type_agrees
    guard_type_differs
    guard_unwritten
    two_deparsers
    (16 programs)
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
