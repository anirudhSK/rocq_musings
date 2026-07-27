open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  let p = str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp in
  Shim.print_malformed_prog p 0;
  p

(* let get_general_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> CrTypeIF.CrModule.coq_GeneralCaracaraProgram_of_sexp *)

let get_mem_program f = MemSolver.load_program f

let print_equiv = function
  | SmtQuery.Equivalent -> print_endline "Equivalent"
  | SmtQuery.NotEquivalent _ -> print_endline "NotEquivalent"
  | SmtQuery.NotEquivalentUnknown -> print_endline "NotEquivalentUnknown"
  | SmtQuery.NotEquivalentVariablesDiffer -> print_endline "NotEquivalentVariablesDiffer"

let print_z3 = function
  | CrMem.Z3Unsat -> print_endline "Z3Unsat"
  | CrMem.Z3Unknown -> print_endline "Z3Unknown"
  | CrMem.Z3Sat (_, _, ValueMismatch) -> print_endline "Z3Sat(ValueMismatch)"
  | CrMem.Z3Sat (_, _, BoundsMismatch) -> print_endline "Z3Sat(BoundsMismatch)"
  | CrMem.Z3Sat (_, _, FullMismatch) -> print_endline "Z3Sat(FullMismatch)"

(* Test 1: A program should be equal to itself. *)
let%expect_test "refl_0: identical programs are equivalent" =
  let p = get_program "../test/prog1.out" in
  print_equiv (SmtQuery.equivalence_checker_cr_dsl p p);
  [%expect {| Equivalent |}]

(* Test 2: Different constant assignments to header variable.
 * p1: x=5, p2: x=1 *)
let%expect_test "hdr_diff: different constants are NotEquivalent" =
  let p1 = get_program "../test/prog1.out" in
  let p2 = get_program "../test/prog2.out" in
  print_equiv (SmtQuery.equivalence_checker_cr_dsl p1 p2);
  (* hdr_1 is never read arithmetically here (both programs overwrite it with a
     constant), so its width is unconstrained by the query and defaults to u64. *)
  [%expect {|
    ┌ SAT Valuation
    | var( hdr_1 ) : u64 := 0
    └
    NotEquivalent
    |}]

(* Test 3: -2 and +254 agree under 8-bit 2s complement.
 * p1: x-2, p2: x+254 *)
let%expect_test "sub_1comp: -2 and +254 are equivalent" =
  let p1 = get_program "../test/subtract1.out" in
  let p2 = get_program "../test/subtract2.out" in
  print_equiv (SmtQuery.equivalence_checker_cr_dsl p1 p2);
  [%expect {| Equivalent |}]

(* Test 4: Addition is commutative.
 * p1: x + 2 - 1, p2: x - 1 + 2 *)
let%expect_test "complex_add_sub: reordered add/sub are equivalent" =
  let p1 = get_program "../test/complex1a.out" in
  let p2 = get_program "../test/complex1b.out" in
  print_equiv (SmtQuery.equivalence_checker_cr_dsl p1 p2);
  [%expect {| Equivalent |}]

(* Test 5: Trivially non-equivalent.
 * p1: x - 1 + 2, p2: x - 1 *)
let%expect_test "complex_add_sub: dropping an op breaks equivalence" =
  let p1 = get_program "../test/complex1b.out" in
  let p2 = get_program "../test/subtract1.out" in
  print_equiv (SmtQuery.equivalence_checker_cr_dsl p1 p2);
  (* hdr_1 is read at u8 (x - 1), so the threaded width is recovered as u8. *)
  [%expect {|
    ┌ SAT Valuation
    | var( hdr_1 ) : u8 := 0
    └
    NotEquivalent
    |}]

(* Test 6: Address offsets should alias.
 * p1: *(x+4), p2: *(x+2+2) *)
let%expect_test "basic address alias" =
  let p1 = get_mem_program "../test/mem1a.out" in
  let p2 = get_mem_program "../test/mem1b.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    adding query to solver...
    running query...
    Z3Unsat
    |}]

(* Test 7: Writing a variable value vs writing a constant value differ.
 * p1: *(x+4) = y, p2: *(x+4) = 1 *)
let%expect_test "basic memory overwrite: value differs" =
  let p1 = get_mem_program "../test/mem1a.out" in
  let p2 = get_mem_program "../test/mem1c.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    adding query to solver...
    running query...
    ┌ SAT Valuation
    | var( 10 ) : u8 := 254
    | var( 11 ) : u8 := 0
    | arr( 1 ) := [0] (len=1)
    | Outputs equal: false
    | Bounds equal: true
    └
    Z3Sat(ValueMismatch)
    |}]

(* Test 8: Programs with different segfault behavior.
 * p1: ret *(x+0), p2: *(x+1); ret *(x+0) *)
let%expect_test "divergent load extents: bounds differ" =
  let p1 = get_mem_program "../test/mem2a.out" in
  let p2 = get_mem_program "../test/mem2b.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    adding query to solver...
    running query...
    ┌ SAT Valuation
    | arr( 1 ) := [0] (len=1)
    | Outputs equal: true
    | Bounds equal: false
    └
    Z3Sat(BoundsMismatch)
    |}]

(* Test 9: Access extents and output variables match.
 * p1: *(x+1); ret *(x+0), p2: *(x+1)=0; ret *(x+0) *)
let%expect_test "mem nop are equiv" =
  let p1 = get_mem_program "../test/mem2b.out" in
  let p2 = get_mem_program "../test/mem2c.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    adding query to solver...
    running query...
    Z3Unsat
    |}]

(* Test 10: If statement collapses.
 * p1: if (0 == 0) then A else B, p2: A *)
let%expect_test "degenerate branch collapses" =
  let p1 = get_mem_program "../test/mem3a.out" in
  let p2 = get_mem_program "../test/mem3b.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    Met nil expression
    adding query to solver...
    running query...
    Z3Unsat
    |}]

(* Test 11: Array values may differ.
 * p1: *(x+1); ret *(x+0), p2: *(x+0); ret *(x+1) *)
let%expect_test "sat aval: array values differ" =
  let p1 = get_mem_program "../test/mem4a.out" in
  let p2 = get_mem_program "../test/mem4b.out" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    adding query to solver...
    running query...
    ┌ SAT Valuation
    | arr( 1 ) := [255, 0] (len=2)
    | Outputs equal: false
    | Bounds equal: true
    └
    Z3Sat(ValueMismatch)
    |}]

(* Test 12: End-to-end -O0 vs -O2 compilation of a basic bpf program. *)
let%expect_test "e2e bpf test: O0 ≡ O2" =
  let p1 = get_mem_program "../test/O0.ir" in
  let p2 = get_mem_program "../test/O2.ir" in
  print_z3 (MemSolver.mem_solve p1 p2);
  [%expect {|
    casting query to z3 expression...
    Met nil expression
    adding query to solver...
    running query...
    Z3Unsat
    |}]

(* Test 13: linear scan vs tss for simple filter database.  Both are full
   parser -> table chain -> deparser networks over a 192-bit input packet (what
   field_extractor consumes), so they go through the bitstream checker: the
   observable is the label byte the deparser emits.

   NOTE: this test is weaker than it looks -- it reported Equivalent even while
   tss_db concretely produced nothing and linear_db emitted a label.  Agreeing
   on output packets does not pin down which label a classifier assigns.  The
   concrete labels are checked in TestModuleSemantics ("pktclass..."); keep
   both tests. *)
let%expect_test "tss basic" =
  (* let p1 = get_general_program "../test/lin_pkt.out" in
  let p2 = get_general_program "../test/tss_pkt.out" in *)
  let p1 = PktClass.ex_lin_prog in
  let p2 = PktClass.ex_tss_prog in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| Equivalent |}]

(* Test 14: bitstream-I/O equivalence.  A parse->deparse pipeline is equivalent
   to itself over any 16-bit input packet: the deparser re-emits exactly the
   bits the parser consumed.  Exercises the new bitstream [modnet_equivalence_checker]
   (shared symbolic input packet -> compare deparser output packets). *)
let%expect_test "bitstream self-equivalence: parse->deparse" =
  let p = Shim.find_modprog "parse_deparse" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p p);
  [%expect {| Equivalent |}]

(* Test 15: bitstream NON-equivalence.  The same parser feeding a deparser that
   emits the two bytes in swapped order produces a different output packet
   whenever the bytes differ, so the checker must report NotEquivalent. *)
let%expect_test "bitstream non-equivalence: emit order swapped" =
  let p1 = Shim.find_modprog "parse_deparse" in
  let p2 = Shim.find_modprog "parse_deparse_swapped" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {|
    ┌ SAT Valuation
    | var( pkt_1 ) : u64 := 0
    | var( pkt_10 ) : u64 := 1
    | var( pkt_100 ) : u64 := 1
    | var( pkt_1000 ) : u64 := 0
    | var( pkt_10000 ) : u64 := 0
    | var( pkt_1001 ) : u64 := 0
    | var( pkt_101 ) : u64 := 1
    | var( pkt_1010 ) : u64 := 1
    | var( pkt_1011 ) : u64 := 0
    | var( pkt_11 ) : u64 := 0
    | var( pkt_110 ) : u64 := 1
    | var( pkt_1100 ) : u64 := 1
    | var( pkt_1101 ) : u64 := 0
    | var( pkt_111 ) : u64 := 0
    | var( pkt_1110 ) : u64 := 1
    | var( pkt_1111 ) : u64 := 0
    └
    NotEquivalent
    |}]

(* Test 16: bitstream accept/reject.  Two one-byte parse->deparse pipelines whose
   parsers agree on every packet except 0xFF, where one Rejects and the other
   Accepts.  With reject threaded as a symbolic accept predicate, the checker must
   report NotEquivalent, witnessed by the 0xFF packet (every pkt bit = 1).  Under
   the old swallow-the-reject semantics this was wrongly Equivalent. *)
let%expect_test "bitstream accept differs: reject-on-0xFF vs always-accept" =
  let p1 = Shim.find_modprog "parse_reject_deparse" in
  let p2 = Shim.find_modprog "parse_accept_deparse" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {|
    ┌ SAT Valuation
    | var( pkt_1 ) : u64 := 1
    | var( pkt_10 ) : u64 := 1
    | var( pkt_100 ) : u64 := 1
    | var( pkt_1000 ) : u64 := 1
    | var( pkt_101 ) : u64 := 1
    | var( pkt_11 ) : u64 := 1
    | var( pkt_110 ) : u64 := 1
    | var( pkt_111 ) : u64 := 1
    └
    NotEquivalent
    |}]

(* Test 17: the rejecting pipeline is equivalent to itself — the accept
   conditions coincide, so no packet distinguishes it from itself. *)
let%expect_test "bitstream self-equivalence: reject-on-0xFF" =
  let p = Shim.find_modprog "parse_reject_deparse" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p p);
  [%expect {| Equivalent |}]

(* Test 18: read extent.  Both pipelines emit exactly h1 = byte 0, so their
   output packets are identical and the write-tape check alone cannot tell them
   apart (a deparser emits only its emitted bits — the unconsumed tail is not
   appended).  They differ in how much input they consume: 8 bits vs 16.  The
   [check_sym_bits_read] conjunct is what makes this NotEquivalent — a network
   that reads further into its input is not interchangeable with one that does
   not, the bitstream analogue of the memory IR's access-extent equivalence.
   Every packet is a witness, hence the all-zero valuation. *)
let%expect_test "bitstream residual: consume1 vs consume2 (emit h1)" =
  let p1 = Shim.find_modprog "consume1_emit1" in
  let p2 = Shim.find_modprog "consume2_emit1" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {|
    ┌ SAT Valuation
    | var( pkt_1 ) : u64 := 0
    | var( pkt_10 ) : u64 := 0
    | var( pkt_100 ) : u64 := 0
    | var( pkt_1000 ) : u64 := 0
    | var( pkt_101 ) : u64 := 0
    | var( pkt_11 ) : u64 := 0
    | var( pkt_110 ) : u64 := 0
    | var( pkt_111 ) : u64 := 0
    └
    NotEquivalent
    |}]

(* Test 19: data-dependent consumption (consume one or two bytes depending on
   whether byte 0 is zero) is equivalent to itself — the variable-length residual
   merges consistently across the two branches. *)
let%expect_test "bitstream self-equivalence: data-dependent consumption" =
  let p = Shim.find_modprog "varlen_emit1" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p p);
  [%expect {| Equivalent |}]

(* Test 20: write-tape append, symbolically.  mod_prog_parse_deparse emits h1
   and h2 from ONE deparser; mod_prog_two_deparsers emits h1 from one deparser
   and h2 from a second chained after it.  Both consume the same 16-bit packet
   and, because each deparser appends to the shared write tape rather than
   replacing it, both produce the same 16-bit output.  Under the old replacing
   semantics the two-deparser pipeline would emit only h2 -- 8 bits -- and this
   would be NotEquivalent.  This is the symbolic counterpart to the concrete
   "two_deparsers" test in TestModuleSemantics. *)
let%expect_test "bitstream: one deparser emitting h1,h2 = two deparsers chained" =
  let p1 = Shim.find_modprog "parse_deparse" in
  let p2 = Shim.find_modprog "two_deparsers" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| Equivalent |}]
