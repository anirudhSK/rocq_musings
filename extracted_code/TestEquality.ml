open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  let p = str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp in
  Shim.print_malformed_prog p 0;
  p

let get_general_program f =
  let p = Shim.load_general_program f in
  Shim.print_malformed_gprog p f;
  p

let print_equiv = function
  | SmtQuery.Equivalent -> print_endline "Equivalent"
  | SmtQuery.NotEquivalent _ -> print_endline "NotEquivalent"
  | SmtQuery.NotEquivalentUnknown -> print_endline "NotEquivalentUnknown"
  | SmtQuery.NotEquivalentVariablesDiffer -> print_endline "NotEquivalentVariablesDiffer"

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
    | var( hdr_1 ) := uninit
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

(* Test 6: -O0 vs -O2 of one eBPF program -- the point of the whole memory
   merge.  ../test/bpf_O{0,2}.ir are `~/proj/ect/bpf_to_ir` output for the -O0
   and -O2 lowerings of one XDP program (test/bpf_ref.c), regenerated there
   with `make O0.ir O2.ir`.  They are module networks, so unlike test 12 this
   runs through modnet_equivalence_checker and Z3Solver, and compares the
   emitted return value, the bits read, and the contents and access extents of
   the ctx and packet regions. *)
let%expect_test "e2e bpf test: O0 ≡ O2" =
  let p1 = get_general_program "../test/bpf_O0.ir" in
  let p2 = get_general_program "../test/bpf_O2.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| Equivalent |}]

(* Test 13: linear scan vs tss for simple filter database.  Both are full
   parser -> table chain -> deparser networks over a 192-bit input packet (what
   field_extractor consumes), so they go through the bitstream checker: the
   observable is the label byte the deparser emits.*)
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

(* -------------------------------------------------------------------- *)
(* Tests 21-26: memory.                                                 *)
(*                                                                      *)
(* All of these run through the SAME checker and the SAME solver as the *)
(* network tests above -- the point of the unification.  Region 1 is    *)
(* declared with 4 cells in every one of these programs, so offsets     *)
(* 0..3 are in bounds and 4 is not.                                     *)
(* -------------------------------------------------------------------- *)

let check n1 n2 =
  print_equiv (SmtModuleQuery.modnet_equivalence_checker
                 (Shim.find_modprog n1) (Shim.find_modprog n2))

(* Test 21: address aliasing.  One program writes the offset literally, the
   other computes it into a header first.  Which header holds an address is
   internal, so the two agree -- and the solver has to reason about the
   computed index to see it, since [SmtArrSel] takes the index symbolically. *)
let%expect_test "mem: a computed offset aliases a literal one" =
  check "mem_store_load" "mem_store_load_alias";
  [%expect {| Equivalent |}]

(* Test 22: same shape, same extent, different value stored.  Caught by the
   region-contents conjunct and by the output packet. *)
let%expect_test "mem: a different stored value is not equivalent" =
  check "mem_store_load" "mem_store_load_differs";
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
    | mem( mem_1 ) : len=4 := [-, -, -, -]
    └
    NotEquivalent
    |}]

(* Test 23: two programs whose only difference is which scratch header a dead
   load lands in.  Headers are internal, so this is unobservable. *)
let%expect_test "mem: the scratch header a dead load targets is internal" =
  check "mem_load1_load0" "mem_load1_load0_alt";
  [%expect {| Equivalent |}]

(* Test 24: THE extent test, and the reason [sh_mem_extent] exists.  Both
   programs read only cells that were never written, so both emit the same
   zero byte and leave the region untouched -- output equality and contents
   equality cannot tell them apart.  They differ solely in that one reaches
   cell 1 and the other stops at cell 0, which is a real difference: one can
   fault where the other cannot.  If this reports Equivalent, the extent is
   not reaching the query.  (Compare test 18, its bitstream analogue.) *)
let%expect_test "mem: reading one cell further is not equivalent" =
  check "mem_load1_load0" "mem_load0";
  [%expect {|
    ┌ SAT Valuation
    | mem( mem_1 ) : len=4 := [-, -, -, -]
    └
    NotEquivalent
    |}]

(* Test 25: in bounds, the order of a load and a store to one cell matters --
   the second program reads back what it just wrote, the first does not. *)
let%expect_test "mem: in bounds, load-then-store differs from store-then-load" =
  check "mem_ib_load_store" "mem_store_load";
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
    | mem( mem_1 ) : len=4 := [254:u8, 254:u8, 254:u8, 254:u8]
    └
    NotEquivalent
    |}]

(* Test 26: the same pair at an out-of-bounds offset, where order stops
   mattering: the store is dropped and the load yields ErrorVal either way.
   This is the test that the Z3 lowering guards BOTH memory operations with the
   region's declared length -- Z3's array theory is total, so:

     - an unguarded [select] would let the store-then-load program read its own
       out-of-bounds write back;
     - an unguarded [store] would leave the two regions differing at offset 4,
       which the [SmtArrEq] encoding *does* see (extensional array equality
       looks at every index, unlike the old per-cell conjunction over 0..3).

   Either way the checker would report NotEquivalent on a difference the
   concrete semantics cannot produce, i.e. an unsound verdict.  The store half
   of that became load-bearing when the cell-by-cell comparison was replaced;
   before, nothing in the query ever looked at offset 4.  Together with test 25
   this pins the bound down from both sides. *)
let%expect_test "mem: out of bounds, the order stops mattering" =
  check "mem_oob_load_store" "mem_oob_store_load";
  [%expect {| Equivalent |}]

(* The replacement for the retired memory IR's "a branch on a constant
   collapses": a match pattern that cannot fail is the same as no pattern.
   [CrVal.eqb] is reflexive on every constructor, so a header compared to
   itself always matches. *)
let%expect_test "mem: a guard that cannot fail is the same as no guard" =
  check "mem_guard_tautology" "mem_store_load";
  [%expect {| Equivalent |}]

(* Memory is an array of BYTES, so a u16 store is exactly the two u8 stores an
   optimiser coalesces it from.  This pair is the reason for that model: under
   the previous one-value-per-cell scheme they landed in different cells with
   different types and came back NotEquivalent -- a false positive on any
   -O0 vs -O2 comparison, since -O2 merges adjacent narrow stores. *)
let%expect_test "mem: a u16 store is the two u8 stores it coalesces from" =
  check "mem_two_u8_stores" "mem_one_u16_store";
  [%expect {| Equivalent |}]
