open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  let p = str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp in
  Shim.print_malformed_prog p 0;
  p

let get_parser f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  let p = str |> Sexp.of_string |> CrTypeIF.CrParser.coq_Parser_of_sexp in
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
  [%expect {| NotEquivalent |}]

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
  [%expect {| NotEquivalent |}]

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

(* The same pipeline over a program that calls bpf_map_lookup_elem, from
   ~/proj/ect/ex/map_*.c (regenerate with `make` there, then
   `./bpf_to_ir ex/<name>.o > <ir>/test/bpf_<name>.ir`).  A map is a declared
   region whose first [nslots] bytes are presence flags and whose remainder is
   the values, so both a hit and a miss are ordinary symbolic input.

   The verdicts have to come in both directions to mean anything.  map_spill is
   map_ref with the looked-up value round-tripped through a volatile stack
   slot: different bytecode, same meaning.  The other two are map_ref with one
   arm of the lookup changed, and they are what pin the arms as REACHABLE -- if
   the miss arm were pruned, map_miss_differs would come back Equivalent, and if
   the hit arm never read the map region, map_hit_differs would. *)
let%expect_test "e2e bpf map test: a lookup and a stack spill agree" =
  let p1 = get_general_program "../test/bpf_map_ref.ir" in
  let p2 = get_general_program "../test/bpf_map_spill.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| Equivalent |}]

let%expect_test "e2e bpf map test: the miss arm of a lookup is reachable" =
  let p1 = get_general_program "../test/bpf_map_ref.ir" in
  let p2 = get_general_program "../test/bpf_map_miss_differs.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]

let%expect_test "e2e bpf map test: the hit arm reads the map region" =
  let p1 = get_general_program "../test/bpf_map_ref.ir" in
  let p2 = get_general_program "../test/bpf_map_hit_differs.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]


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
  [%expect {| NotEquivalent |}]

(* Test 16: bitstream accept/reject.  Two one-byte parse->deparse pipelines whose
   parsers agree on every packet except 0xFF, where one Rejects and the other
   Accepts.  With reject threaded as a symbolic accept predicate, the checker must
   report NotEquivalent, witnessed by the 0xFF packet (every pkt bit = 1).  Under
   the old swallow-the-reject semantics this was wrongly Equivalent. *)
let%expect_test "bitstream accept differs: reject-on-0xFF vs always-accept" =
  let p1 = Shim.find_modprog "parse_reject_deparse" in
  let p2 = Shim.find_modprog "parse_accept_deparse" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]

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
  [%expect {| NotEquivalent |}]

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

(* The positive control for the region model, and the reason it exists.  Two
   programs that branch on a byte loaded from a region, one testing [b > 100]
   and the other [b < 101] -- the same test for any byte, so Equivalent.

   Before a region's cells were pinned to bytes this came back NotEquivalent:
   a model could leave cell 0 non-integer, [ld_val]'s [cast u8 _] then made the
   loaded header ErrorVal, and [CrVal.ltb] is false on ErrorVal in BOTH
   directions -- so neither match fired, both defaults ran, and the two emitted
   different bytes on an input no machine produces.  It is the whole family of
   opposite-direction comparisons, which is what an -O0/-O2 pair is full of. *)
let%expect_test "mem: comparing a loaded byte either way round agrees" =
  check "mem_cmp_gt" "mem_cmp_lt";
  [%expect {| Equivalent |}]

(* Test 22: same shape, same extent, different value stored.  Caught by the
   region-contents conjunct and by the output packet. *)
let%expect_test "mem: a different stored value is not equivalent" =
  check "mem_store_load" "mem_store_load_differs";
  [%expect {| NotEquivalent |}]

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
  [%expect {| NotEquivalent |}]

(* Test 25: in bounds, the order of a load and a store to one cell matters --
   the second program reads back what it just wrote, the first does not. *)
let%expect_test "mem: in bounds, load-then-store differs from store-then-load" =
  check "mem_ib_load_store" "mem_store_load";
  [%expect {| NotEquivalent |}]

(* Test 26: the same pair at an out-of-bounds offset.  READ WHAT THIS STILL
   CHECKS AND WHAT IT NO LONGER DOES.

   It used to pin the Z3 lowering's bounds guards on [SmtArrSel] and
   [SmtArrSt]: order stops mattering out of bounds only if the store is really
   dropped and the load really yields ErrorVal, so an unguarded select or store
   turned this into NotEquivalent.  That is gone.  Both runs overrun a
   four-byte region, so [mem_extents_in_bounds_smt] makes both invalid and
   [check_sym_pkt_out]'s both-reject disjunct answers Equivalent without ever
   looking at the memory conjuncts.  The verdict below is now insensitive to
   the guards.

   The guards are pinned by the "witness: an out-of-bounds read/write" pair at
   the bottom of this file instead, which builds the expressions directly and
   so does not go through [gps_valid].  What test 26 still checks is that an
   out-of-bounds run rejects rather than diverging or faulting the checker. *)
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

(* Compares the spec program to a program generated by lowering
   the ParserHawk-generated pipeline. *)
let%expect_test "parserhawk: ICMP" =
  let spec_program = ParserHawkEval.icmp_spec in
  let synth_parser = get_parser "../test/parserhawk/icmp_ipu.ir" in
  let synth_program = ParserHawkEval.dump_headers synth_parser
    (ParserHawkEval.ICMPHdr (Shim.int_to_pos 1, Shim.int_to_pos 2)) in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker spec_program synth_program);
  [%expect {| Equivalent |}]

let%expect_test "parserhawk: SAI" =
  let spec_program = ParserHawkEval.sai_spec in
  let synth_parser = get_parser "../test/parserhawk/sai_tofino.ir" in
  let synth_program = ParserHawkEval.dump_headers synth_parser
    (ParserHawkEval.SAIHdr
       (Shim.int_to_pos 1, Shim.int_to_pos 2, Shim.int_to_pos 3,
        Shim.int_to_pos 4, Shim.int_to_pos 5, Shim.int_to_pos 6,
        Shim.int_to_pos 7, Shim.int_to_pos 8, Shim.int_to_pos 9)) in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker spec_program synth_program);
  [%expect {| Equivalent |}]

(* Compares ParserHawk's synthesized tofino and IPU pipelines *)
let%expect_test "parserhawk: ethernet tofino vs ipu" =
  let tofino_parser = get_parser "../test/parserhawk/ethernet_tofino.ir" in
  let tofino_program = ParserHawkEval.dump_headers tofino_parser
    (ParserHawkEval.EthHdr (Shim.int_to_pos 1, Shim.int_to_pos 2)) in
  let ipu_parser = get_parser "../test/parserhawk/ethernet_ipu.ir" in
  let ipu_program = ParserHawkEval.dump_headers ipu_parser
    (ParserHawkEval.EthHdr (Shim.int_to_pos 1, Shim.int_to_pos 2)) in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker tofino_program ipu_program);
  [%expect {| Equivalent |}]

(* ParserHawk multiple field key *)
let%expect_test "parserhawk: multifield tofino vs spec" =
  let tof = get_parser "../test/parserhawk/multifield_tofino.ir" in
  let spec = ParserHawkEval.mfk_spec in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker (ParserHawkEval.dump_headers tof
    (ParserHawkEval.MultiFieldHdr
       (Shim.int_to_pos 1, Shim.int_to_pos 2, Shim.int_to_pos 3))) spec);
  [%expect {| Equivalent |}]

let%expect_test "parserhawk: multifield ipu vs spec" =
  let ipu = get_parser "../test/parserhawk/multifield_ipu.ir" in
  let spec = ParserHawkEval.mfk_spec in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker (ParserHawkEval.dump_headers ipu
    (ParserHawkEval.MultiFieldHdr
       (Shim.int_to_pos 1, Shim.int_to_pos 2, Shim.int_to_pos 3))) spec);
  [%expect {| NotEquivalent |}]

let%expect_test "parserhawk: multifield tofino vs ipu" =
  let tof = get_parser "../test/parserhawk/multifield_tofino.ir" in
  let ipu = get_parser "../test/parserhawk/multifield_ipu.ir" in
  let mk p = ParserHawkEval.dump_headers p
    (ParserHawkEval.MultiFieldHdr
       (Shim.int_to_pos 1, Shim.int_to_pos 2, Shim.int_to_pos 3)) in
  Shim.print_malformed_gprog (mk tof) "multifield_tofino";
  Shim.print_malformed_gprog (mk ipu) "multifield_ipu";
  print_equiv (SmtModuleQuery.modnet_equivalence_checker (mk tof) (mk ipu));
  [%expect {| NotEquivalent |}]

(* A header some parser extracts is a FIELD REGISTER: it holds an arbitrary
   value of its own width on entry, not [UninitVal].  These two parsers differ
   only in a select that reads h1 BEFORE the state that extracts it, so they
   agree on every packet and differ only on the register's initial contents --
   the counterexample is [hdr_1 := 255], the value whose low byte makes one
   reject and the other accept.

   Seed the register uninit instead and this pair comes back Equivalent:
   [slice_val] of [UninitVal] is [ErrorVal], [CrVal.eqb] is false against every
   pattern, so the case can never fire and the two collapse into one program.
   Verified both ways round.  This is the shape ParserHawk's IPU pipelines
   emit -- a transition key naming a field a later node extracts. *)
let%expect_test "hdr init: a register read before its extraction is free" =
  let p1 = Shim.find_modprog "hdr_init_sel" in
  let p2 = Shim.find_modprog "hdr_init_nosel" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]

(* ===================================================================== *)
(* Witness checking: solve an [SmtBoolExpr], then re-evaluate that same   *)
(* expression under the model Z3 returned.  [eval_smt_bool] is the Coq    *)
(* semantics, so a "REJECTED" line is Z3 and Rocq disagreeing -- i.e.     *)
(* [smt_query_sound_some] failing.  No verdict test can see this: the     *)
(* verdict is right, only the witness is wrong.  SOUNDNESS.md, on reading *)
(* a tag back, has the bugs these were written for.                       *)
(* ===================================================================== *)

let u64 n = Shim.int_to_coq_uint64 n
let konst n ty = SmtExpr.SmtArithConst (u64 n, ty)
let svar s = SmtExpr.SmtArithVar (Shim.str_to_coq_str s)
let avar s len = SmtExpr.SmtArrVar (Shim.str_to_coq_str s, u64 len)
(* [cast] of a non-[IntVal] is [ErrorVal] (CrVal.v), so this is an error
   literal -- the language has none, and [SmtUninit] is not one. *)
let err_lit = SmtExpr.SmtCast (CrVal.W8, CrVal.W16, SmtExpr.SmtUninit)

let witness name (e : SmtExpr.coq_SmtBoolExpr) =
  match Z3Solver.solve e with
  | SmtTypes.SmtSat v ->
      (match SmtExpr.eval_smt_bool e v with
       | Datatypes.Coq_true  -> Printf.printf "%s: SAT, witness verified\n" name
       | Datatypes.Coq_false ->
           Printf.printf "%s: SAT, WITNESS REJECTED by eval_smt_bool\n" name)
  | SmtTypes.SmtUnsat   -> Printf.printf "%s: UNSAT\n" name
  | SmtTypes.SmtUnknown -> Printf.printf "%s: unknown\n" name

let%expect_test "witness: a scalar the model leaves non-integer" =
  (* A scalar still CAN be ErrorVal: [eval_smt_arith]'s [SmtArithVar] arm
     coerces every non-[IntVal] to it, mirroring the lowering's
     [ite (tag_is_int t) t tag_err].  Left as is deliberately -- at network
     level the free scalars are per-program state and ctrl variables, which
     [check_sym_pkt_out] never compares, while the free inputs the two
     programs SHARE are the packet bits and the memory regions.  The regions
     are the ones that had to be pinned; see the next test. *)
  witness "scalar-error" (SmtExpr.SmtBoolEq (svar "x", err_lit));
  [%expect {|
    scalar-error: SAT, witness verified
    |}]

let%expect_test "witness: a memory cell cannot be left non-integer" =
  (* UNSAT, and it is the regression test for the region model.  A region's
     contents on entry are an INPUT, and a real one is bytes, so
     [eval_smt_mem]'s [SmtArrVar] arm sends them through [CrVal.to_byte] and
     [Z3Solver] pins each cell of 0..[len) to the [u8] tag with its value
     bounded by 255.  Those two have to move together: loosen one and a
     [smt_query_sound_*] axiom is false.

     This used to be SAT with cell 0 [err], and that was a live source of false
     [NotEquivalent]s.  [ld_val] casts every cell with [cast u8 _], so ONE bad
     cell makes the whole multi-byte load ErrorVal, and [CrVal.ltb] is false on
     ErrorVal in both directions -- so [x > 100] and [x < 101] are both false,
     and two programs testing opposite ways were reported different on a
     machine state that cannot occur. *)
  witness "cell-error"
    (SmtExpr.SmtBoolEq (SmtExpr.SmtArrSel (avar "a" 4, konst 0 CrVal.W64), err_lit));
  [%expect {| cell-error: UNSAT |}]

let%expect_test "witness: a cell read back is the cell that is there" =
  (* Stores cell 0 back onto itself, then asks whether the region changed.
     [SmtArrEq] lowers to [mk_eq] on whole arrays, which sees RAW cell tags,
     while [SmtArrSel] sees normalised ones -- if those two disagree, Z3 finds
     a difference that the reconstruction cannot represent. *)
  let a = avar "a" 4 in
  let sel0 = SmtExpr.SmtArrSel (a, konst 0 CrVal.W64) in
  let stored = SmtExpr.SmtArrSt (a, konst 0 CrVal.W64, sel0) in
  witness "noop-store"
    (SmtExpr.SmtBoolNot (SmtExpr.SmtArrEq (Shim.int_to_coq_nat 4, a, stored)));
  [%expect {| noop-store: UNSAT |}]

(* The two guards that "mem: out of bounds, the order stops mattering" used to
   pin from the verdict side.  It cannot any more: an out-of-bounds run is now
   invalid ([mem_extents_in_bounds_smt]), so that pair is Equivalent by the
   both-reject disjunct whatever the lowering does with the offending access.
   Stated here instead, where [gps_valid] is not in the picture at all.

   They still matter because an offset can be data-dependent: a run is invalid
   only on the valuations that actually overrun, and on the rest the checker
   compares regions as before. *)
let%expect_test "witness: an out-of-bounds read is ErrorVal, not a cell" =
  (* Z3's [select] is total and [ld_arr] is not.  Drop the [ite] guard in
     [Z3Solver.lower_arith] and Z3 finds a model giving cell 4 of a 4-cell
     region some integer, which [eval_smt_bool] then rejects. *)
  witness "oob-select"
    (SmtExpr.SmtBoolNot
       (SmtExpr.SmtBoolEq
          (SmtExpr.SmtArrSel (avar "a" 4, konst 4 CrVal.W64), err_lit)));
  [%expect {| oob-select: UNSAT |}]

let%expect_test "witness: an out-of-bounds write leaves the region alone" =
  (* The store-side mirror.  [st_arr] refuses and returns the region
     unchanged; Z3's [store] is total, so without the guard the two arrays
     differ at index 4 -- which [SmtArrEq]'s [mk_eq] lowering DOES see, unlike
     the old per-cell conjunction over 0..3. *)
  let a = avar "a" 4 in
  let stored = SmtExpr.SmtArrSt (a, konst 4 CrVal.W64, konst 7 CrVal.W8) in
  witness "oob-store"
    (SmtExpr.SmtBoolNot (SmtExpr.SmtArrEq (Shim.int_to_coq_nat 4, a, stored)));
  [%expect {| oob-store: UNSAT |}]

let%expect_test "witness: two undeclared regions agree" =
  (* [SmtArrInit] denotes [Unallocated], and [arr_agree_upto n Unallocated
     Unallocated] is [true] for every n -- [ld_arr] is [Illegal] on both sides.
     So the negation must be UNSAT, which holds only if both occurrences lower
     to ONE Z3 term.  If they ever lower to two fresh consts this comes back
     SAT (and the witness is unreconstructable), which is what would happen if
     [SmtArrInit] gained an argument and stopped being an immediate. *)
  witness "undeclared-agree"
    (SmtExpr.SmtBoolNot
       (SmtExpr.SmtArrEq
          (Shim.int_to_coq_nat 4, SmtExpr.SmtArrInit, SmtExpr.SmtArrInit)));
  [%expect {| undeclared-agree: UNSAT |}]

(* Suricata's ebpf/vlan_filter.c (~/proj/ect/ex/vlan_filter.c), a real
   production socket filter, against the same filter accepting VLAN 3 and 5
   instead of 2 and 4.

   This is a regression test for the CONTEXT LAYOUT as much as for the filter.
   An __sk_buff program reaches vlan_tci at ctx offset 24 and data/data_end at
   76/80; while bpf_to_ir modelled every ctx as struct xdp_md's 20 bytes, all
   of those overran the region, an overrun rejects the run at the sink, and the
   both-rejected disjunct then reported these two Equivalent -- with the
   translator exiting 0.  So Equivalent here does not mean "no change", it
   means the filter stopped running. *)
let%expect_test "e2e bpf: suricata vlan_filter distinguishes its VLAN set" =
  let p1 = get_general_program "../test/bpf_vlan_filter.ir" in
  let p2 = get_general_program "../test/bpf_vlan_filter_alt.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]

let%expect_test "e2e bpf: suricata vlan_filter is equivalent to itself" =
  let p = get_general_program "../test/bpf_vlan_filter.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p p);
  [%expect {| Equivalent |}]

let%expect_test "u16 load == two u8 loads" =
  let p1 = get_general_program "../test/basic_load.ir" in
  let p2 = get_general_program "../test/basic_load_split.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| Equivalent |}]
(* Suricata's ebpf/filter.c (~/proj/ect/ex/sur_filter.c) against itself with
   the DADDR branch returning 7 instead of 0.  It is the widest single test of
   the translator: two map lookups, a store through a returned value pointer,
   LD_ABS and LD_IND packet reads, and a ctx store.

   NotEquivalent here is specifically evidence that the SECOND lookup is
   reached.  It was not while the packet region was 32 bytes: the daddr read
   at packet offset 30..33 overran it, the run rejected, and these two came
   back Equivalent with the translator exiting 0. *)
let%expect_test "e2e bpf: suricata filter.c reaches its second map lookup" =
  let p1 = get_general_program "../test/bpf_sur_filter.ir" in
  let p2 = get_general_program "../test/bpf_sur_filter_alt.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p1 p2);
  [%expect {| NotEquivalent |}]

let%expect_test "e2e bpf: suricata filter.c is equivalent to itself" =
  let p = get_general_program "../test/bpf_sur_filter.ir" in
  print_equiv (SmtModuleQuery.modnet_equivalence_checker p p);
  [%expect {| Equivalent |}]

