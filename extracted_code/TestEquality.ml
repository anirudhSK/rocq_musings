open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp

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
  [%expect {|
    ┌ SAT Valuation
    | var( 1 ) := 0
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
  [%expect {|
    ┌ SAT Valuation
    | var( 1 ) := 0
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
    | var( 1000 ) := 254
    | var( 1100 ) := 0
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
