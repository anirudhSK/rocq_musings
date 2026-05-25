let programs = Shim.listify_coq_list TestPrograms.test_programs
let get_program = Stdlib.List.nth programs
let init_state n = CrVarLike.init_concrete_state (get_program n)
let run pid setup =
  let s  = setup (init_state pid) in
  Shim.run_program (get_program pid) s

(* Test 1: Unconditional subtract
 * h1 = 3 → h1 = 1 after subtracting 2. *)
let%expect_test "sub2_h1: h1=3 starts; after -=2" =
  let s' = run 0 (Shim.set_header 1 (Shim.uint8_crval 3)) in
  Shim.print_state s';
  [%expect {| h1=1 |}]

(* Test 2: Predicate mismatch leaves state unchanged
 * Rule fires only when h1 = 0; starting with h1 = 3, nothing changes. *)
let%expect_test "sub5_h1_if_h1eq0: no match, h1=3 unchanged" =
  let s' = run 1 (Shim.set_header 1 (Shim.uint8_crval 3)) in
  Shim.print_state s';
  [%expect {| h1=3 |}]

(* Test 3: sub5_h1_if_h1eq0 — predicate match path
 * Rule fires when h1 = 0; (0 - 5) mod 256 = 251. *)
let%expect_test "sub5_h1_if_h1eq0: match fires, h1=0 underflows" =
  let s' = run 1 (Shim.set_header 1 (Shim.uint8_crval 0)) in
  Shim.print_state s';
  [%expect {| h1=251 |}]

(* Test 4: Predicate match fires the action
 * h1 = 5 matches; h1 = 5 → h1 = 8 after adding 3. *)
let%expect_test "add3_h1_if_h1eq5: match fires, h1=5" =
  let s' = run 2 (Shim.set_header 1 (Shim.uint8_crval 5)) in
  Shim.print_state s';
  [%expect {| h1=8 |}]

(* Test 5: add3_h1_if_h1eq5 — predicate mismatch path
 * Pattern requires h1 = 5; with h1 = 7 the rule does not fire. *)
let%expect_test "add3_h1_if_h1eq5: no match, h1=7 unchanged" =
  let s' = run 2 (Shim.set_header 1 (Shim.uint8_crval 7)) in
  Shim.print_state s';
  [%expect {| h1=7 |}]

(* Test 6: First-match semantics
 * Both rules match h1 = 5; only the first (h1 += 1) fires. *)
let%expect_test "first_match_h1eq5: only rule 1 fires" =
  let s' = run 3 (Shim.set_header 1 (Shim.uint8_crval 5)) in
  Shim.print_state s';
  [%expect {| h1=6 |}]

(* Test 7: first_match_h1eq5 — neither rule matches
 * Both rules require h1 = 5; with h1 = 3 neither fires. *)
let%expect_test "first_match_h1eq5: no rule matches" =
  let s' = run 3 (Shim.set_header 1 (Shim.uint8_crval 3)) in
  Shim.print_state s';
  [%expect {| h1=3 |}]

(* Test 8: StatefulOp writes to a state variable; header is unchanged
 * s1 := h1 - 2. With h1 = 10: s1 = 8, h1 remains 10. *)
let%expect_test "stateful_sub2: h1=10 writes s1, leaves h1" =
  let s' = run 4 (Shim.set_header 1 (Shim.uint8_crval 10)) in
  Shim.print_state s';
  [%expect {|
    h1=10
    s1=8
  |}]

(* Test 9: Ctrl-plane variable used as an operand
 * h1 := h1 + ctrl1. With h1 = 5, ctrl1 = 3: h1 = 8. *)
let%expect_test "add_ctrl1_to_h1: h1=5, ctrl1=3" =
  let s' = run 5 (fun s ->
    Shim.set_ctrl   1 (Shim.uint8_crval 3)
      (Shim.set_header 1 (Shim.uint8_crval 5) s)) in
  Shim.print_state s';
  [%expect {|
    h1=8
    c1=3
  |}]

(* Test 10: Action list fold_left order — head of list executes first
 * action = [h1 += 1 ; h1 *= 2]: the add (head) runs first.
 * h1 = 10 → 10 + 1 = 11 → 11 * 2 = 22. *)
let%expect_test "fold_left_order: h1=10, +1 before *2" =
  let s' = run 6 (Shim.set_header 1 (Shim.uint8_crval 10)) in
  Shim.print_state s';
  [%expect {| h1=22 |}]

(* Test 11: SubOp underflow wraps modulo 2^8 *)
let%expect_test "sub_underflow_h1: 2 - 5 wraps" =
  let s' = run 7 (Shim.set_header 1 (Shim.uint8_crval 2)) in
  Shim.print_state s';
  [%expect {| h1=253 |}]

(* Test 12: AddOp overflow wraps modulo 2^8 *)
let%expect_test "add_overflow_h1: 250 + 10 wraps" =
  let s' = run 8 (Shim.set_header 1 (Shim.uint8_crval 250)) in
  Shim.print_state s';
  [%expect {| h1=4 |}]

(* Test 13: Bitwise AND mask. h1 := h1 AND 0x0F with h1=0xAB. *)
let%expect_test "and_mask_h1: 0xAB AND 0x0F" =
  let s' = run 9 (Shim.set_header 1 (Shim.uint8_crval 171)) in
  Shim.print_state s';
  [%expect {| h1=11 |}]

(* Test 14: Bitwise OR. h1 := h1 OR 0xF0 with h1=0x05. *)
let%expect_test "or_h1: 0x05 OR 0xF0" =
  let s' = run 10 (Shim.set_header 1 (Shim.uint8_crval 5)) in
  Shim.print_state s';
  [%expect {| h1=245 |}]

(* Test 15: Bitwise XOR. h1 := h1 XOR 0xFF with h1=0x55. *)
let%expect_test "xor_h1: 0x55 XOR 0xFF" =
  let s' = run 11 (Shim.set_header 1 (Shim.uint8_crval 85)) in
  Shim.print_state s';
  [%expect {| h1=170 |}]

(* Test 16: MulOp *)
let%expect_test "mul_h1: 3 * 7" =
  let s' = run 12 (Shim.set_header 1 (Shim.uint8_crval 3)) in
  Shim.print_state s';
  [%expect {| h1=21 |}]

(* Test 17: DivOp (unsigned) *)
let%expect_test "div_h1: 10 / 3" =
  let s' = run 13 (Shim.set_header 1 (Shim.uint8_crval 10)) in
  Shim.print_state s';
  [%expect {| h1=3 |}]

(* Test 18: ModOp (unsigned) *)
let%expect_test "mod_h1: 23 mod 7" =
  let s' = run 14 (Shim.set_header 1 (Shim.uint8_crval 23)) in
  Shim.print_state s';
  [%expect {| h1=2 |}]

(* Test 19: StatefulArg used as an input operand
 * h1 := h1 + s1. With h1 = 3 and s1 = 4: h1 = 7, s1 unchanged. *)
let%expect_test "stateful_arg_input: h1=3, s1=4" =
  let s' = run 15 (fun s ->
    Shim.set_state  1 (Shim.uint8_crval 4)
      (Shim.set_header 1 (Shim.uint8_crval 3) s)) in
  Shim.print_state s';
  [%expect {|
    h1=7
    s1=4
  |}]

(* Test 20: Multi-rule, first rule does not match, second does *)
let%expect_test "multi_rule_second_matches: second fires, h1=10" =
  let s' = run 16 (Shim.set_header 1 (Shim.uint8_crval 10)) in
  Shim.print_state s';
  [%expect {| h1=110 |}]

(* Test 21: multi_rule_second_matches — first rule fires *)
let%expect_test "multi_rule_second_matches: first fires, h1=5" =
  let s' = run 16 (Shim.set_header 1 (Shim.uint8_crval 5)) in
  Shim.print_state s';
  [%expect {| h1=6 |}]

(* Test 22: multi_rule_second_matches — neither rule matches *)
let%expect_test "multi_rule_second_matches: no rule matches, h1=3" =
  let s' = run 16 (Shim.set_header 1 (Shim.uint8_crval 3)) in
  Shim.print_state s';
  [%expect {| h1=3 |}]

(* Test 23: Cross-header predicate (predicate on h2, write to h1)
 * When h2 = 7: h1 := h1 + 1. *)
let%expect_test "cross_header_predicate: h2=7 gates h1+=1" =
  let s' = run 17 (fun s ->
    Shim.set_header 2 (Shim.uint8_crval 7)
      (Shim.set_header 1 (Shim.uint8_crval 5) s)) in
  Shim.print_state s';
  [%expect {| h1=6, h2=7 |}]

(* Test 24: cross_header_predicate — predicate fails *)
let%expect_test "cross_header_predicate: h2=1 leaves h1" =
  let s' = run 17 (fun s ->
    Shim.set_header 2 (Shim.uint8_crval 1)
      (Shim.set_header 1 (Shim.uint8_crval 5) s)) in
  Shim.print_state s';
  [%expect {| h1=5, h2=1 |}]

(* Test 25: Empty transformer leaves state unchanged *)
let%expect_test "empty_transformer: h1=42 unchanged" =
  let s' = run 18 (Shim.set_header 1 (Shim.uint8_crval 42)) in
  Shim.print_state s';
  [%expect {| h1=42 |}]
