let programs =
  let rec aux acc = function
    | Datatypes.Coq_nil -> Stdlib.List.rev acc
    | Datatypes.Coq_cons (h, t) -> aux (h :: acc) t
  in aux [] TestPrograms.test_programs
let get_program = Stdlib.List.nth programs
let init_state n = CrVarLike.init_concrete_state (get_program n)

let semantics_tests = ref []
let register_semantics test_label test_fn =
  semantics_tests := (test_label, test_fn) :: !semantics_tests

(* Test 1: Unconditional subtract
 * h1 = 3 → h1 = 1 after subtracting 2. *)
let () = register_semantics "sub2_h1: h1=3 → h1=1" (fun () ->
  let pid = 0 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 1 then 1 else 0)

(* Test 2: Predicate mismatch leaves state unchanged
 * Rule fires only when h1 = 0; starting with h1 = 3, nothing changes. *)
let () = register_semantics "sub5_h1_if_h1eq0: no match, h1=3 unchanged" (fun () ->
  let pid = 1 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 3 then 1 else 0)

(* Test 3: sub5_h1_if_h1eq0 — predicate match path
 * Rule fires when h1 = 0; (0 - 5) mod 256 = 251. *)
let () = register_semantics "sub5_h1_if_h1eq0: match fires, h1=0 → h1=251" (fun () ->
  let pid = 1 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 0) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 251 then 1 else 0)

(* Test 4: Predicate match fires the action
 * h1 = 5 matches; h1 = 5 → h1 = 8 after adding 3. *)
let () = register_semantics "add3_h1_if_h1eq5: match fires, h1=5 → h1=8" (fun () ->
  let pid = 2 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 8 then 1 else 0)

(* Test 5: add3_h1_if_h1eq5 — predicate mismatch path
 * Pattern requires h1 = 5; with h1 = 7 the rule does not fire. *)
let () = register_semantics "add3_h1_if_h1eq5: no match, h1=7 unchanged" (fun () ->
  let pid = 2 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 7) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 7 then 1 else 0)

(* Test 6: First-match semantics
 * Both rules match h1 = 5; only the first (h1 += 1) fires.
 * h1 = 5 → h1 = 6, not 15. *)
let () = register_semantics "first_match_h1eq5: only rule 1 fires, h1=5 → h1=6" (fun () ->
  let pid = 3 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 6 then 1 else 0)

(* Test 7: first_match_h1eq5 — neither rule matches
 * Both rules require h1 = 5; with h1 = 3 neither fires. *)
let () = register_semantics "first_match_h1eq5: no rule matches, h1=3 unchanged" (fun () ->
  let pid = 3 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 3 then 1 else 0)

(* Test 8: StatefulOp writes to a state variable; header is unchanged
 * s1 := h1 - 2. With h1 = 10: s1 = 8, h1 remains 10. *)
let () = register_semantics "stateful_sub2: h1=10 → s1=8, h1 unchanged" (fun () ->
  let pid = 4 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 10) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  let s1_ok = Shim.crval_to_int (Shim.get_state  1 s') = 8 in
  let h1_ok = Shim.crval_to_int (Shim.get_header 1 s') = 10 in
  if s1_ok && h1_ok then 1 else 0)

(* Test 9: Ctrl-plane variable used as an operand
 * h1 := h1 + ctrl1. With h1 = 5, ctrl1 = 3: h1 = 8. *)
let () = register_semantics "add_ctrl1_to_h1: h1=5, ctrl1=3 → h1=8" (fun () ->
  let pid = 5 in
  let s  = Shim.set_ctrl   1 (Shim.uint8_crval 3)
             (Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid)) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 8 then 1 else 0)

(* Test 10: Action list fold_left order — head of list executes first
 * action = [h1 += 1 ; h1 *= 2]: the add (head) runs first.
 * h1 = 10 → 10 + 1 = 11 → 11 * 2 = 22. *)
let () = register_semantics "fold_left_order: h1=10 → 22 (+1 before ×2)" (fun () ->
  let pid = 6 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 10) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 22 then 1 else 0)

(* Test 11: SubOp underflow wraps modulo 2^8
 * h1 := h1 - 5. With h1 = 2: (2 - 5) mod 256 = 253. *)
let () = register_semantics "sub_underflow_h1: h1=2 → h1=253" (fun () ->
  let pid = 7 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 2) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 253 then 1 else 0)

(* Test 12: AddOp overflow wraps modulo 2^8
 * h1 := h1 + 10. With h1 = 250: (250 + 10) mod 256 = 4. *)
let () = register_semantics "add_overflow_h1: h1=250 → h1=4" (fun () ->
  let pid = 8 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 250) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 4 then 1 else 0)

(* Test 13: Bitwise AND mask
 * h1 := h1 AND 0x0F. With h1 = 0xAB (171): 0x0B (11). *)
let () = register_semantics "and_mask_h1: h1=0xAB → h1=0x0B" (fun () ->
  let pid = 9 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 171) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 11 then 1 else 0)

(* Test 14: Bitwise OR
 * h1 := h1 OR 0xF0. With h1 = 0x05 (5): 0xF5 (245). *)
let () = register_semantics "or_h1: h1=0x05 → h1=0xF5" (fun () ->
  let pid = 10 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 245 then 1 else 0)

(* Test 15: Bitwise XOR (invert via XOR with 0xFF)
 * h1 := h1 XOR 0xFF. With h1 = 0x55 (85): 0xAA (170). *)
let () = register_semantics "xor_h1: h1=0x55 → h1=0xAA" (fun () ->
  let pid = 11 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 85) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 170 then 1 else 0)

(* Test 16: MulOp
 * h1 := h1 * 7. With h1 = 3: 21. *)
let () = register_semantics "mul_h1: h1=3 → h1=21" (fun () ->
  let pid = 12 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 21 then 1 else 0)

(* Test 17: DivOp (unsigned)
 * h1 := h1 / 3. With h1 = 10: 3. *)
let () = register_semantics "div_h1: h1=10 → h1=3" (fun () ->
  let pid = 13 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 10) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 3 then 1 else 0)

(* Test 18: ModOp (unsigned)
 * h1 := h1 mod 7. With h1 = 23: 2. *)
let () = register_semantics "mod_h1: h1=23 → h1=2" (fun () ->
  let pid = 14 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 23) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 2 then 1 else 0)

(* Test 19: StatefulArg used as an input operand
 * h1 := h1 + s1. With h1 = 3 and s1 = 4: h1 = 7, s1 unchanged. *)
let () = register_semantics "stateful_arg_input: h1=3, s1=4 → h1=7" (fun () ->
  let pid = 15 in
  let s  = Shim.set_state  1 (Shim.uint8_crval 4)
             (Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid)) in
  let s' = Shim.run_program (get_program pid) s in
  let h1_ok = Shim.crval_to_int (Shim.get_header 1 s') = 7 in
  let s1_ok = Shim.crval_to_int (Shim.get_state  1 s') = 4 in
  if h1_ok && s1_ok then 1 else 0)

(* Test 20: Multi-rule, first rule does not match, second does
 * Rule 1: h1=5 → h1 += 1. Rule 2: h1=10 → h1 += 100.
 * With h1 = 10: only rule 2 fires → h1 = 110. *)
let () = register_semantics "multi_rule_second_matches: h1=10 → h1=110" (fun () ->
  let pid = 16 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 10) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 110 then 1 else 0)

(* Test 21: multi_rule_second_matches — first rule fires
 * Rule 1: h1=5 → h1 += 1. With h1 = 5 the first rule fires; h1 = 6. *)
let () = register_semantics "multi_rule_second_matches: first fires, h1=5 → h1=6" (fun () ->
  let pid = 16 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 6 then 1 else 0)

(* Test 22: multi_rule_second_matches — neither rule matches
 * Patterns require h1 ∈ {5, 10}; with h1 = 3 nothing fires. *)
let () = register_semantics "multi_rule_second_matches: no rule matches, h1=3 unchanged" (fun () ->
  let pid = 16 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 3) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 3 then 1 else 0)

(* Test 23: Cross-header predicate (predicate on h2, write to h1)
 * When h2 = 7: h1 := h1 + 1. With h1 = 5, h2 = 7: h1 = 6, h2 unchanged. *)
let () = register_semantics "cross_header_predicate: h2=7 gates h1+=1" (fun () ->
  let pid = 17 in
  let s  = Shim.set_header 2 (Shim.uint8_crval 7)
             (Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid)) in
  let s' = Shim.run_program (get_program pid) s in
  let h1_ok = Shim.crval_to_int (Shim.get_header 1 s') = 6 in
  let h2_ok = Shim.crval_to_int (Shim.get_header 2 s') = 7 in
  if h1_ok && h2_ok then 1 else 0)

(* Test 24: cross_header_predicate — predicate fails
 * Predicate requires h2 = 7; with h2 = 1, h1 is unchanged. *)
let () = register_semantics "cross_header_predicate: h2=1 → h1 unchanged" (fun () ->
  let pid = 17 in
  let s  = Shim.set_header 2 (Shim.uint8_crval 1)
             (Shim.set_header 1 (Shim.uint8_crval 5) (init_state pid)) in
  let s' = Shim.run_program (get_program pid) s in
  let h1_ok = Shim.crval_to_int (Shim.get_header 1 s') = 5 in
  let h2_ok = Shim.crval_to_int (Shim.get_header 2 s') = 1 in
  if h1_ok && h2_ok then 1 else 0)

(* Test 25: Empty transformer leaves state unchanged
 * No rules; h1 = 42 stays 42. *)
let () = register_semantics "empty_transformer: h1=42 unchanged" (fun () ->
  let pid = 18 in
  let s  = Shim.set_header 1 (Shim.uint8_crval 42) (init_state pid) in
  let s' = Shim.run_program (get_program pid) s in
  if Shim.crval_to_int (Shim.get_header 1 s') = 42 then 1 else 0)
