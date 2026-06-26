let mod_programs = Shim.listify_coq_list TestModulePrograms.mod_test_programs
let get_mod_program = Stdlib.List.nth mod_programs
let run pid setup =
  let p  = get_mod_program pid in
  Shim.print_malformed_gprog p pid;
  let gcs0 = CrVarLike.init_general_concrete_state p in
  let sid = Shim.start_mod_id p in
  let gcs = Shim.set_mod_state sid
    (setup (Shim.get_mod_state sid gcs0)) gcs0 in
  match CrModConcreteSemantics.eval_general_program_concrete p gcs with
  | None -> failwith "eval_general_program_concrete_sinks returned None"
  | Some sinks -> sinks

(* ------------------------------------------------------------------ *)
(* mod_prog_single_add3 (pid 0): one module, h1 := h1 + 3            *)
(* ------------------------------------------------------------------ *)

let%expect_test "single_add3: h1=5 → h1=8" =
  let s' = run 0 (Shim.set_header_to_int 1 5) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=8
  |}]

let%expect_test "single_add3: h1=0 → h1=3" =
  let s' = run 0 (Shim.set_header_to_int 1 0) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=3
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_add1_then_mul2 (pid 1): h1 → (h1+1)*2                    *)
(* ------------------------------------------------------------------ *)

let%expect_test "add1_then_mul2: h1=5 → 12" =
  let s' = run 1 (Shim.set_header_to_int 1 5) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=6
    Module 2:
      h1=12
  |}]

let%expect_test "add1_then_mul2: h1=0 → 2 (0+1)*2" =
  let s' = run 1 (Shim.set_header_to_int 1 0) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=1
    Module 2:
      h1=2
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_conditional_pipeline (pid 2)                              *)
(*   Module 1: h1=7 → h1:=1, else no-op.  Module 1: h1 := h1+10.    *)
(* ------------------------------------------------------------------ *)

let%expect_test "conditional_pipeline: h1=7 hits guard → 11" =
  let s' = run 2 (Shim.set_header_to_int 1 7) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=1
    Module 2:
      h1=11
  |}]

let%expect_test "conditional_pipeline: h1=3 misses guard → 13" =
  let s' = run 2 (Shim.set_header_to_int 1 3) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=3
    Module 2:
      h1=13
  |}]

(* ------------------------------------------------------------------ *)
(* mod_prog_cmplt_matchheader (pid 3)                                 *)
(*   Module 1: h1<h2 → h1:=h1+h2.  Module 1: h1 := h1+1.            *)
(* ------------------------------------------------------------------ *)

let%expect_test "cmplt_matchheader: h1=3 h2=5 fires → h1=9" =
  let s' = run 3 (fun s ->
    Shim.set_header_to_int 2 5
      (Shim.set_header_to_int 1 3 s)) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=8, h2=5
    Module 2:
      h1=9, h2=5
  |}]

let%expect_test "cmplt_matchheader: h1=5 h2=3 no match → h1=6" =
  let s' = run 3 (fun s ->
    Shim.set_header_to_int 2 3
      (Shim.set_header_to_int 1 5 s)) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=5, h2=3
    Module 2:
      h1=6, h2=3
  |}]

let%expect_test "cmplt_matchheader: h1=h2=4 equal, no match → h1=5" =
  let s' = run 3 (fun s ->
    Shim.set_header_to_int 2 4
      (Shim.set_header_to_int 1 4 s)) in
  Shim.print_general_state s';
  [%expect {|
    Module 1:
      h1=4, h2=4
    Module 2:
      h1=5, h2=4
  |}]
