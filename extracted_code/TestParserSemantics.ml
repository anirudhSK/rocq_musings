let parsers = Shim.listify_coq_list TestParserPrograms.parser_test_programs
let get_parser = Stdlib.List.nth parsers
let run pid bytes = Shim.run_parser (get_parser pid) bytes

(* p_extract8 (0): a single byte read into h1. *)
let%expect_test "extract8: 0xAB -> h1=171" =
  Shim.print_parser_result (run 0 [0xAB]);
  [%expect {| h1=171 |}]

(* Packet shorter than the field: extraction runs past the end -> parse fails. *)
let%expect_test "extract8: empty packet -> Reject" =
  Shim.print_parser_result (run 0 []);
  [%expect {| Reject |}]

(* p_extract_two (1): two sequential bytes into h1, h2. *)
let%expect_test "extract_two: [0x12;0x34] -> h1=18, h2=52" =
  Shim.print_parser_result (run 1 [0x12; 0x34]);
  [%expect {| h1=18, h2=52 |}]

(* p_select_extract (2): h1=1 fires the second extraction. *)
let%expect_test "select: h1=1 extracts h2" =
  Shim.print_parser_result (run 2 [1; 99]);
  [%expect {| h1=1, h2=99 |}]

(* p_select_extract (2): h1<>1 takes the default (Accept), h2 untouched. *)
let%expect_test "select: h1<>1 skips h2" =
  Shim.print_parser_result (run 2 [2; 99]);
  [%expect {| h1=2 |}]

(* p_loop (3): consume header bytes until a 0 terminator (state revisited
   three times here), then one payload byte into h2. Needs the looping fuel. *)
let%expect_test "loop: [5;3;0;42] -> h1=0, h2=42" =
  Shim.print_parser_result (run 3 [5; 3; 0; 42]);
  [%expect {| h1=0, h2=42 |}]

(* p_reject (4): h1=255 takes the Reject transition. *)
let%expect_test "reject: h1=255 -> Reject" =
  Shim.print_parser_result (run 4 [255]);
  [%expect {| Reject |}]

(* p_reject (4): any other value Accepts. *)
let%expect_test "reject: h1=7 -> Accept" =
  Shim.print_parser_result (run 4 [7]);
  [%expect {| h1=7 |}]
