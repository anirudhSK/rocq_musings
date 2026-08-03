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

(* ------------------------------------------------------------------ *)
(* Sexp encoding.  These are what [dump_sexp --parser] prints.         *)

let sexp_of_parser p = CrTypeIF.CrParser.sexp_of_coq_Parser p
let print_parser_sexp p = print_endline (Sexplib.Sexp.to_string_hum (sexp_of_parser p))

(* p_select_nibble (5): [sc_pattern] is a [list bool], and it prints as the
   binary literal it denotes rather than as a [Coq_cons] chain.  MSB-first, so
   the four digits of [0b0011] read in list order; the leading zeros are the
   pattern's own, not padding this converter added. *)
let%expect_test "sexp: a select pattern prints as a 0b literal" =
  print_parser_sexp (get_parser 5);
  [%expect {|
    ((parser_start 1)
     (parser_states
      (Coq_cons
       ((psd_label 1) (psd_action (Some (ExtractOpConstructor 1 8 W64)))
        (psd_trans
         (Select
          (Coq_cons
           ((sc_header 1) (sc_start_index 4) (sc_end_index 8) (sc_pattern 0b0011)
            (sc_target (TargetState 2)))
           Coq_nil)
          Accept)))
       (Coq_cons
        ((psd_label 2) (psd_action (Some (ExtractOpConstructor 2 8 W64)))
         (psd_trans (Unconditional Accept)))
        Coq_nil))))
    |}]

(* An 8-bit pattern keeps all eight digits (p_select_extract, whose case is
   [pat_1]), so a dump is faithful rather than normalising -- [0b00000001] and
   [0b1] denote the same thing to [select_case_matches_concrete], but only one
   of them is what the program says. *)
let%expect_test "sexp: leading zeros of a pattern survive the dump" =
  print_parser_sexp (get_parser 2);
  [%expect {|
    ((parser_start 1)
     (parser_states
      (Coq_cons
       ((psd_label 1) (psd_action (Some (ExtractOpConstructor 1 8 W64)))
        (psd_trans
         (Select
          (Coq_cons
           ((sc_header 1) (sc_start_index 0) (sc_end_index 8)
            (sc_pattern 0b00000001) (sc_target (TargetState 2)))
           Coq_nil)
          Accept)))
       (Coq_cons
        ((psd_label 2) (psd_action (Some (ExtractOpConstructor 2 8 W64)))
         (psd_trans (Unconditional Accept)))
        Coq_nil))))
    |}]

(* Every parser in the registry survives sexp -> parser -> sexp. *)
let%expect_test "sexp: every parser round-trips" =
  Stdlib.List.iteri
    (fun i p ->
       let s = sexp_of_parser p in
       let s' = sexp_of_parser (CrTypeIF.CrParser.coq_Parser_of_sexp s) in
       Printf.printf "parser %d: %s\n" i
         (if Sexplib.Sexp.compare s s' = 0 then "ok" else "MISMATCH"))
    parsers;
  [%expect {|
    parser 0: ok
    parser 1: ok
    parser 2: ok
    parser 3: ok
    parser 4: ok
    parser 5: ok
    |}]

(* The [0b] form is emitted, but the derived constructor chain is still
   accepted, so a dump taken before the sugar existed still loads.  Both
   spellings of [pat_nib3] must give the same parser. *)
let%expect_test "sexp: the derived Coq_cons form still loads" =
  let case pattern =
    Printf.sprintf
      "((parser_start 1) (parser_states (Coq_cons \
       ((psd_label 1) (psd_action (Some (ExtractOpConstructor 1 8 W64))) \
       (psd_trans (Select (Coq_cons ((sc_header 1) (sc_start_index 4) \
       (sc_end_index 8) (sc_pattern %s) (sc_target Accept)) Coq_nil) Reject))) \
       Coq_nil)))" pattern in
  let load s =
    sexp_of_parser
      (CrTypeIF.CrParser.coq_Parser_of_sexp (Sexplib.Sexp.of_string (case s))) in
  let sugar = load "0b0011" in
  let derived =
    load "(Coq_cons Coq_false (Coq_cons Coq_false \
          (Coq_cons Coq_true (Coq_cons Coq_true Coq_nil))))" in
  print_endline (if Sexplib.Sexp.compare sugar derived = 0 then "same" else "DIFFERENT");
  print_endline (Sexplib.Sexp.to_string_hum sugar);
  [%expect {|
    same
    ((parser_start 1)
     (parser_states
      (Coq_cons
       ((psd_label 1) (psd_action (Some (ExtractOpConstructor 1 8 W64)))
        (psd_trans
         (Select
          (Coq_cons
           ((sc_header 1) (sc_start_index 4) (sc_end_index 8) (sc_pattern 0b0011)
            (sc_target Accept))
           Coq_nil)
          Reject)))
       Coq_nil)))
    |}]

(* A literal that is not bits is a clean sexp error, not a silent misparse into
   some other pattern. *)
let%expect_test "sexp: a 0b literal takes only 0 and 1" =
  (try
     ignore (CrTypeIF.CrParser.bits_of_sexp (Sexplib.Sexp.of_string "0b0121"))
   with Sexplib.Conv.Of_sexp_error (e, _) -> print_endline (Printexc.to_string e));
  [%expect {| Failure("CrTypeIF.bits_of_sexp: a 0b literal takes only the digits 0 and 1") |}]

(* The empty pattern is [0b] with no digits, and it round-trips. *)
let%expect_test "sexp: the empty pattern is 0b" =
  let empty = Datatypes.Coq_nil in
  let s = CrTypeIF.CrParser.sexp_of_bits empty in
  print_endline (Sexplib.Sexp.to_string_hum s);
  print_endline
    (match CrTypeIF.CrParser.bits_of_sexp s with
     | Datatypes.Coq_nil -> "round-trips to the empty list"
     | Datatypes.Coq_cons _ -> "NOT EMPTY");
  [%expect {|
    0b
    round-trips to the empty list
    |}]
