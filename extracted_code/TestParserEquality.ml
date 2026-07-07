(* Parser-vs-parser equivalence checks.  Parsers are drawn from
   TestParserPrograms: 0 = p_extract8 (one byte -> h1), 1 = p_extract_two
   (two bytes -> h1, h2), 4 = p_reject (byte -> h1, reject iff h1 = 255). *)
let parsers = Shim.listify_coq_list TestParserPrograms.parser_test_programs
let get_parser = Stdlib.List.nth parsers

let print_equiv = function
  | SmtQuery.Equivalent -> print_endline "Equivalent"
  | SmtQuery.NotEquivalent _ -> print_endline "NotEquivalent"
  | SmtQuery.NotEquivalentUnknown -> print_endline "NotEquivalentUnknown"
  | SmtQuery.NotEquivalentVariablesDiffer -> print_endline "NotEquivalentVariablesDiffer"

let check headers packet_len p1 p2 =
  SmtParserQuery.parser_equivalence_checker
    (Shim.headers_of_ints headers) (Shim.int_to_coq_nat packet_len)
    (get_parser p1) (get_parser p2)

(* A parser is equivalent to itself. *)
let%expect_test "reflexive: p_extract8 vs p_extract8 over h1" =
  print_equiv (check [1] 8 0 0);
  [%expect {| Equivalent |}]

(* Accept/reject differs: p_extract8 always accepts, p_reject rejects the
   packet 0xFF.  This is the case a header-only checker would miss. *)
let%expect_test "accept differs: p_extract8 vs p_reject on 0xFF" =
  print_equiv (check [1] 8 0 4);
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

(* Projecting onto h1 only: p_extract_two assigns h1 the same first byte as
   p_extract8, and its extra h2 extraction is irrelevant when h2 is not in the
   interface.  (16-bit packet so p_extract_two's second read succeeds.) *)
let%expect_test "h1 projection: p_extract8 vs p_extract_two over h1 (16-bit)" =
  print_equiv (check [1] 16 0 1);
  [%expect {| Equivalent |}]

(* Same two parsers but comparing h2 as well: p_extract8 leaves h2 at its
   (symbolic) initial value while p_extract_two overwrites it -> not equivalent. *)
let%expect_test "h2 differs: p_extract8 vs p_extract_two over h1,h2 (16-bit)" =
  print_equiv (check [1; 2] 16 0 1);
  [%expect {|
    ┌ SAT Valuation
    | var( hdr_10 ) : u64 := 18446744073709551615
    | var( pkt_1 ) : u64 := 0
    | var( pkt_10 ) : u64 := 0
    | var( pkt_100 ) : u64 := 0
    | var( pkt_1000 ) : u64 := 0
    | var( pkt_10000 ) : u64 := 0
    | var( pkt_1001 ) : u64 := 0
    | var( pkt_101 ) : u64 := 0
    | var( pkt_1010 ) : u64 := 0
    | var( pkt_1011 ) : u64 := 0
    | var( pkt_11 ) : u64 := 0
    | var( pkt_110 ) : u64 := 0
    | var( pkt_1100 ) : u64 := 0
    | var( pkt_1101 ) : u64 := 0
    | var( pkt_111 ) : u64 := 0
    | var( pkt_1110 ) : u64 := 0
    | var( pkt_1111 ) : u64 := 0
    └
    NotEquivalent
    |}]
