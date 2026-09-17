(* Run a bare [CrParser.Parser] s-expression on a packet, or check its
   well-formedness.  The oracle for [translation/parserhawk/test_lower_table.py]:
   that harness lowers a generated pipeline and then asks THIS to say what the
   IR actually does with the result, rather than trusting the lowering's own
   account of it.

   Packets are given as a BIT string, not bytes.  Byte granularity would be
   useless here: the thing most worth testing is what happens at a cursor where
   an extraction no longer fits, and a 17-bit parser handed 3 bytes has 24 bits,
   so the interesting case never arises.

     run_parser --wf FILE            -> "wellformed" | "malformed"
     run_parser FILE 0101...         -> "h1=7, h2=42" | "Reject" | "Incomplete"
*)

let load f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexplib.Sexp.of_string |> CrTypeIF.CrParser.coq_Parser_of_sexp

let bits_of_string s =
  Shim.coq_list_of_list
    (Stdlib.List.init (Stdlib.String.length s) (fun i ->
       match Stdlib.String.get s i with
       | '1' -> Datatypes.Coq_true
       | '0' -> Datatypes.Coq_false
       | c -> failwith (Printf.sprintf "packet bit %d is %C, not 0 or 1" i c)))

let usage () =
  prerr_endline "usage: run_parser [--wf] <parser.ir> [<packet bits, e.g. 01011>]";
  exit 1

let () =
  match Stdlib.List.tl (Array.to_list Sys.argv) with
  | ["--wf"; f] ->
      print_endline
        (match ParserWellFormed.well_formed_parserb (load f) with
         | Datatypes.Coq_true -> "wellformed"
         | Datatypes.Coq_false -> "malformed")
  | [f; bits] ->
      Shim.print_parser_result
        (CrConcreteSemanticsParser.eval_parser_concrete (load f)
           (Shim.mk_parser_state (bits_of_string bits)))
  | [f] ->
      Shim.print_parser_result
        (CrConcreteSemanticsParser.eval_parser_concrete (load f)
           (Shim.mk_parser_state (bits_of_string "")))
  | _ -> usage ()
