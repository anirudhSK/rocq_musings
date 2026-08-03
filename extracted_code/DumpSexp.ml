open Sexplib

let print_sexp s =
  print_endline (Sexp.to_string_hum s);
  print_endline ""

(* --pkt path: a sexp dump of CrModule.coq_GeneralCaracaraProgram examples
   from PktClass.  At the moment there is only one example (ex_lin_prog at
   index 0); future indices can be added as new examples appear. *)

let pkt_examples : CrTypeIF.CrModule.coq_GeneralCaracaraProgram list =
  [ PktClass.ex_lin_prog ; PktClass.ex_tss_prog ]

(* --parser path: a sexp dump of the standalone CrParser.coq_Parser examples,
   in the order [TestParserPrograms.parser_test_programs] declares them (which
   is also the order TestParserSemantics indexes them by). *)

let parser_examples : CrTypeIF.CrParser.coq_Parser list =
  Shim.listify_coq_list TestParserPrograms.parser_test_programs

let usage () =
  prerr_endline
    "usage: dump_sexp (--pkt | --parser) [idx]\n\
    \       dump_sexp --modprog NAME";
  exit 1

let dump sexp_of examples rest_args =
  let print p = print_sexp (sexp_of p) in
  match rest_args with
  | [] -> Stdlib.List.iter print examples
  | [s] ->
    (match Stdlib.Option.bind (int_of_string_opt s) (Stdlib.List.nth_opt examples) with
     | None -> prerr_endline "invalid idx"; exit 1
     | Some p -> print p)
  | _ -> usage ()

let () =
  (* Skip Sys.argv.(0) (program name) and dispatch on subcommand flag.
     Note: the extracted `List` module shadows Stdlib's; use Stdlib.List. *)
  let args = Stdlib.List.tl (Array.to_list Sys.argv) in
  match args with
  | "--pkt" :: rest ->
    dump CrTypeIF.CrModule.sexp_of_coq_GeneralCaracaraProgram pkt_examples rest
  | "--parser" :: rest ->
    dump CrTypeIF.CrParser.sexp_of_coq_Parser parser_examples rest
  | ["--modprog"; name] ->
    print_sexp
      (CrTypeIF.CrModule.sexp_of_coq_GeneralCaracaraProgram (Shim.find_modprog name))
  | _ -> usage ()
