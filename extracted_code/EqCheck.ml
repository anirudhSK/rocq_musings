open Sexplib

let equivalence_check_programs str1 str2 =
  let sexp_1 = Sexp.of_string str1 in
  let sexp_2 = Sexp.of_string str2 in
  let prog_1 = CrTypeIF.coq_CaracaraProgram_of_sexp sexp_1 in
  let prog_2 = CrTypeIF.coq_CaracaraProgram_of_sexp sexp_2 in

  Shim.print_malformed_prog prog_1 1;
  Shim.print_malformed_prog prog_2 2;

  let res = SmtQuery.equivalence_checker_cr_dsl prog_1 prog_2 in
  match res with
  | Equivalent -> print_endline "Equivalent"
  | NotEquivalent _ -> print_endline "Not Equivalent"
  | NotEquivalentUnknown -> print_endline "Not Equivalent (unknown)"
  | NotEquivalentVariablesDiffer -> print_endline "Not Equivalent (variables differ)"

(* Network programs: [GeneralCaracaraProgram]s go through the network checker,
   which compares the emitted packet, the bits read, and every declared memory
   region's contents and access extent. *)
let equivalence_check_networks file_1 file_2 =
  let prog_1 = Shim.load_general_program file_1 in
  let prog_2 = Shim.load_general_program file_2 in

  Shim.print_malformed_gprog prog_1 file_1;
  Shim.print_malformed_gprog prog_2 file_2;

  let res = SmtModuleQuery.modnet_equivalence_checker prog_1 prog_2 in
  match res with
  | Equivalent -> print_endline "Equivalent"
  | NotEquivalent _ -> print_endline "Not Equivalent"
  | NotEquivalentUnknown -> print_endline "Not Equivalent (unknown)"
  | NotEquivalentVariablesDiffer -> print_endline "Not Equivalent (variables differ)"

let load f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str

let usage () =
  prerr_endline "usage: ./bin [--net] <path/to/s/expr/1> <path/to/s/expr/2>";
  prerr_endline "  default: two CaracaraProgram (single-transformer) s-expressions";
  prerr_endline "  --net:   two GeneralCaracaraProgram (module network) s-expressions";
  exit 1

let () =
  match Stdlib.List.tl (Array.to_list Sys.argv) with
  | ["--net"; f1; f2] -> equivalence_check_networks f1 f2
  | [f1; f2] -> equivalence_check_programs (load f1) (load f2)
  | _ -> usage ()
