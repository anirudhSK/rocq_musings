open Sexplib

let print_sexp s =
  print_endline (Sexp.to_string_hum s);
  print_endline ""

(* --pkt path: a sexp dump of CrModule.coq_GeneralCaracaraProgram examples
   from PktClass.  At the moment there is only one example (ex_lin_prog at
   index 0); future indices can be added as new examples appear. *)

let pkt_examples : CrTypeIF.CrModule.coq_GeneralCaracaraProgram list =
  [ PktClass.ex_lin_prog ; PktClass.ex_tss_prog ]

let nth_pkt n =
  match Stdlib.List.nth_opt pkt_examples n with
  | None ->
    prerr_endline "invalid idx";
    exit 1
  | Some p ->
    print_sexp (CrTypeIF.CrModule.sexp_of_coq_GeneralCaracaraProgram p)

let print_pkt_programs () =
  Stdlib.List.iter
    (fun p -> print_sexp (CrTypeIF.CrModule.sexp_of_coq_GeneralCaracaraProgram p))
    pkt_examples

let usage () =
  prerr_endline "usage: dump_sexp --pkt [idx]";
  exit 1

let dump_pkt rest_args =
  match rest_args with
  | [] -> print_pkt_programs ()
  | [s] -> nth_pkt (int_of_string s)
  | _ -> usage ()

let () =
  (* Skip Sys.argv.(0) (program name) and dispatch on subcommand flag.
     Note: the extracted `List` module shadows Stdlib's; use Stdlib.List. *)
  let args = Stdlib.List.tl (Array.to_list Sys.argv) in
  match args with
  | "--pkt" :: rest -> dump_pkt rest
  | _ -> usage ()
