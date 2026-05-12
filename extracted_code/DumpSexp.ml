open Sexplib

let print_sexp s =
  print_endline (Sexp.to_string_hum s);
  print_endline ""

(* --mem path: a sexp dump of CrMem.coq_IM_Program example_programs. *)

let rec print_mem_programs pl =
  let open CrTypeIF.CrMem in
  match pl with
  | Datatypes.Coq_nil -> print_endline ""
  | Datatypes.Coq_cons (p, rest) ->
    print_sexp (sexp_of_coq_IM_Program p);
    print_mem_programs rest

let rec nth_mem l n =
  let open CrTypeIF.CrMem in
  match l with
  | Datatypes.Coq_nil ->
    prerr_endline "invalid idx";
    exit 1
  | Datatypes.Coq_cons (p, rest) ->
    if n <> 0 then nth_mem rest (n - 1)
    else print_sexp (sexp_of_coq_IM_Program p)

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
  prerr_endline "usage: dump_sexp (--mem | --pkt) [idx]";
  exit 1

let dump_mem rest_args =
  let programs = CrMemEx.example_programs in
  match rest_args with
  | [] -> print_mem_programs programs
  | [s] -> nth_mem programs (int_of_string s)
  | _ -> usage ()

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
  | "--mem" :: rest -> dump_mem rest
  | "--pkt" :: rest -> dump_pkt rest
  | _ -> usage ()
