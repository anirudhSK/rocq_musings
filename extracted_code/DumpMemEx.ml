open Sexplib
open CrTypeIF.CrMem

let rec print_programs pl =
  match pl with
  | Datatypes.Coq_nil -> print_endline("")
  | Datatypes.Coq_cons (p, rest) ->
    let s = sexp_of_coq_IM_Program p in
    print_endline(Sexp.to_string_hum s);
    print_endline("");
    print_programs rest

let rec nth l n =
  match l with
  | Datatypes.Coq_nil -> (
    prerr_endline "invalid idx";
    exit 1)
  | Datatypes.Coq_cons (p, rest) ->
    if n <> 0 then
      nth rest (n - 1)
    else
      let s = sexp_of_coq_IM_Program p in
      print_endline(Sexp.to_string_hum s);
      print_endline("")
let () =
  let programs = CrMemEx.example_programs in
  
  if Array.length Sys.argv = 2 then (
    let idx = int_of_string Sys.argv.(1) in
    nth programs idx
  ) else (
    print_programs programs
  )
