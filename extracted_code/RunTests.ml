open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> Interface.coq_CaracaraProgram_of_sexp

let programs = [|
  get_program "./test/prog1.out";
  get_program "./test/prog2.out";
  get_program "./test/subtract1.out"; (* -2*)
  get_program "./test/subtract2.out";
  get_program "./test/complex1a.out"; (* -1, +2*)
  get_program "./test/complex1b.out"; (* +2, -1*)
  get_program "./test/table1a.out";
  get_program "./test/table1b.out";
  get_program "./test/table1c.out";
|]

let tests = ref []
let register test_label test_fn =
  tests := (test_label, test_fn) :: !tests

let () = register "refl_0" (fun () ->
  let p = programs.(0) in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "hdr_diff" (fun () ->
  let p1 = programs.(0) in
  let p2 = programs.(1) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

let () = register "refl_1" (fun () ->
  let p = programs.(2) in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "sub_1comp" (fun () ->
  let p1 = programs.(2) in
  let p2 = programs.(3) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "complex_add/sub equal" (fun () ->
  let p1 = programs.(4) in
  let p2 = programs.(5) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "complex_add/sub NOT equal" (fun () ->
  let p1 = programs.(5) in
  let p2 = programs.(2) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

  let () = register "table equal" (fun () ->
  let p1 = programs.(6) in
  let p2 = programs.(7) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "table NOT equal" (fun () ->
  let p1 = programs.(7) in
  let p2 = programs.(8) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

let () =
  let test_stats = Stdlib.List.fold_left
    (fun (acc : int * int) (name, test) -> (
      let p, t = acc in
      Printf.printf "Running Test (%s)\n" name;
      let passed = test () in (
      Printf.printf "\027[1m%s\027[0m\n\n" (if passed = 1 then "\027[32mPASSED" else "\027[31mFAILED");
      (p + passed, t + 1)))) (0, 0) (Stdlib.List.rev !tests) in
  
  (Printf.printf "Passed %d/%d tests\n" (fst test_stats) (snd test_stats);

  if ((fst test_stats) <> (snd test_stats)) then exit 1)
