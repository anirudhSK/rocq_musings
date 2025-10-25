open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> Interface.coq_CaracaraProgram_of_sexp

let programs = [|
  get_program "./test/prog1.out";
  get_program "./test/prog2.out"
|]

let test_1 () =
  (* reflexive comparison of extremely basic program *)
  let p = programs.(0) in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0

let test_2 () =
  (* compares two basic programs with different header values *)
  let p1 = programs.(0) in
  let p2 = programs.(1) in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0

let () =
  let tests = [
    test_1; test_2
  ] in
  
  let n_passed = Stdlib.List.fold_left
    (fun (acc : int) test ->
      let passed = test () in
      acc + passed) 0 tests in
  
  let n_tests = Stdlib.List.length tests in
  Printf.printf "Passed %d/%d tests\n" n_passed n_tests;

  if n_passed <> n_tests then exit 1
