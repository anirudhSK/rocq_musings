open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp

let get_mem_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> CrTypeIF.CrMem.coq_IM_Program_of_sexp

let tests = ref []
let register test_label test_fn =
  tests := (test_label, test_fn) :: !tests

let () = register "refl_0" (fun () ->
  let p = get_program "./test/prog1.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "hdr_diff" (fun () ->
  let p1 = get_program "./test/prog1.out" in
  let p2 = get_program "./test/prog2.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

let () = register "refl_1" (fun () ->
  let p = get_program "./test/subtract1.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "sub_1comp" (fun () ->
  let p1 = get_program "./test/subtract1.out" in
  let p2 = get_program "./test/subtract2.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "complex_add/sub equal" (fun () ->
  let p1 = get_program "./test/complex1a.out" in
  let p2 = get_program "./test/complex1b.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

let () = register "complex_add/sub NOT equal" (fun () ->
  let p1 = get_program "./test/complex1b.out" in
  let p2 = get_program "./test/subtract1.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

let () = register "basic address alias" (fun () ->
  let p1 = get_mem_program "./test/mem1a.out" in
  let p2 = get_mem_program "./test/mem1b.out" in

  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Unsat -> 1
  | _ -> 0)

let () = register "basic memory overwrite" (fun () ->
  let p1 = get_mem_program "./test/mem1a.out" in
  let p2 = get_mem_program "./test/mem1c.out" in
  
  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Sat (_, _, f) -> (
    match f with
    | ValueMismatch -> 1
    | _ -> 0
    )
  | _ -> 0)

let () = register "divergent load extents" (fun () ->
  let p1 = get_mem_program "./test/mem2a.out" in
  let p2 = get_mem_program "./test/mem2b.out" in
  
  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Sat (_, _, f) -> (
    match f with
    | BoundsMismatch -> 1
    | _ -> 0
    )
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
