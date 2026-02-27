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

(* Test 1:
 * A program should be equal to itself
 *)
let () = register "refl_0" (fun () ->
  let p = get_program "./test/prog1.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p p in
  match res with
  | Equivalent -> 1
  | _ -> 0)

(* Test 2:
 * Different values get statically assigned to header variable
 * p1: x=5
 * p2: x=1
 *)
let () = register "hdr_diff" (fun () ->
  let p1 = get_program "./test/prog1.out" in
  let p2 = get_program "./test/prog2.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

(* Test 3:
 * -1 and +254 should be the same under 8-bit 2s complement
 * p1: x-1
 * p2: x+254
 *)
let () = register "sub_1comp" (fun () ->
  let p1 = get_program "./test/subtract1.out" in
  let p2 = get_program "./test/subtract2.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

(* Test 4:
 * In essence, we're testing that addition is commutative
 * p1: x - 1 + 2
 * p2: x + 2 - 1
 *)
let () = register "complex_add/sub equal" (fun () ->
  let p1 = get_program "./test/complex1a.out" in
  let p2 = get_program "./test/complex1b.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
   match res with
  | Equivalent -> 1
  | _ -> 0)

(* Test 5:
 * Trivially non-equivalent
 * p1: x + 2 - 1
 * p2: x - 1
 *)
let () = register "complex_add/sub NOT equal" (fun () ->
  let p1 = get_program "./test/complex1b.out" in
  let p2 = get_program "./test/subtract1.out" in

  let res = SmtQuery.equivalence_checker_cr_dsl p1 p2 in
  match res with
  | NotEquivalent _ -> 1
  | _ -> 0)

(* Test 6:
 * Address offsets should alias
 * p1: *(x+4)
 * p2: *(x+2+2)
 *)
let () = register "basic address alias" (fun () ->
  let p1 = get_mem_program "./test/mem1a.out" in
  let p2 = get_mem_program "./test/mem1b.out" in

  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Unsat -> 1
  | _ -> 0)

(* Test 7:
 * writing a variable value will not always be the same as writing a constant value
 * p1: *(x+4) = y
 * p2: *(x+4) = 1
 *)
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

(* Test 8:
 * Programs can have different segfault behavior
 * p1: ret *(x+0)
 * p2: *(x+1); ret *(x+0)
 *)
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

(* Test 9:
 * Access extents are the same, and output variables are same
 * p1: *(x+1); ret *(x+0)
 * p2: *(x+1)=0; ret *(x+0)
 *)
let () = register "mem nop are equiv" (fun () ->
  let p1 = get_mem_program "./test/mem2b.out" in
  let p2 = get_mem_program "./test/mem2c.out" in
  
  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Unsat -> 1
  | _ -> 0)

(* Test 10:
 * If statement collapses
 * p1: if (0 == 0) then A else B
 * p2: A
 *)
let () = register "degenerate branch" (fun () ->
  let p1 = get_mem_program "./test/mem3a.out" in
  let p2 = get_mem_program "./test/mem3b.out" in
  
  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Unsat -> 1
  | _ -> 0)

(* Test 11:
 * Array values might be different
 * p1: *(x+1); ret *(x+0)
 * p2: *(x+0); ret *(x+1)
 *)
let () = register "sat aval" (fun () ->
  let p1 = get_mem_program "./test/mem4a.out" in
  let p2 = get_mem_program "./test/mem4b.out" in
  
  let res = MemSolver.mem_solve p1 p2 in
  match res with
  | Z3Sat (_, _, f) -> (
    match f with
    | ValueMismatch -> 1
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
