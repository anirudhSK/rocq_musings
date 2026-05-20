open Sexplib

let get_program f =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexp.of_string |> CrTypeIF.coq_CaracaraProgram_of_sexp

let semantics_tests = ref []
let register_semantics test_label test_fn =
  semantics_tests := (test_label, test_fn) :: !semantics_tests

(* Sematics Test 1:
 * subtract1 should subtract 2 from Header[1]
 * tests that Header[1] = 3 -> Header[1]' = 1
 *)
let () = register_semantics "write to program state" (fun () ->
  let p = get_program "./test/subtract1.out" in
  let s = CrVarLike.init_concrete_state p in
  let s' = Shim.set_header 1 (Shim.uint8_crval 3) s in
  let h2' = Shim.crval_to_int (Shim.get_header 1 s') in
  let s'' = Shim.run_program p s' in
  let h3' = Shim.crval_to_int (Shim.get_header 1 s'') in
  if (h2' == 3) && (h3' == 1) then 1 else 0)
