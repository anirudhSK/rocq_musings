(* Run with:
   dune build
   dune exec test_ppx_deriving_sexp *)
type sorts =
  [%import: Sorts.family]
  [@@deriving sexp]

let () =
  let test = Sorts.InType in
  let sexp = sexp_of_sorts test in
  let orig = sorts_of_sexp sexp in
  assert (orig = test); Printf.printf "Test passed!\n";