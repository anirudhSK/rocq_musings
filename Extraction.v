From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "fun expr -> match expr with | _ ->
                               SmtUnknown
                               let y = let open Z3Example in Z3Example.example_1".

(* Extract everything else normally *)
Extraction "EquivalenceChecker.ml" SmtQuery.equivalence_checker_cr_dsl.