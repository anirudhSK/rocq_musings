From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "MyZ3.solve". (* TODO: Implement MyZ3.solve *)

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction SmtQuery.equivalence_checker_cr_dsl.