From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "Z3Solver.solve expr".

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction SmtQuery.equivalence_checker_cr_dsl.
