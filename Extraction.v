From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.
From MyProject Require Import Integers.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "Z3Solver.solve".

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction CrDsl.CaracaraProgram Integers.repr SmtQuery.equivalence_checker_cr_dsl SmtTypes.SmtResult.
