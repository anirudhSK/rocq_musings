From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "SmtSolver.solve".

(* Extract everything else normally *)
Extraction "EquivalenceChecker.ml" SmtQuery.equivalence_checker_cr_dsl.