From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

(* Tell Coq to use your external implementation *)
Extract Constant smt_query => "Smt_solver.solve_smt_bool_expr".

Extraction "imp1.ml" SmtQuery.equivalence_checker_cr_dsl.