From Coq Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

Extraction "imp1.ml" SmtQuery.equivalence_checker_cr_dsl.