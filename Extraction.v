From Stdlib Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.
From MyProject Require Import SmtModuleQuery.
From MyProject Require Import Integers.

From MyProject Require Import CrVal.
From MyProject Require Import CrMem.
From MyProject Require Import CrMemEx.
From MyProject Require Import PktClass.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "Z3Solver.solve".
Extract Constant z3_query => "MemSolver.mem_solve".

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction
  CrMem.query_expression CrMem.Z3Res
  CrMemEx.example_programs
  CrDsl.CaracaraProgram Integers.repr SmtQuery.equivalence_checker_cr_dsl SmtTypes.SmtResult
  PktClass.ex_lin_prog PktClass.ex_tss_prog modnet_equivalence_checker.
