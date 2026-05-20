From Stdlib Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.

From MyProject Require Import CrMem.
From MyProject Require Import CrMemEx.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "Z3Solver.solve".
Extract Constant z3_query => "MemSolver.mem_solve".

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction
  CrMem.query_expression CrMem.Z3Res
  CrMemEx.example_programs
  CrDsl.CaracaraProgram Integers.repr SmtQuery.equivalence_checker_cr_dsl SmtTypes.SmtResult
  CrSymbolicSemanticsTransformer.eval_sym_state
  CrConcreteSemanticsTransformer.eval_cr_program_concrete
  CrVarLike.program_state_mapper CrVarLike.init_concrete_state.
