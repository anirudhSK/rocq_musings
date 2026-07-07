From Stdlib Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.
From MyProject Require Import SmtModuleQuery.
From MyProject Require Import SmtParserQuery.

From MyProject Require Import CrMem.
From MyProject Require Import CrMemEx.
From MyProject Require Import TestPrograms.
From MyProject Require Import TestModulePrograms.
From MyProject Require Import TestParserPrograms.
From MyProject Require Import PktClass.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrDslProperties.

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
  CrVarLike.program_state_mapper CrVarLike.init_concrete_transformer_state
  test_programs mod_test_programs parser_test_programs
  CrConcreteSemanticsParser.eval_parser_concrete
  CrVarLike.init_general_concrete_state
  CrConcreteSemanticsModule.eval_general_program_concrete_sinks
  PktClass.ex_lin_prog PktClass.ex_tss_prog modnet_equivalence_checker
  SmtParserQuery.parser_equivalence_checker
  well_formed_programb well_formed_general_programb.
