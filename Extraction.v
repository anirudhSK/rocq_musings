From Stdlib Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.
From MyProject Require Import SmtModuleQuery.

From MyProject Require Import TestPrograms.
From MyProject Require Import TestModulePrograms.
From MyProject Require Import TestParserPrograms.
From MyProject Require Import PktClass.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrDslProperties.

(* Tell extraction to use your external OCaml implementation *)
Extract Constant smt_query => "Z3Solver.solve".

Set Extraction Output Directory "extracted_code".

(* Extract everything else normally *)
Separate Extraction
  CrDsl.CaracaraProgram Integers.repr SmtQuery.equivalence_checker_cr_dsl SmtTypes.SmtResult
  CrSymbolicSemanticsTransformer.eval_sym_state
  CrConcreteSemanticsTransformer.eval_cr_program_concrete
  CrVarLike.program_state_mapper CrVarLike.init_concrete_transformer_state
  test_programs parser_test_programs
  TestModulePrograms.lookup_mod_test_program
  TestModulePrograms.mod_test_program_names
  CrConcreteSemanticsParser.eval_parser_concrete
  CrVarLike.init_general_concrete_state
  CrConcreteSemanticsModule.eval_general_program_concrete
  PktClass.ex_lin_prog PktClass.ex_tss_prog
  PktClass.ex_lin_overlap PktClass.ex_tss_overlap
  PktClass.ex_lin_distinct PktClass.ex_tss_distinct
  modnet_equivalence_checker
  (* [Z3Solver] needs the declared length of a region to emit the same bounds
     guard the concrete [ld_arr] applies. *)
  SmtExpr.smt_arr_len
  well_formed_programb well_formed_general_programb

   sai_dump_headers parserhawk_sai_spec.
