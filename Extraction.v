From Stdlib Require Extraction.
Extraction Language OCaml.

From MyProject Require Import SmtQuery.
From MyProject Require Import SmtCompile.
From MyProject Require Import ParserWellFormed.
From MyProject Require Import SmtModuleQuery.

From MyProject Require Import TestPrograms.
From MyProject Require Import TestModulePrograms.
From MyProject Require Import TestParserPrograms.
From MyProject Require Import PktClass.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrDslProperties.
From MyProject Require Import ParserHawkEval.

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
  (* The query compiler.  [Z3Solver.solve] runs [compile_bool] before lowering,
     so the lowering only ever sees the core fragment and can stay a structural
     transliteration; [lcb] is the well-formedness [compile_bool_correct]
     assumes, checked at run time rather than trusted. *)
  SmtCompile.compile_bool SmtCompile.lcb
  (* The one-layer steps, so [Z3Solver] can tie the recursive knot with a
     memo table -- a pure Rocq [Fixpoint] re-traverses a shared subterm once
     per path through the DAG, which does not terminate on a real query. *)
  SmtCompile.cstep_bool SmtCompile.cstep_arith SmtCompile.cstep_arr
  SmtCompile.lcstep_bool SmtCompile.lcstep_arith SmtCompile.lcstep_arr
  SmtCompile.compile_query SmtCompile.regions_wf
  well_formed_programb well_formed_general_programb
  (* [run_parser] checks a lowered parser against the IR's own conditions. *)
  ParserWellFormed.well_formed_parserb

  dump_headers icmp_spec eth_spec mfk_spec sai_spec.
