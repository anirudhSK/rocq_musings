open BinNums
open CrDsl
open CrIdentifiers
open CrTransformer
open Datatypes
open First_generated

(** val headers_to_check : coq_Header list **)

let headers_to_check =
  Coq_cons ((Coq_xI (Coq_xI Coq_xH)), Coq_nil)

(** val state_vars_to_check : coq_State list **)

let state_vars_to_check =
  Coq_nil

(** val ctrl_stmts_to_check : coq_Ctrl list **)

let ctrl_stmts_to_check =
  Coq_nil

(** val transformer_first : coq_Transformer **)

let transformer_first =
  Coq_cons (the_table_0_rule, Coq_nil)

(** val example_program_1 : coq_CaracaraProgram **)

let example_program_1 =
  CaracaraProgramDef (headers_to_check, state_vars_to_check,
    ctrl_stmts_to_check, transformer_first)

