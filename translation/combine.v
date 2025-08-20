From MyProject Require Import first_generated.
From MyProject Require Import second_generated.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrTransformer.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
Require Import ZArith.
Require Import List.
Import ListNotations.
From MyProject Require Import SmtQuery.


(* THE SIMPLEST POSSIBLE ProgramState SmtArithExpr *)
(* We have been operating on stateless only so far so this is a dummy instance to satisfy the compiler.*)
Definition simplest_state : ProgramState SmtArithExpr := {|
  ctrl_map := PMap.init (SmtConst (repr 0%Z));
  header_map := PMap.init (SmtConst (repr 0%Z));
  state_map := PMap.init (SmtConst (repr 0%Z))
|}.

Definition headers_to_check : list Header := [HeaderCtr 1%positive].
Definition state_vars_to_check : list State := [].
Definition ctrl_stmts_to_check : list Ctrl := [].

Definition transformer_first: Transformer := [first_generated.the_table_0_rule].
Definition transformer_second: Transformer := [second_generated.the_table_0_rule].

(* Define concrete example programs *)
Definition example_program_1 : CaracaraProgram :=
  CaracaraProgramDef 
    headers_to_check
    state_vars_to_check  
    ctrl_stmts_to_check
    transformer_first.

Definition example_program_2 : CaracaraProgram :=
  CaracaraProgramDef 
    headers_to_check
    state_vars_to_check
    ctrl_stmts_to_check  
    transformer_second.

(* Construct the equivalence checker instance *)
Definition my_equivalence_check_cr_dsl : bool :=
  equivalence_checker_cr_dsl example_program_1 example_program_2.

Transparent lookup_ctrl.
Transparent update_hdr_map.
Transparent update_state_map.
Transparent update_hdr.
Transparent update_state.
Transparent lookup_hdr. 
Transparent lookup_state.
Transparent lookup_hdr_map.
Transparent lookup_state_map.
Transparent program_state_mapper.
Transparent update_all_hdrs.
Transparent update_all_states.
Transparent HeaderMap.
Transparent StateMap.
Transparent CtrlMap.
Transparent new_pmap_from_old.
Transparent is_header_in_ps.
Transparent is_state_var_in_ps.
Transparent get_all_headers_from_ps.
Transparent get_all_states_from_ps.


Eval compute in my_equivalence_check_cr_dsl.