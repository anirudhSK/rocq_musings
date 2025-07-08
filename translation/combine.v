From MyProject Require Import first_generated.
From MyProject Require Import second_generated.
From MyProject Require Import SmtExpr.
(* From MyProject Require Import CrProgramState. *)
Require Import ZArith.
Require Import List.
Import ListNotations.
From MyProject Require Import SmtQuery.


(* THE SIMPLEST POSSIBLE ProgramState SmtArithExpr *)
(* We have been operating on stateless only so far so this is a dummy instance to satisfy the compiler.*)
Definition simplest_state : ProgramState SmtArithExpr := {|
ctrl_plane_map := fun _ => SmtConst (repr 0%Z);
header_map := fun _ => SmtConst (repr 0%Z);
state_var_map := fun _ => SmtConst (repr 0%Z)
|}.

Definition headers_to_check : list Header := [first_generated.header_H; second_generated.header_H].
Definition state_vars_to_check : list StateVar := [].
(* Construct the equivalence checker instance *)
Definition my_equivalence_check : SmtResult :=
  equivalence_checker
      simplest_state       (* Starting symbolic state *)
      first_generated.the_table_0_seq_rule          (* First rule *)
      second_generated.the_table_0_seq_rule          (* Second rule (same) *)
      headers_to_check             
      state_vars_to_check.   

Eval compute in my_equivalence_check.