From MyProject Require Import SmtExpr.
From MyProject Require Import SmtQuery.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrSymbolicSemantics.
From MyProject Require Import CrConcreteSemantics.
From MyProject Require Import ConcreteToSymbolicLemmas.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrTransformer.
Require Import Strings.String.
Open Scope string_scope.
Require Import ZArith.
Require Import List.
Import ListNotations.

(* Header definition: H *)
Definition header_H : Header := HeaderCtr 1%positive.

(* Action: MyAction1 *)
Definition MyAction1_op : HdrOp := 
  StatelessOp AddOp (ConstantArg (repr 1%Z))  (ConstantArg (repr 0%Z)) header_H.

(* Table: the_table_0 *)
Definition the_table_0_seq_rule : SeqRule := 
  SeqCtr [(header_H, repr 0%Z)] [MyAction1_op]. (* Match and execute actions *)

Definition the_table_0_rule : MatchActionRule := 
  Seq the_table_0_seq_rule.

(* THE SIMPLEST POSSIBLE ProgramState SmtArithExpr *)
(* We have been operating on stateless only so far so this is a dummy instance to satisfy the compiler.*)
Definition simplest_state : ProgramState SmtArithExpr := {|
ctrl_plane_map := fun _ => SmtConst (repr 0%Z);
header_map := fun _ => SmtConst (repr 0%Z);
state_var_map := fun _ => SmtConst (repr 0%Z)
|}.

Definition headers_to_check : list Header := [header_H].
Definition state_vars_to_check : list StateVar := [].
(* Construct the equivalence checker instance *)
Definition my_equivalence_check : SmtResult :=
  equivalence_checker
      simplest_state       (* Starting symbolic state *)
      the_table_0_seq_rule          (* First rule *)
      the_table_0_seq_rule          (* Second rule (same) *)
      headers_to_check             
      state_vars_to_check.         
Eval compute in my_equivalence_check.

