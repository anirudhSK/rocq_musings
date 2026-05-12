From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import CrVal.

(* The ProgramState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record ProgramState (T : Type) := {
  ctrl_map : PMap.t T;
  header_map : PMap.t T;
  state_map : PMap.t T;
}.

Arguments header_map {T} _.
Arguments state_map {T} _.  
Arguments ctrl_map {T} _.

Definition ConcreteState := ProgramState CrVal.
Definition SymbolicState := ProgramState SmtArithExpr.