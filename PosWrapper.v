From Stdlib Require Import ZArith.

Class PosWrapper (A : Type) := {
  wrap   : positive -> A;
  unwrap : A -> positive;
  incr   : A -> A;
}.

From MyProject Require Import CrIdentifiers.

Instance PosWrapper_ParserState : PosWrapper ParserState := {
  wrap := fun p => ParserStateCtr p;
  unwrap := fun s => match s with ParserStateCtr p => p end;
  incr := fun s => match s with ParserStateCtr p => ParserStateCtr (p + 1) end
}.
Instance PosWrapper_Header : PosWrapper Header := {
  wrap := fun p => HeaderCtr p;
  unwrap := fun s => match s with HeaderCtr p => p end;
  incr := fun s => match s with HeaderCtr p => HeaderCtr (p + 1) end;
}.
Instance PosWrapper_State : PosWrapper State := {
  wrap := fun p => StateCtr p;
  unwrap := fun s => match s with StateCtr p => p end;
  incr := fun s => match s with StateCtr p => StateCtr (p + 1) end;
}.
Instance PosWrapper_ModuleName : PosWrapper ModuleName := {
  wrap := fun p => ModuleNameCtr p;
  unwrap := fun s => match s with ModuleNameCtr p => p end;
  incr := fun s => match s with ModuleNameCtr p => ModuleNameCtr (p + 1) end;
}.
Instance PosWrapper_FunctionName : PosWrapper FunctionName := {
  wrap := fun p => FunctionNameCtr p;
  unwrap := fun s => match s with FunctionNameCtr p => p end;
  incr := fun s => match s with FunctionNameCtr p => FunctionNameCtr (p + 1) end;
}.
Instance PosWrapper_ConnectionName: PosWrapper ConnectionName := {
  wrap := fun p => ConnectionNameCtr p;
  unwrap := fun s => match s with ConnectionNameCtr p => p end;
  incr := fun s => match s with ConnectionNameCtr p => ConnectionNameCtr (p + 1) end;
}.
Instance PosWrapper_Ctrl : PosWrapper Ctrl := {
  wrap := fun p => CtrlCtr p;
  unwrap := fun s => match s with CtrlCtr p => p end;
  incr := fun s => match s with CtrlCtr p => CtrlCtr (p + 1) end;
}.