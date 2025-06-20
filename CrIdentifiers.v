Require Import Strings.String.
From MyProject Require Export Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8 := @bit_int 8.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (uid : nat).
Inductive Header : Type := HeaderCtr (uid : nat).
Inductive StateVar : Type := StateVarCtr (uid : nat).
Inductive ModuleName : Type := ModuleNameCtr (uid : nat).
Inductive FunctionName : Type := FunctionNameCtr (uid : nat).
Inductive ConnectionName : Type := ConnectionNameCtr (uid : nat).
Inductive CtrlPlaneConfigName : Type := CtrlPlaneConfigNameCtr (uid : nat).