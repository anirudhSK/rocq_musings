Require Import Strings.String.
From MyProject Require Export Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8 := @bit_int 8.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (name : string).
Inductive Header : Type := HeaderCtr (name : string).
Inductive StateVar : Type := StateVarCtr (name : string).
Inductive ModuleName : Type := ModuleNameCtr (name : string).
Inductive FunctionName : Type := FunctionNameCtr (name : string).
Inductive ConnectionName : Type := ConnectionNameCtr (name : string).
Inductive CtrlPlaneConfigName : Type := CtrlPlaneConfigNameCtr (name : string).