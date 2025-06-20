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

(* Equality check functions for the identifiers above *)
Definition parser_state_equal (p1 p2 : ParserState) :=
    match p1, p2 with
            | ParserStateCtr xid, ParserStateCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for Header *)
Definition header_equal (h1 h2 : Header) :=
    match h1, h2 with
            | HeaderCtr xid, HeaderCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for StateVar *)
Definition state_var_equal (sv1 sv2 : StateVar) :=
    match sv1, sv2 with
            | StateVarCtr xid, StateVarCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for ModuleName *)
Definition module_name_equal (m1 m2 : ModuleName) :=
    match m1, m2 with
            | ModuleNameCtr xid, ModuleNameCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for FunctionName *)
Definition function_name_equal (f1 f2 : FunctionName) :=
    match f1, f2 with
            | FunctionNameCtr xid, FunctionNameCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for ConnectionName *)
Definition connection_name_equal (c1 c2 : ConnectionName) :=
    match c1, c2 with
            | ConnectionNameCtr xid, ConnectionNameCtr yid => Nat.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for CtrlPlaneConfigName *)
Definition ctrl_plane_config_name_equal (cc1 cc2 : CtrlPlaneConfigName) :=
    match cc1, cc2 with
            | CtrlPlaneConfigNameCtr xid, CtrlPlaneConfigNameCtr yid => Nat.eqb xid yid
    end.