Require Import Strings.String.
From MyProject Require Export Integers.
From MyProject Require Import MyInts.
From MyProject Require Export InitStatus.
Require Import ZArith.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (uid : positive).
Inductive Header : Type := HeaderCtr (uid : positive).
Inductive State : Type := StateCtr (uid : positive).
Inductive ModuleName : Type := ModuleNameCtr (uid : positive).
Inductive FunctionName : Type := FunctionNameCtr (uid : positive).
Inductive ConnectionName : Type := ConnectionNameCtr (uid : positive).
Inductive Ctrl : Type := CtrlCtr (uid : positive).

(* Equality check functions for the identifiers above *)
Definition parser_state_equal (p1 p2 : ParserState) :=
    match p1, p2 with
            | ParserStateCtr xid, ParserStateCtr yid => Pos.eqb xid yid
    end.
(* Use positive equality directly for identifiers *)
Definition parser_state_equal' (p1 p2 : ParserState) :=
        match p1, p2 with
        | ParserStateCtr xid, ParserStateCtr yid => Pos.eqb xid yid
        end.
(* Do the same thing as parser_state_equal for Header *)
Definition header_equal (h1 h2 : Header) :=
    match h1, h2 with
            | HeaderCtr xid, HeaderCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for State *)
Definition state_equal (sv1 sv2 : State) :=
    match sv1, sv2 with
            | StateCtr xid, StateCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for ModuleName *)
Definition module_name_equal (m1 m2 : ModuleName) :=
    match m1, m2 with
            | ModuleNameCtr xid, ModuleNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for FunctionName *)
Definition function_name_equal (f1 f2 : FunctionName) :=
    match f1, f2 with
            | FunctionNameCtr xid, FunctionNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for ConnectionName *)
Definition connection_name_equal (c1 c2 : ConnectionName) :=
    match c1, c2 with
            | ConnectionNameCtr xid, ConnectionNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for Ctrl *)
Definition ctrl_equal (cc1 cc2 : Ctrl) :=
    match cc1, cc2 with
            | CtrlCtr xid, CtrlCtr yid => Pos.eqb xid yid
    end.

Definition hdr_list_equal (h1 : list Header) (h2 : list Header) :=
  andb (List.forallb (fun '(x, y) => header_equal x y) (List.combine h1 h2)) (* every pair has equal elements *)
       (Nat.eqb (List.length h1) (List.length h2)).                          (* both lists have same number of elements *)

(* Generate same definitions as above but for state variables *)
Definition state_list_equal (s1 : list State) (s2 : list State) :=
  andb (List.forallb (fun '(x, y) => state_equal x y) (List.combine s1 s2))
       (Nat.eqb (List.length s1) (List.length s2)).