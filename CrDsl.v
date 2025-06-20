(* This file defines the grammar for the Caracara domain-specific language (DSL) *)
(* The grammar is defined using inductive types and is used to parse and interpret Caracara code. *)

(* Import necessary modules *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrTransformer.
From MyProject Require Export ListUtils.

(* A Module has a module name and either a parser or transformer definition *)
Inductive Module : Type := 
  | TransformerModule (m : ModuleName) (t : Transformer).

(* A Connection is a pair of module names *)
(* and a connection name *)
Inductive Connection : Type := 
  | ConnectionDef : ModuleName -> ModuleName -> ConnectionName -> Connection.

Inductive CaracaraProgram : Type := 
  | CaracaraProgramDef : 
      list ParserState -> 
      list Header -> 
      list StateVar -> 
      list ModuleName -> 
      list FunctionName -> 
      list ConnectionName -> 
      list CtrlPlaneConfigName -> 
      list Module -> 
      list Connection -> 
      CaracaraProgram.

Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef p h s m f c cc _ _ =>
      has_duplicates (fun x y =>
            match x, y with
            | ParserStateCtr xid, ParserStateCtr yid => Nat.eqb xid yid
            end) p ||
      has_duplicates (fun x y =>
            match x, y with
            | HeaderCtr xid, HeaderCtr yid => Nat.eqb xid yid
            end) h ||
      has_duplicates (fun x y =>
            match x, y with
            | StateVarCtr xid, StateVarCtr yid => Nat.eqb xid yid
            end) s ||
      has_duplicates (fun x y =>
            match x, y with
            | ModuleNameCtr xid, ModuleNameCtr yid => Nat.eqb xid yid
            end) m ||
      has_duplicates (fun x y =>
            match x, y with
            | FunctionNameCtr xid, FunctionNameCtr yid => Nat.eqb xid yid
            end) f ||
      has_duplicates (fun x y =>
            match x, y with
            | ConnectionNameCtr xid, ConnectionNameCtr yid => Nat.eqb xid yid
            end) c ||
      has_duplicates (fun x y =>
            match x, y with
            | CtrlPlaneConfigNameCtr xid, CtrlPlaneConfigNameCtr yid => Nat.eqb xid yid
            end) cc
  end.