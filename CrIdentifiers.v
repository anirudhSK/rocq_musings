From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

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

Definition module_name_equal (m1 m2 : ModuleName) :=
    match m1, m2 with
            | ModuleNameCtr xid, ModuleNameCtr yid => Pos.eqb xid yid
    end.

Definition function_name_equal (f1 f2 : FunctionName) :=
    match f1, f2 with
            | FunctionNameCtr xid, FunctionNameCtr yid => Pos.eqb xid yid
    end.

Definition connection_name_equal (c1 c2 : ConnectionName) :=
    match c1, c2 with
            | ConnectionNameCtr xid, ConnectionNameCtr yid => Pos.eqb xid yid
    end.

(* Decidable equality for the varlike identifiers, derived from positive equality. *)
Definition header_eq_dec : forall x y : Header, {x = y} + {x <> y}.
Proof.
  intros [a] [b]. destruct (Pos.eq_dec a b);
    [left; subst; reflexivity | right; intro Heq; inversion Heq; contradiction].
Defined.

Definition state_eq_dec : forall x y : State, {x = y} + {x <> y}.
Proof.
  intros [a] [b]. destruct (Pos.eq_dec a b);
    [left; subst; reflexivity | right; intro Heq; inversion Heq; contradiction].
Defined.

Definition ctrl_eq_dec : forall x y : Ctrl, {x = y} + {x <> y}.
Proof.
  intros [a] [b]. destruct (Pos.eq_dec a b);
    [left; subst; reflexivity | right; intro Heq; inversion Heq; contradiction].
Defined.
