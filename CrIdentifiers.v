Require Import Strings.String.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import InitStatus.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (uid : positive).
Inductive Header : Type := HeaderCtr (uid : positive).
Inductive State : Type := StateCtr (uid : positive).
Inductive ModuleName : Type := ModuleNameCtr (uid : positive).
Inductive FunctionName : Type := FunctionNameCtr (uid : positive).
Inductive ConnectionName : Type := ConnectionNameCtr (uid : positive).
Inductive Ctrl : Type := CtrlCtr (uid : positive).

Definition injective_contravariant {A B} (f : A -> B) : Prop :=
  forall x y, x <> y -> f x <> f y.

Class CrVarLike (A : Type) := {
  make_item : positive -> A;
  get_key   : A -> positive;
  inverses : forall (x : A), make_item (get_key x) = x;
  inverses' : forall (i : positive), get_key (make_item i) = i;
  inj : injective_contravariant get_key;
}.

Instance CrVarLike_Header : CrVarLike Header.
Proof.
  refine {| make_item := fun uid => HeaderCtr uid;
            get_key := fun h => match h with HeaderCtr uid => uid end;
            inverses := _;
            inj := _ |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [uid]. simpl. reflexivity.
  - (* inverses' : forall i, get_key (make_item i) = i *)
    reflexivity.
  - (* inj : injective_contravariant get_key *)
    intros x y Hxy Heq.
    destruct x as [uid1], y as [uid2]; simpl in Heq.
    rewrite Heq in Hxy.
    congruence.
Defined.

(* Do the same as CrVarLike Header, but for CrVarLike State *)
Instance CrVarLike_State : CrVarLike State.
Proof.
  refine {| make_item := fun uid => StateCtr uid;
            get_key := fun s => match s with StateCtr uid => uid end;
            inverses := _;
            inj := _ |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [uid]. simpl. reflexivity.
  - (* inverses' : forall i, get_key (make_item i) = i *)
    reflexivity.
  - (* inj : injective_contravariant get_key *)
    intros x y Hxy Heq.
    destruct x as [uid1], y as [uid2]; simpl in Heq.
    rewrite Heq in Hxy.
    congruence.
Defined.

Instance CrVarLike_Ctrl : CrVarLike Ctrl.
Proof.
  refine {| make_item := fun uid => CtrlCtr uid;
            get_key := fun s => match s with CtrlCtr uid => uid end;
            inverses := _;
            inj := _ |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [uid]. simpl. reflexivity.
  - (* inverses' : forall i, get_key (make_item i) = i *)
    reflexivity.
  - (* inj : injective_contravariant get_key *)
    intros x y Hxy Heq.
    destruct x as [uid1], y as [uid2]; simpl in Heq.
    rewrite Heq in Hxy.
    congruence.
Defined.

(* Equality check functions for the identifiers above *)
Definition parser_state_equal (p1 p2 : ParserState) :=
    match p1, p2 with
            | ParserStateCtr xid, ParserStateCtr yid => Pos.eqb xid yid
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

Section CrVarLikeEqual.

Context {A : Type} `{CrVarLike A}.

Definition varlike_equal (v1 v2 : A) :=
  Pos.eqb (get_key v1) (get_key v2).

Lemma varlike_equal_lemma :
  forall v1 v2,
  varlike_equal v1 v2 = true ->
  v2 = v1.
Proof.
  intros.
  unfold varlike_equal in H0.
  apply Pos.eqb_eq in H0.
  rewrite <- inverses.
  rewrite H0.
  rewrite inverses.
  reflexivity.
Qed.

Fixpoint varlike_list_equal (v1 v2 : list A) :=
  match v1, v2 with
  | nil, nil => true
  | v::y, v'::y' => andb (varlike_equal v v') (varlike_list_equal y y')
  | _, _ => false
  end.

Lemma varlike_list_equal_lemma :
  forall v1 v2,
  varlike_list_equal v1 v2 = true ->
  v1 = v2.
Proof.
  intros.
  revert v2 H0.
  induction v1 as [|v1' v1''].
  - destruct v2.
    + reflexivity.
    + discriminate.
  - destruct v2 as [|v2' v2''].
    + intros. simpl in *. congruence.
    + intros. simpl in *.
      rewrite andb_true_iff in H0. destruct H0.
      apply varlike_equal_lemma in H0.
      apply IHv1'' in H1.
      rewrite H0. rewrite <- H1. reflexivity.
Qed.

End CrVarLikeEqual.
