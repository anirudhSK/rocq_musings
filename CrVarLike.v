Require Import Strings.String.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import InitStatus.
From MyProject Require Import CrIdentifiers.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

Definition injective_contravariant {A B} (f : A -> B) : Prop :=
  forall x y, x <> y -> f x <> f y.

Class CrVarLike (A : Type) := {
  make_item : positive -> A;
  get_key   : A -> positive;
  inverses : forall (x : A), make_item (get_key x) = x;
  inverses' : forall (i : positive), get_key (make_item i) = i;
  inj : injective_contravariant get_key;
}.

Ltac prove_inj :=
  intros x y Hxy Heq;
  destruct x as [uid1], y as [uid2]; simpl in Heq;
  rewrite Heq in Hxy;
  congruence.

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
    prove_inj.
Defined.

Instance CrVarLike_State : CrVarLike State.
Proof.
  refine {| make_item := fun uid => StateCtr uid;
            get_key := fun s => match s with StateCtr uid => uid end;
            inverses := _;
            inj := _ |}.
  - intros [uid]. simpl. reflexivity.
  - reflexivity.
  - prove_inj.
Defined.

Instance CrVarLike_Ctrl : CrVarLike Ctrl.
Proof.
  refine {| make_item := fun uid => CtrlCtr uid;
            get_key := fun c => match c with CtrlCtr uid => uid end;
            inverses := _;
            inj := _ |}.
  - intros [uid]. simpl. reflexivity.
  - reflexivity.
  - prove_inj.
Defined.

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