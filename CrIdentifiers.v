From Stdlib Require Import ZArith.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Import Bool.
From Stdlib Require Import List.
Import ListNotations.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserStateLabel : Type := ParserStateLabelCtr (uid : positive).
Inductive Header : Type := HeaderCtr (uid : positive).
Inductive State : Type := StateCtr (uid : positive).
Inductive ModuleName : Type := ModuleNameCtr (uid : positive).
Inductive FunctionName : Type := FunctionNameCtr (uid : positive).
Inductive Ctrl : Type := CtrlCtr (uid : positive).

Class Posesque (A : Type) := {
  wrap       : positive -> A;
  unwrap     : A -> positive;
  incr       : A -> A;
  unwrap_inj : forall x y : A, unwrap x = unwrap y -> x = y;
}.

Instance Posesque_ParserStateLabel : Posesque ParserStateLabel := {
  wrap := fun p => ParserStateLabelCtr p;
  unwrap := fun s => match s with ParserStateLabelCtr p => p end;
  incr := fun s => match s with ParserStateLabelCtr p => ParserStateLabelCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | ParserStateLabelCtr px, ParserStateLabelCtr py =>
                   fun H => f_equal ParserStateLabelCtr H
               end;
}.
Instance Posesque_Header : Posesque Header := {
  wrap := fun p => HeaderCtr p;
  unwrap := fun s => match s with HeaderCtr p => p end;
  incr := fun s => match s with HeaderCtr p => HeaderCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | HeaderCtr px, HeaderCtr py =>
                   fun H => f_equal HeaderCtr H
               end;
}.
Instance Posesque_State : Posesque State := {
  wrap := fun p => StateCtr p;
  unwrap := fun s => match s with StateCtr p => p end;
  incr := fun s => match s with StateCtr p => StateCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | StateCtr px, StateCtr py =>
                   fun H => f_equal StateCtr H
               end;
}.
Instance Posesque_ModuleName : Posesque ModuleName := {
  wrap := fun p => ModuleNameCtr p;
  unwrap := fun s => match s with ModuleNameCtr p => p end;
  incr := fun s => match s with ModuleNameCtr p => ModuleNameCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | ModuleNameCtr px, ModuleNameCtr py =>
                   fun H => f_equal ModuleNameCtr H
               end;
}.
Instance Posesque_FunctionName : Posesque FunctionName := {
  wrap := fun p => FunctionNameCtr p;
  unwrap := fun s => match s with FunctionNameCtr p => p end;
  incr := fun s => match s with FunctionNameCtr p => FunctionNameCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | FunctionNameCtr px, FunctionNameCtr py =>
                   fun H => f_equal FunctionNameCtr H
               end;
}.
Instance Posesque_Ctrl : Posesque Ctrl := {
  wrap := fun p => CtrlCtr p;
  unwrap := fun s => match s with CtrlCtr p => p end;
  incr := fun s => match s with CtrlCtr p => CtrlCtr (p + 1) end;
  unwrap_inj :=
    fun x y => match x, y with
               | CtrlCtr px, CtrlCtr py =>
                   fun H => f_equal CtrlCtr H
               end;
}.

Section Posesque.
Context {A : Type} {PA : Posesque A}.
Definition posesque_eq (v1 v2: A) : Prop :=
  Pos.eq (unwrap v1) (unwrap v2).
Definition posesque_eqb (v1 v2: A) : bool :=
  Pos.eqb (unwrap v1) (unwrap v2).
Lemma posesque_eq_eqb :
  forall v1 v2,
    posesque_eq v1 v2 <-> posesque_eqb v1 v2 = true.
Proof.
  intros. unfold posesque_eq, posesque_eqb.
  rewrite Pos.eqb_eq. reflexivity.
Qed.
Lemma posesque_eqb_iff :
  forall (x y : A), posesque_eqb x y = true <-> x = y.
Proof.
  intros. unfold posesque_eqb. split.
  - intros H. apply Pos.eqb_eq in H. apply unwrap_inj. exact H.
  - intros H. inversion H. apply Pos.eqb_refl.
Qed.
Lemma posesque_eqb_refl :
  forall (x : A), posesque_eqb x x = true.
Proof. intros. apply posesque_eqb_iff. reflexivity. Qed.
Lemma posesque_eqb_sym :
  forall (x y : A), posesque_eqb x y = posesque_eqb y x.
Proof.
  intros x y. unfold posesque_eqb.
  destruct (Pos.eqb (unwrap x) (unwrap y)) eqn:E.
  - symmetry. apply Pos.eqb_eq. apply Pos.eqb_eq in E. auto.
  - symmetry. apply Pos.eqb_neq. apply Pos.eqb_neq in E. auto.
Qed.
Definition posesque_eq_dec (x y : A) : {x = y} + {x <> y}.
Proof.
  destruct (posesque_eqb x y) eqn:Heq.
  - left. apply posesque_eqb_iff. exact Heq.
  - right. intros H. apply posesque_eqb_iff in H.
    rewrite H in Heq. discriminate.
Defined.
End Posesque.
