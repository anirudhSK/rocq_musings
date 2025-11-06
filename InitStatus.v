From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From Stdlib Require Import ZArith.

Inductive InitStatus (A: Type) : Type :=
  | Uninitialized : InitStatus A
  | Initialized : A -> InitStatus A.

Definition initstatus_uint8_equal (x y : InitStatus uint8) : bool :=
  match x, y with
  | Uninitialized, Uninitialized => true
  | Initialized a1, Initialized a2 => eq a1 a2
  | _, _ => false
  end.

(* Helper functions to do arithmetic on InitStatus uint8 *)
Definition add (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.add a1 a2)
  | _, _ => Uninitialized uint8
  end.

(* Same thing as above for sub, and, or, xor, mul, divu, modu *)
Definition sub (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.sub a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition and (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.and a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition or (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.or a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition xor (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.xor a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition mul (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.mul a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition divu (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.divu a1 a2)
  | _, _ => Uninitialized uint8
  end.

Definition modu (x y : InitStatus uint8) : InitStatus uint8 :=
  match x, y with
  | Initialized a1, Initialized a2 => Initialized uint8 (Integers.modu a1 a2)
  | _, _ => Uninitialized uint8
  end.

(* InitStatus version of not *)
Definition not (x : InitStatus uint8) : InitStatus uint8 :=
  match x with
  | Initialized a => Initialized uint8 (Integers.not a)
  | Uninitialized => Uninitialized uint8
  end.

Lemma concrete_if_else : forall v1 v2,
  ((if initstatus_uint8_equal v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct (initstatus_uint8_equal v1 v2) eqn:Ex.
  -- unfold initstatus_uint8_equal in Ex.
     destruct v1 eqn:desv1, v2 eqn:desv2; simpl in Ex; auto.
     --- exfalso. congruence.
     --- exfalso. congruence.
     --- unfold eq in Ex.
         unfold Rocqlib.zeq in Ex.
         destruct (Z.eq_dec (unsigned u) (unsigned u0)) as [Heq|Hneq].
         ---- apply uint8_eq_from_unsigned in Heq. rewrite Heq.
              reflexivity.
         ---- exfalso. congruence.
  -- exfalso. congruence.
Qed.


Lemma concrete_if_else2 : forall v1 v2,
  ((if initstatus_uint8_equal v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct (initstatus_uint8_equal v1 v2) eqn:Ex.
  -- exfalso. congruence.
  -- unfold initstatus_uint8_equal in Ex.
     destruct v1 eqn:desv1, v2 eqn:desv2; simpl in Ex; auto.
     --- exfalso. congruence.
     --- discriminate.
     --- discriminate.
     --- unfold eq in Ex.
         unfold Rocqlib.zeq in Ex.
         destruct (Z.eq_dec (unsigned u) (unsigned u0)) as [Heq|Hneq].
         ---- exfalso. congruence.
         ---- apply uint8_neq_from_unsigned in Hneq.
              intro Hcontra.
              injection Hcontra as H_eq.
              apply Hneq.
              exact H_eq.             
Qed.

(* TODO: Global Opaque the definitions here *)