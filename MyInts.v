From MyProject Require Export Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8 := @bit_int 8%positive.

Lemma uint8_eq_from_unsigned : forall (v1 v2 : uint8),
  unsigned v1 = unsigned v2 -> v1 = v2.
Proof.
  intros v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  apply mkint_eq; auto.
Qed.

Lemma uint8_neq_from_unsigned : forall (v1 v2 : uint8),
  unsigned v1 <> unsigned v2 -> v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  simpl in H.
  intro Heq.
  injection Heq as H_val_eq.
  apply H.
  assumption.
Qed.
