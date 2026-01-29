From MyProject Require Import Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8   := @bit_int  8%positive.
Definition uint32  := @bit_int 32%positive.
Definition uintptr := @bit_int 32%positive.

Lemma uintw_eq_from_unsigned :
  forall (w : positive) (v1 v2 : @bit_int w),
  unsigned v1 = unsigned v2 -> v1 = v2.
Proof.
  intros w v1 v2 H.
  destruct v1, v2.
  apply mkint_eq; auto.
Qed.

Lemma uintw_neq_from_unsigned :
  forall (w : positive) (v1 v2 : @bit_int w),
  unsigned v1 <> unsigned v2 -> v1 <> v2.
Proof.
  intros w v1 v2 H.
  destruct v1 as [val1 range1].
  destruct v2 as [val2 range2].
  simpl in H.
  intro Heq.
  injection Heq as H_val_eq.
  apply H.
  assumption.
Qed.
