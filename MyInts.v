From MyProject Require Import Integers.
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

Lemma uint8_concrete_if_else : forall (v1 v2 : uint8),
  ((if eq v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct (eq v1 v2) eqn:Ex.
  -- unfold eq in Ex.
     unfold Rocqlib.zeq in Ex.
     destruct (Z.eq_dec (unsigned v1) (unsigned v2)) as [Heq|Hneq].
     ---- apply uint8_eq_from_unsigned in Heq. rewrite Heq.
          reflexivity.
     ---- exfalso. congruence.
  -- exfalso. congruence.
Qed.

Lemma uint8_concrete_if_else2 : forall (v1 v2 : uint8),
  ((if eq v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct (eq v1 v2) eqn:Ex.
  -- exfalso. congruence.
  -- unfold eq in Ex.
     unfold Rocqlib.zeq in Ex.
     destruct (Z.eq_dec (unsigned v1) (unsigned v2)) as [Heq|Hneq].
     --- exfalso. congruence.
     --- apply uint8_neq_from_unsigned in Hneq.
         assumption.            
Qed.