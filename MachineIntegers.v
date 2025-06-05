Require Import ZArith.
Require Import Lia.
Definition GreaterThan5Int := {n : Z | (n >= 5)%Z }.
Example hello : nat := 5.
Example hello2: GreaterThan5Int.
Proof.
    exists 6%Z.
    lia.
Defined.
Check hello2.

(* Start with the unsigned 8-bit integers for now *)
Definition uint8 := {n : Z | (0 <= n < 256)%Z }.
Definition eq (x y : uint8) := Z.eqb (proj1_sig x) (proj1_sig y).
Definition lt (x y : uint8) := Z.ltb (proj1_sig x) (proj1_sig y).

Definition add (x y : uint8): uint8.
Proof.
  exists ((proj1_sig x + proj1_sig y) mod 256)%Z. (* witness *)
  apply Z.mod_pos_bound. lia.                     (* proof of witness *)
Defined.

Definition sub (x y : uint8): uint8.
Proof.
  exists ((proj1_sig x - proj1_sig y) mod 256)%Z.
  apply Z.mod_pos_bound. lia.
Defined.

Definition shift_left (x : uint8) (n : uint8) : uint8.
Proof.
  exists ((Z.shiftl (proj1_sig x) (proj1_sig n)) mod 256)%Z.
  apply Z.mod_pos_bound. lia.
Defined.

Definition shift_right (x : uint8) (n : uint8) : uint8.
Proof.
  exists ((Z.shiftr (proj1_sig x) (proj1_sig n)) mod 256)%Z.
  apply Z.mod_pos_bound. lia.
Defined.

Definition bw_and (x y : uint8) : uint8.
Proof.
    exists ((Z.land (proj1_sig x) (proj1_sig y)) mod 256)%Z.
    apply Z.mod_pos_bound. lia.
Defined.

Definition bw_or (x y : uint8) : uint8.
Proof.
    exists ((Z.lor (proj1_sig x) (proj1_sig y)) mod 256)%Z.
    apply Z.mod_pos_bound. lia.
Defined.

Definition bw_xor (x y : uint8) : uint8.
Proof.
    exists ((Z.lxor (proj1_sig x) (proj1_sig y)) mod 256)%Z.
    apply Z.mod_pos_bound. lia.
Defined.