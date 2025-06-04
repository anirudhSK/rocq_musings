Require Import Coq.Vectors.Vector.
Import VectorNotations.

Definition Bvector := Vector.t bool.

(* Create a Bvector of length 4 *)
Definition bv4 : Bvector 4 := [true; false; true; false]%vector.

Definition bool_to_nat (b : bool) := if b then 1 else 0.

(* Negate all bits in the Bvector *)
Definition bv4_neg := Vector.map negb bv4.
Definition bv_and {n : nat} (v1 v2 : Bvector n) : Bvector n :=
  Vector.map2 andb v1 v2.
Definition bv_or {n : nat} (v1 v2 : Bvector n) : Bvector n :=
  Vector.map2 orb v1 v2.
Definition bv_xor {n : nat} (v1 v2 : Bvector n) : Bvector n :=
  Vector.map2 xorb v1 v2.
Definition bv_nand {n : nat} (v1 v2 : Bvector n) : Bvector n :=
  Vector.map2 (fun x y => negb (andb x y)) v1 v2.
Definition bv_nor {n : nat} (v1 v2 : Bvector n) : Bvector n :=
  Vector.map2 (fun x y => negb (orb x y)) v1 v2.

(* Can you implement a bvector to nat conversion function? *)
Definition bv_to_nat {n : nat} (v : Bvector n) : nat :=
  Vector.fold_left (fun acc b => acc * 2 + bool_to_nat b) 0 v.

(* Example usage of bv_to_nat *)
Lemma test1 : bv_to_nat ([true; false; true; false]%vector) = 10.
Proof. reflexivity. Qed.

(* Example usage of bv_to_nat *)
Lemma test2 : bv_to_nat ([true; false; true; true]%vector) = 11.
Proof. reflexivity. Qed.

(* Example usage of bv_to_nat *)
Lemma test3 : bv_to_nat ([true; true; false; false]%vector) = 12.
Proof. reflexivity. Qed.