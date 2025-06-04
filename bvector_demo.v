(* Demonstration of Coq.Bool.Bvector usage *)

Require Import Coq.Bool.Bvector.
Require Import Coq.Vectors.Vector.
Import VectorNotations.

(* Create a Bvector of length 4 *)
Definition bv4 : Bvector 4 := [true; false; true; false]%vector.

(* Negate all bits in the Bvector *)
Definition bv4_neg := Vector.map negb bv4.

(* Convert Bvector to list for inspection *)
Definition bv4_list := Vector.to_list bv4.

(* Prove that the length of bv4 is 4 *)
Lemma bv4_length : List.length (Vector.to_list bv4) = 4.
Proof. reflexivity. Qed.

(* Prove that negating twice gives the original vector *)
Lemma bv4_double_neg : Vector.map negb (Vector.map negb bv4) = bv4.
Proof. reflexivity. Qed.