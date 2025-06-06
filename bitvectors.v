Require Import Coq.Vectors.Vector.
Import VectorNotations.
Require Import Lia.

Definition Bvector := Vector.t bool.

Check eq_rect.

Lemma test_lemma : forall (shift : nat),
shift + (5 - shift) = 5.
Admitted.

Definition func (shift : nat) (v : Bvector 5) : Bvector 5 :=
  @eq_rect nat (shift + (5 - shift)) (Bvector)  (Vector.append (Vector.const false shift) (Vector.const false (5 - shift))) (5) (test_lemma shift).

 (* P (x) in eq_rect is vector.append : *)
 (* Read up on implicit type parameters and polymorphism chapter in software foundations *)