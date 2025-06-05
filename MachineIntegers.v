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