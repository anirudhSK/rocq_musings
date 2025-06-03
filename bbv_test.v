Require Import bbv.Word.

(* 8-bit zero bitvector *)
Definition zeros8 : Word.word 8 := Word.wzero 8.

(* 8-bit bitvector from nat *)
Definition bv_from_nat (x : nat) : Word.word 8 := Word.natToWord 8 x.

(* Bitwise AND *)
Definition bv_and (a b : Word.word 8) : Word.word 8 := Word.wand a b.