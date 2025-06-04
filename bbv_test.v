Require Import bbv.Word.
Require Import String.
Require Import List.

Open Scope string_scope.

(* 8-bit zero bitvector *)
Definition zeros8 : Word.word 8 := Word.wzero 8.

(* 8-bit bitvector from nat *)
Definition bv_from_nat (x : nat) : Word.word 8 := Word.natToWord 8 x.

(* Bitwise AND *)
Definition bv_and (a b : Word.word 8) : Word.word 8 := Word.wand a b.

(* Bitwise OR *)
Definition bv_or (a b : Word.word 8) : Word.word 8 := Word.wor a b.

(* Bitwise XOR *)
Definition bv_xor (a b : Word.word 8) : Word.word 8 := Word.wxor a b.

(* Bitwise NOT *)
Definition bv_not (a : Word.word 8) : Word.word 8 := Word.wnot a.

(* Bitwise left shift *)
Definition bv_shl (a : Word.word 8) : Word.word 8 :=
  Word.wlshift a 5.

(* Bitwise right shift *)
Definition bv_shr (a : Word.word 8) : Word.word 8 :=
  Word.wrshift a 5.

(* Example usage: separate functions for each operation *)
Definition example_a : Word.word 8 := bv_from_nat 5.
Definition example_b : Word.word 8 := bv_from_nat 3.

Definition and_result : Word.word 8 := bv_and example_a example_b.
Definition or_result : Word.word 8 := bv_or example_a example_b.
Definition xor_result : Word.word 8 := bv_xor example_a example_b.
Definition not_result : Word.word 8 := bv_not example_a.
Definition shl_result : Word.word 8 := bv_shl example_a.
Definition shr_result : Word.word 8 := bv_shr example_a.

(* Example results *)
Compute example_a.
Compute example_b.
Compute and_result.
Compute or_result.
Compute xor_result.
Compute not_result.
Check not_result.
Check shl_result.
Compute shl_result.
Compute shr_result.