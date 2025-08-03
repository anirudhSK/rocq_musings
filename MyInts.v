From MyProject Require Export Integers.
Require Import ZArith.

(* Various kinds of fixed-bit-width integers *)
Definition uint8 := @bit_int 8%positive.