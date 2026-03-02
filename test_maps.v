From MyProject Require Import Maps.
From Stdlib.Strings Require Import String.
From Stdlib Require Import PArith.PArith.

(* Check string_dec : forall (x y : string), {x = y} + {x <> y}. *)

Module StringEq.
  Definition t := string.
  Definition eq := string_dec.   
End StringEq.

Module StringMap := EMap(StringEq).

Example test_pmap  := PMap.init nat.

(*
Eval compute in PMap.init 0.

Eval compute in (PMap.set (Pos.of_nat 1) 5 (PMap.init 0)).

Eval compute in (PMap.get (Pos.of_nat 1) (PMap.set (Pos.of_nat 1) 5 (PMap.init 0))).
*)