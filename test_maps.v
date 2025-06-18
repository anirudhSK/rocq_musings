From MyProject Require Import Maps.
From Coq.Strings Require Import String.

Check string_dec : forall (x y : string), {x = y} + {x <> y}.

Module StringEq.
  Definition t := string.
  Definition eq := string_dec.   
End StringEq.

Module StringMap := EMap(StringEq).