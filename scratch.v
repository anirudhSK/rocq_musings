(*

Require Import List.
Import ListNotations.

Require Import Strings.String.

Definition my_pair : nat * bool := (42, true).
Check CaracaraProgram.
Check my_pair.

(* Various iden*)

(* A CaracaraProgram is a list of modules, followed by a list of connections *)
Definition CaracaraProgram : Type :=  (list ModuleName) * (list ConnectionName).

Definition my_list : list nat := [1; 2; 3; 4].
Definition double_list (l : list nat) : list nat :=
  map (fun x => x * 2) l.

Eval compute in double_list my_list. *)