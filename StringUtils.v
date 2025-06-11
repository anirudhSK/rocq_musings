Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Import ListNotations.

(* Checks if s1 is a prefix of s2 *)
Fixpoint string_prefix (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, _ => true
  | String a s1', String b s2' => if Ascii.eqb a b then string_prefix s1' s2' else false
  | _, _ => false
  end.

Eval compute in string_prefix "hdr_" "hdr_foo". (* returns true *)
Eval compute in string_prefix "ctrl_" "hdr_foo". (* returns false *)
Eval compute in string_prefix "ctrl_" "ctrl_bar". (* returns true *)
Eval compute in string_prefix "flibbertigibbit_" "flibbertigibbit_123". (* returns true *)
Eval compute in string_prefix "flibbertigibbit_" "flibbertigibbt_123". (* returns false *)

Fixpoint string_drop (n : nat) (s : string) : string :=
  match n, s with
  | O, _ => s
  | S n', EmptyString => EmptyString
  | S n', String _ s' => string_drop n' s'
  end.

Eval compute in string_drop 4 "hdr_foo". (* returns "foo" *)
Eval compute in string_drop 5 "ctrl_bar". (* returns "bar" *)
Eval compute in string_drop 6 "state_var_123". (* returns "var_123" *)