From Stdlib.Strings Require Import String.
From MyProject Require Import MyInts.

(* Note that these strings may or may not have a one-to-one correspondence with
  identifiers in the CrDsl program. *)
(* Currently only need valuations from strings to uint8
  because there are no primitive bool variables within the IR.
  Expressions can still be bools though (for conditionals, equalities, etc.) *)
Definition SmtValuation := string -> uint8.

Inductive SmtResult : Type :=
  | SmtSat (f : SmtValuation)  (* Satisfiable with valuation f *)
  | SmtUnsat                   (* Unsatisfiable *)
  | SmtUnknown.                (* Unknown status *)