From Stdlib.Strings Require Import String.
From MyProject Require Import CrVal.

(* Note that these strings may or may not have a one-to-one correspondence with
  identifiers in the CrDsl program. *)
(* A valuation has two components because the query has two sorts: scalars
  (headers, state vars, ctrl config, packet bits -- all read through [sv_ints])
  and memory regions ([sv_arrs]).  There are still no primitive bool variables
  within the IR; a symbolic packet bit is an integer read as nonzero/zero.
  Expressions can of course be bools (for conditionals, equalities, etc). *)
Record SmtValuation := mkSmtValuation {
  sv_ints : string -> CrVal;
  sv_arrs : string -> @Array CrVal;
}.

Inductive SmtResult : Type :=
  | SmtSat (f : SmtValuation)  (* Satisfiable with valuation f *)
  | SmtUnsat                   (* Unsatisfiable *)
  | SmtUnknown.                (* Unknown status *)
