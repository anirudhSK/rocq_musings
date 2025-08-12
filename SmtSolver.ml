(* smt_external.ml *)

(* This function matches the signature expected by the extracted code *)
let solve (expr : Equivalence_checker.smtBoolExpr) : Equivalence_checker.smtResult =
  match expr with
  | _ -> 
      Equivalence_checker.SmtUnknown