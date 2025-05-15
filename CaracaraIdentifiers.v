Require Import Strings.String.

(* Define the different types of identifiers in the Caracara DSL *)
Definition ParserState : Type := string.
Definition Header : Type := string.
Definition StateVar : Type := string.
Definition ModuleName : Type := string.
Definition FunctionName : Type := string.
Definition ConnectionName : Type := string.
Definition VariableName : Type := string.
Definition CtrlPlaneConfigName : Type := string.