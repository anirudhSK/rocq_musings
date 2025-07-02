From MyProject Require Export CrIdentifiers.
From MyProject Require Export CrTransformer.

Class Semantics (T : Type) := {
  lookup_function_argument : FunctionArgument -> @ProgramState T -> T;
  eval_hdr_op_expr : HdrOp -> @ProgramState T -> T;
  eval_hdr_op_assign : HdrOp -> @ProgramState T -> @ProgramState T;
}.