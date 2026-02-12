module BinNums = struct
  include BinNums
  type positive = [%import: BinNums.positive]
  [@@deriving sexp]
  type coq_Z = [%import: BinNums.coq_Z]
  [@@deriving sexp]
end
module Datatypes = struct
  include Datatypes
  type ('a, 'b) prod = [%import: ('a, 'b) Datatypes.prod]
  [@@deriving sexp]
  type 'a list = [%import: 'a Datatypes.list]
  [@@deriving sexp]
end
module Integers = struct
  include Integers
  type bit_int = [%import: Integers.bit_int]
  [@@deriving sexp]
end
module MyInts = struct
  include MyInts
  type uint8 = [%import: MyInts.uint8]
  [@@deriving sexp]
  type uint32 = [%import: MyInts.uint32]
  [@@deriving sexp]
  type uintptr = [%import: MyInts.uintptr]
  [@@deriving sexp]
end
module CrVal = struct
include CrVal
type coq_CrInt_T = [%import: CrVal.coq_CrInt_T]
[@@deriving sexp]
type coq_CrPtr_T = [%import: CrVal.coq_CrPtr_T]
[@@deriving sexp]
type coq_CrVal = [%import: CrVal.coq_CrVal]
[@@deriving sexp]
end
module CrIdentifiers = struct
  include CrIdentifiers
  type coq_Header = [%import: CrIdentifiers.coq_Header]
  [@@deriving sexp]
  type coq_State = [%import: CrIdentifiers.coq_State]
  [@@deriving sexp]
  type coq_Ctrl = [%import: CrIdentifiers.coq_Ctrl]
  [@@deriving sexp]
end
module CrTransformer = struct
  include CrTransformer
  type coq_FunctionArgument = [%import: CrTransformer.coq_FunctionArgument]
  [@@deriving sexp]
  type coq_BinaryOp = [%import: CrTransformer.coq_BinaryOp]
  [@@deriving sexp]
  type coq_HdrOp = [%import: CrTransformer.coq_HdrOp]
  [@@deriving sexp]
  type coq_MatchPattern = [%import: CrTransformer.coq_MatchPattern]
  [@@deriving sexp]
  type coq_SeqRule = [%import: CrTransformer.coq_SeqRule]
  [@@deriving sexp]
  type coq_ParRule = [%import: CrTransformer.coq_ParRule]
  [@@deriving sexp]
  type coq_MatchActionRule = [%import: CrTransformer.coq_MatchActionRule]
  [@@deriving sexp]
  type coq_Transformer = [%import: CrTransformer.coq_Transformer]
  [@@deriving sexp]
end
include CrDsl
type coq_CaracaraProgram = [%import: CrDsl.coq_CaracaraProgram]
[@@deriving sexp]

module CrMem = struct
  type var_id = [%import : CrMem.var_id]
  [@@deriving sexp]
  type coq_Imm = [%import: CrMem.coq_Imm]
  [@@deriving sexp]
  type coq_FnArg = [%import: CrMem.coq_FnArg]
  [@@deriving sexp]
  type coq_Instruction = [%import: CrMem.coq_Instruction]
  [@@deriving sexp]
  type coq_ValType = [%import: CrMem.coq_ValType]
  [@@deriving sexp]
  type coq_IM_Program = [%import: CrMem.coq_IM_Program]
  [@@deriving sexp]

  type arith_expr = [%import: CrMem.arith_expr]
  and ptr_expr = [%import: CrMem.ptr_expr]
  and arr_expr = [%import: CrMem.arr_expr]
  and bool_expr = [%import: CrMem.bool_expr]
  and coq_Z3Expr = [%import: CrMem.coq_Z3Expr]
  [@@deriving sexp]
end
