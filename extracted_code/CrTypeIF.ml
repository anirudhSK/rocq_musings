module BinNums = struct
  include BinNums
  type positive = [%import: BinNums.positive]
  [@@deriving sexp]
  type coq_Z = [%import: BinNums.coq_Z]
  [@@deriving sexp]
end
module Datatypes = struct
  include Datatypes
  type nat = [%import: Datatypes.nat]
  [@@deriving sexp]
  type bool = [%import: Datatypes.bool]
  [@@deriving sexp]
  type 'a option = [%import: 'a Datatypes.option]
  [@@deriving sexp]
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
  type uint64 = [%import: MyInts.uint64]
  [@@deriving sexp]
  type uintbptr = [%import: MyInts.uintbptr]
  [@@deriving sexp]
end
module CrVal = struct
include CrVal
type coq_CrWidth = [%import: CrVal.coq_CrWidth]
[@@deriving sexp]
type coq_CrIntType = [%import: CrVal.coq_CrIntType]
[@@deriving sexp]
type coq_CrPtr_T = [%import: CrVal.coq_CrPtr_T]
[@@deriving sexp]
type coq_CrVal = [%import: CrVal.coq_CrVal]
[@@deriving sexp]
end
module CrIdentifiers = struct
  include CrIdentifiers
  type coq_ParserStateLabel = [%import: CrIdentifiers.coq_ParserStateLabel]
  [@@deriving sexp]
  type coq_Header = [%import: CrIdentifiers.coq_Header]
  [@@deriving sexp]
  type coq_State = [%import: CrIdentifiers.coq_State]
  [@@deriving sexp]
  type coq_ModuleName = [%import: CrIdentifiers.coq_ModuleName]
  [@@deriving sexp]
  type coq_Ctrl = [%import: CrIdentifiers.coq_Ctrl]
  [@@deriving sexp]
end
module CrTransformer = struct
  include CrTransformer
  type coq_Operand = [%import: CrTransformer.coq_Operand]
  [@@deriving sexp]
  type coq_CmpOp = [%import: CrTransformer.coq_CmpOp]
  [@@deriving sexp]
  type coq_BinaryOp = [%import: CrTransformer.coq_BinaryOp]
  [@@deriving sexp]
  type coq_HdrOp = [%import: CrTransformer.coq_HdrOp]
  [@@deriving sexp]
  type coq_MatchValue = [%import: CrTransformer.coq_MatchValue]
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
module CrDeparser = struct
  include CrDeparser
  type coq_EmitOp = [%import: CrDeparser.coq_EmitOp]
  [@@deriving sexp]
  type coq_Deparser = [%import: CrDeparser.coq_Deparser]
  [@@deriving sexp]
end
module CrParser = struct
  include CrParser
  type coq_ParserOp = [%import: CrParser.coq_ParserOp]
  [@@deriving sexp]
  type coq_ParserTarget = [%import: CrParser.coq_ParserTarget]
  [@@deriving sexp]
  type coq_SelectCase = [%import: CrParser.coq_SelectCase]
  [@@deriving sexp]
  type coq_Transition = [%import: CrParser.coq_Transition]
  [@@deriving sexp]
  type coq_ParserStateDef = [%import: CrParser.coq_ParserStateDef]
  [@@deriving sexp]
  type coq_Parser = [%import: CrParser.coq_Parser]
  [@@deriving sexp]
end
module CrDsl = struct
  include CrDsl
  type coq_CaracaraProgram = [%import: CrDsl.coq_CaracaraProgram]
  [@@deriving sexp]
  type coq_CrModule = [%import: CrDsl.coq_CrModule]
  [@@deriving sexp]
  type coq_Connections = [%import: CrDsl.coq_Connections]
  [@@deriving sexp]
end
(* Re-export at top level for backwards compatibility with the rest of
   the OCaml shim. *)
type coq_CaracaraProgram = CrDsl.coq_CaracaraProgram
let sexp_of_coq_CaracaraProgram = CrDsl.sexp_of_coq_CaracaraProgram
let coq_CaracaraProgram_of_sexp = CrDsl.coq_CaracaraProgram_of_sexp

module CrModule = struct
  include CrModule
  type coq_ModuleNetwork = [%import: CrModule.coq_ModuleNetwork]
  [@@deriving sexp]
  type coq_GeneralCaracaraProgram = [%import: CrModule.coq_GeneralCaracaraProgram]
  [@@deriving sexp]
end

module CrMem = struct
  type var_id = [%import : CrMem.var_id]
  [@@deriving sexp]
  type coq_Imm = [%import: CrMem.coq_Imm]
  [@@deriving sexp]
  type coq_FnArg = [%import: CrMem.coq_FnArg]
  [@@deriving sexp]
  type coq_ArithBinOp = [%import: CrMem.coq_ArithBinOp]
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
