module Datatypes = struct
  (* If you omit this next line, then we would lose all the other
    operations in the new re-defined Datatypes, so first we include
    it. *)
  include Datatypes
  type bool = [%import: Datatypes.bool]
  [@@deriving sexp]
end
module Ascii = struct
  include Ascii
  type ascii = [%import: Ascii.ascii]
  [@@deriving sexp]
end
module String = struct
  include String
  type string = [%import: String.string]
  [@@deriving sexp]
end
module BinNums = struct
  include BinNums
  type positive = [%import: BinNums.positive]
  [@@deriving sexp]
  type coq_Z = [%import: BinNums.coq_Z]
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
end

type coq_SmtBoolExpr = [%import: SmtExpr.coq_SmtBoolExpr]
[@@deriving sexp]
and coq_SmtArithExpr = [%import: SmtExpr.coq_SmtArithExpr]
[@@deriving sexp]