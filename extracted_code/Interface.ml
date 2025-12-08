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

(* Trusted Shim Procedures *)
include Integers
include Datatypes
include MyInts
include String
type coq_ValueMap =
| VMap of string * uint8 * coq_ValueMap
| VMap_DNE
let rec coq_TraverseMap (vm : coq_ValueMap) (s : string) : uint8 =
  match vm with
  | VMap (var_, val_, nxt_) ->
    if (s = var_) then
      val_
    else
      coq_TraverseMap nxt_ s
  | VMap_DNE -> repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) Z0
let coq_Z_to_int (n : BinNums.coq_Z) : int =
  let rec pos_to_int_ (n : BinNums.positive) (i : int) : int =
    match n with
    | Coq_xH -> 1 lsl i
    | Coq_xO n_ -> (pos_to_int_ n_ (i+1))
    | Coq_xI n_ -> (1 lsl i) + (pos_to_int_ n_ (i+1)) in
  let pos_to_int (n : BinNums.positive) : int = (pos_to_int_ n 0) in
  match n with
  | Z0 -> 0
  | Zpos n_ -> pos_to_int n_
  | Zneg n_ -> 0 - (pos_to_int n_)
let int_to_coq_uint8 (n : int) : BinNums.coq_Z =
  let rec int_to_pos (n : int) : BinNums.positive =
    if (n = 1) then Coq_xH
    else if (n mod 2 = 0) then
      Coq_xO (int_to_pos (n lsr 1))
    else
      Coq_xI (int_to_pos (n lsr 1)) in

  repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) (
    if (n = 0) then Z0
    else Zpos (int_to_pos n))
let rec coq_str_to_str (s : string) : Stdlib.String.t =
  let bool_to_bit (b : Datatypes.bool) (idx : int) : int =
    match b with
    | Coq_true -> 1 lsl idx
    | Coq_false -> 0 in
  let ascii_to_char (c : Ascii.ascii) : Stdlib.String.t =
    match c with
    | Ascii (b7, b6, b5, b4, b3, b2, b1, b0) -> Char.escaped (Char.chr (
      (bool_to_bit b7 7) +
      (bool_to_bit b6 6) +
      (bool_to_bit b5 5) +
      (bool_to_bit b4 4) +
      (bool_to_bit b3 3) +
      (bool_to_bit b2 2) +
      (bool_to_bit b1 1) +
      (bool_to_bit b0 0)
    )) in
  match s with
  | EmptyString -> ""
  | String (c, rest) -> (ascii_to_char c) ^ (coq_str_to_str rest)
let char_to_ascii (c : char) : Ascii.ascii =
  let get_bit (code: int) (idx: int) : Datatypes.bool =
    match ((code lsr idx) land 1) with
    | 0 -> Coq_false
    | 1 -> Coq_true
    | _ -> raise (Failure "&0x1 should only result in 0 or 1.") in
  let code : int = Char.code c in
  Ascii (get_bit code 7, get_bit code 6, get_bit code 5, get_bit code 4,
         get_bit code 3, get_bit code 2, get_bit code 1, get_bit code 0)
let rec str_to_coq_str (s : Stdlib.String.t) : string =
  match s with
  | "" -> EmptyString
  | _ ->
    let c = Stdlib.String.get s 0 in
    let rest = Stdlib.String.sub s 1 (Stdlib.String.length s - 1) in
    String.String ((char_to_ascii c), (str_to_coq_str rest))


let example_program : coq_CaracaraProgram =
  let h0 : BinNums.positive = Coq_xH in
  let r0 : BinNums.positive = Coq_xH in
  let r1 : BinNums.positive = Coq_xO Coq_xH in
  let r2 : BinNums.positive = Coq_xI Coq_xH in
  let r3 : BinNums.positive = Coq_xO (Coq_xO Coq_xH) in
  let headers = Coq_cons (h0, Coq_nil) in
  let states = Coq_cons (r0, (Coq_cons (r1, (Coq_cons (r2, (Coq_cons (r3,
    Coq_nil)))))))
  in
  let ctrls = Coq_nil in
  let match_pattern = Coq_cons ((Coq_pair (h0,
    (repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) Z0))), Coq_nil)
  in
  let action = Coq_cons ((CrTransformer.StatefulOp (AddOp, (ConstantArg
    (repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) (Zpos (Coq_xI (Coq_xO Coq_xH))))),
    (ConstantArg (repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) Z0)), r0)), Coq_nil)
  in
  let rule = CrTransformer.Seq (SeqCtr (match_pattern, action)) in
  let transformer = Coq_cons (rule, Coq_nil) in
  CaracaraProgramDef (headers, states, ctrls, transformer)
