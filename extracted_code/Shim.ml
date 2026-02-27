
(* Trusted Shim Procedures *)
include Integers
include Datatypes
include MyInts
include String
type coq_ValueMap =
| VMap of string * CrVal.coq_CrVal * coq_ValueMap
| VMap_DNE
let rec coq_TraverseMap (vm : coq_ValueMap) (s : string) : CrVal.coq_CrVal =
  match vm with
  | VMap (var_, val_, nxt_) ->
    if (s = var_) then
      val_
    else
      coq_TraverseMap nxt_ s
  | VMap_DNE -> UninitVal
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
let rec pos_to_str (n : BinNums.positive) : Stdlib.String.t =
  match n with
  | Coq_xH -> "1"
  | Coq_xO n_ -> (pos_to_str n_) ^ "0"
  | Coq_xI n_ -> (pos_to_str n_) ^ "1"

let rec int_to_pos (n : int) : BinNums.positive =
  if (n = 1) then Coq_xH
  else if (n mod 2 = 0) then
    Coq_xO (int_to_pos (n lsr 1))
  else
    Coq_xI (int_to_pos (n lsr 1))
let int_to_coq_uint8 (n : int) : BinNums.coq_Z =
  repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) (
    if (n = 0) then Z0
    else Zpos (int_to_pos n))
let int_to_coq_uint32 (n : int) : BinNums.coq_Z =
  repr (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))) (
    if (n = 0) then Z0
    else Zpos (int_to_pos n))
let int_to_coq_uint64 (n : int) : BinNums.coq_Z =
  repr (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH)))))) (
    if (n = 0) then Z0
    else Zpos (int_to_pos n))
let rec coq_str_to_str (s : string) : Stdlib.String.t =
  let bool_to_bit (b : Datatypes.bool) (idx : int) : int =
    match b with
    | Coq_true -> 1 lsl idx
    | Coq_false -> 0 in
  let ascii_to_char (c : Ascii.ascii) : Stdlib.String.t =
    match c with
    | Ascii (b0, b1, b2, b3, b4, b5, b6, b7) -> Stdlib.String.make 1 (Char.chr (
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
