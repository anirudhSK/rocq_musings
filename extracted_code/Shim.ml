
(* Trusted Shim Procedures *)
include Integers
include Datatypes
include MyInts
include String

(* Helpers for constructing an SMT valuation *)
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

(* Helpers for casting between ocaml and rocq types *)
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

let rec pos_to_str (n : BinNums.positive) : Stdlib.String.t =
  match n with
  | Coq_xH -> "1"
  | Coq_xO n_ -> (pos_to_str n_) ^ "0"
  | Coq_xI n_ -> (pos_to_str n_) ^ "1"
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

let int_to_crval (n : int) : CrVal.coq_CrVal =
  CrVal.IntVal (CrVal.CrInt (int_to_coq_uint64 n))
let crval_to_int (v : CrVal.coq_CrVal) : int =
  match v with
  | CrVal.IntVal (CrVal.CrInt x) -> coq_Z_to_int x
  | _ -> -1

let get_header (n : int) (s : CrProgramState.coq_ConcreteState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_Header s (int_to_pos n)
let set_header_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteState)
    : CrProgramState.coq_ConcreteState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_Header s (int_to_pos n) (int_to_crval v)
let get_state (n : int) (s : CrProgramState.coq_ConcreteState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_State s (int_to_pos n)
let set_state_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteState)
    : CrProgramState.coq_ConcreteState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_State s (int_to_pos n) (int_to_crval v)
let get_ctrl (n : int) (s : CrProgramState.coq_ConcreteState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_Ctrl s (int_to_pos n)
let set_ctrl_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteState)
    : CrProgramState.coq_ConcreteState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_Ctrl s (int_to_pos n) (int_to_crval v)

let run_program (p : CrDsl.coq_CaracaraProgram) (s : CrProgramState.coq_ConcreteState)
    : CrProgramState.coq_ConcreteState =
  CrConcreteSemanticsTransformer.eval_cr_program_concrete p s

let print_state' indentation separator (ps : CrProgramState.coq_ConcreteState) =
  let header_map = ps.header_map in let ctrl_map = ps.ctrl_map in let state_map = ps.state_map in
  let header_tree = Datatypes.snd header_map in let ctrl_tree = Datatypes.snd ctrl_map in let state_tree = Datatypes.snd state_map in
  let headers = Maps.PTree.elements header_tree in let ctrls = Maps.PTree.elements ctrl_tree in let states = Maps.PTree.elements state_tree in
  let key p = coq_Z_to_int (BinNums.Zpos p) in
  let rec to_pairs = function
    | Datatypes.Coq_nil -> []
    | Datatypes.Coq_cons (Datatypes.Coq_pair (k, v), rest) ->
        (key k, crval_to_int v) :: to_pairs rest
  in
  let render prefix coq_list =
    Stdlib.String.concat "" [
      indentation;
      (coq_list
      |> to_pairs
      |> Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b)
      |> Stdlib.List.map (fun (k, v) -> Printf.sprintf "%s%d=%d" prefix k v)
      |> Stdlib.String.concat ", ")]
  in
  let groups = Stdlib.List.filter (fun s -> s <> "")
    [render "h" headers; render "c" ctrls; render "s" states]
  in
  print_endline (Stdlib.String.concat separator groups)

let print_state = print_state' "" "\n"

let start_mod_id (p : CrModule.coq_GeneralCaracaraProgram) : int =
  let net = CrModule.get_network_from_general p in
  coq_Z_to_int (BinNums.Zpos
    (CrIdentifiers.coq_Posesque_ModuleName.unwrap net.CrModule.start_module))

let get_mod_state (key : int) (gcs : CrProgramState.coq_ConcreteState Maps.PMap.t)
    : CrProgramState.coq_ConcreteState =
  Maps.PMap.get (int_to_pos key) gcs
let set_mod_state (key : int) (ps : CrProgramState.coq_ConcreteState)
    (gcs : CrProgramState.coq_ConcreteState Maps.PMap.t)
    : CrProgramState.coq_ConcreteState Maps.PMap.t =
  Maps.PMap.set (int_to_pos key) ps gcs

let print_general_state (gcs : CrProgramState.coq_ConcreteState Maps.PMap.t) =
  let rec to_list acc = function
    | Datatypes.Coq_nil -> acc
    | Datatypes.Coq_cons (Datatypes.Coq_pair (mod_id, local_state), rest) ->
        to_list ((coq_Z_to_int (BinNums.Zpos mod_id), local_state) :: acc) rest
  in
  let pairs = to_list [] (Maps.PTree.elements (Datatypes.snd gcs)) in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.iter (fun (id, local_state) ->
    Printf.printf "Module %d:\n" id;
    print_state' "  " "" local_state) sorted

let listify_coq_list (a_list : 'a Datatypes.list) : 'a Stdlib.List.t =
  let rec aux acc = function
  | Datatypes.Coq_nil -> Stdlib.List.rev acc
  | Datatypes.Coq_cons (h, t) -> aux (h :: acc) t
  in
  aux [] a_list

let print_malformed_prog p pid =
  match CrDslProperties.well_formed_programb p with
  | Datatypes.Coq_false -> Printf.printf "(%d) malformed\n" pid
  | Datatypes.Coq_true -> ()

let print_malformed_gprog p pid =
  match CrDslProperties.well_formed_general_programb p with
  | Datatypes.Coq_false -> Printf.printf "(%d) malformed\n" pid
  | Datatypes.Coq_true -> ()
