
(* Trusted Shim Procedures *)
include Integers
include Datatypes
include MyInts
include String

(* Helpers for constructing an SMT valuation.  A valuation has two components,
   scalars and memory regions; each is an association list walked by name. *)
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

type coq_ArrayMap =
| AMap of string * CrVal.coq_CrVal CrVal.coq_Array * coq_ArrayMap
| AMap_DNE
let rec coq_TraverseArrayMap (am : coq_ArrayMap) (s : string)
    : CrVal.coq_CrVal CrVal.coq_Array =
  match am with
  | AMap (var_, val_, nxt_) ->
    if (s = var_) then
      val_
    else
      coq_TraverseArrayMap nxt_ s
  | AMap_DNE -> CrVal.Unallocated

(* The names the most recent valuation bound, scalars and regions kept apart.

   [SmtValuation] is a record of two FUNCTIONS, so a valuation carries no
   domain: there is nothing to iterate over and no way to ask it which names it
   knows.  The names exist only here, where the association lists are still in
   hand, so here is where they are kept.

   [print_valuation] takes the NAMES from this table and every VALUE from the
   valuation it is handed, which bounds what a stale table can do.  It can name
   a variable the caller's valuation does not bind -- [coq_TraverseMap] answers
   [UninitVal] for an unknown name, printed as "<unbound>" rather than folded
   into "error", so a stale read is visible -- or it can omit a name entirely.
   It can never attribute a wrong value to a name. *)
let last_valuation_names : (string Stdlib.List.t * string Stdlib.List.t) ref =
  ref ([], [])

let mk_valuation (vm : coq_ValueMap) (am : coq_ArrayMap) : SmtTypes.coq_SmtValuation =
  let rec int_names = function
    | VMap (n, _, rest) -> n :: int_names rest
    | VMap_DNE -> [] in
  let rec arr_names = function
    | AMap (n, _, rest) -> n :: arr_names rest
    | AMap_DNE -> [] in
  last_valuation_names := (int_names vm, arr_names am);
  { SmtTypes.sv_ints = coq_TraverseMap vm;
    SmtTypes.sv_arrs = coq_TraverseArrayMap am }

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

(* A uint64 Coq value from a decimal numeral string (the form Z3 returns). *)
let str_to_coq_uint64 (s : Stdlib.String.t) : BinNums.coq_Z =
  repr (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO (Coq_xO Coq_xH))))))
       (CrTypeIF.BinNums.coq_Z_of_zarith (Z.of_string s))
(* Decimal string of a Coq [Z] (the form Z3's [mk_numeral] expects), overflow-
   free.  [pos_to_str] renders binary, not decimal, so it can't be used here. *)
let coq_Z_to_str (n : BinNums.coq_Z) : Stdlib.String.t =
  Z.to_string (CrTypeIF.BinNums.zarith_of_coq_Z n)

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
  (* Coq's [Ascii b0 .. b7] takes b0 as the LEAST significant bit -- the order
     [coq_str_to_str] above decodes with.  Passing the bits the other way round
     builds a bit-reversed character, so a Coq-built string and an OCaml-built
     one for the same text would not be equal: [coq_TraverseMap] would miss
     every variable, and a name used as a map key would never be found. *)
  Ascii (get_bit code 0, get_bit code 1, get_bit code 2, get_bit code 3,
         get_bit code 4, get_bit code 5, get_bit code 6, get_bit code 7)
let rec str_to_coq_str (s : Stdlib.String.t) : string =
  match s with
  | "" -> EmptyString
  | _ ->
    let c = Stdlib.String.get s 0 in
    let rest = Stdlib.String.sub s 1 (Stdlib.String.length s - 1) in
    String.String ((char_to_ascii c), (str_to_coq_str rest))

(* Seed values are typed u8 (the transformer test programs operate at u8);
   [mk_int] masks the value into the u8 width so the stored value is well-typed. *)
let int_to_crval_u8 (n : int) : CrVal.coq_CrVal =
  CrVal.mk_int CrVal.u8 (int_to_coq_uint64 n)
(* Seed a value at an explicit integer width (used by the cast tests, whose
   source header must carry the cast's [from] type for the cast to type-check). *)
let typed_int_to_crval (ty : CrVal.coq_CrIntType) (n : int) : CrVal.coq_CrVal =
  CrVal.mk_int ty (int_to_coq_uint64 n)
let crval_to_int (v : CrVal.coq_CrVal) : int =
  match v with
  | CrVal.IntVal (x, _) -> coq_Z_to_int x
  | _ -> -1

let get_header (n : int) (s : CrProgramState.coq_ConcreteTransformerState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_Header s (int_to_pos n)
let set_header_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteTransformerState)
    : CrProgramState.coq_ConcreteTransformerState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_Header s (int_to_pos n) (int_to_crval_u8 v)
let set_header_to_typed_int (n : int) (ty : CrVal.coq_CrIntType) (v : int)
    (s : CrProgramState.coq_ConcreteTransformerState)
    : CrProgramState.coq_ConcreteTransformerState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_Header s (int_to_pos n) (typed_int_to_crval ty v)
let get_state (n : int) (s : CrProgramState.coq_ConcreteTransformerState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_State s (int_to_pos n)
let set_state_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteTransformerState)
    : CrProgramState.coq_ConcreteTransformerState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_State s (int_to_pos n) (int_to_crval_u8 v)
let get_ctrl (n : int) (s : CrProgramState.coq_ConcreteTransformerState) : CrVal.coq_CrVal =
  CrVarLike.lookup_varlike CrVarLike.coq_CrVarLike_Ctrl s (int_to_pos n)
let set_ctrl_to_int (n : int) (v : int) (s : CrProgramState.coq_ConcreteTransformerState)
    : CrProgramState.coq_ConcreteTransformerState =
  CrVarLike.update_varlike CrVarLike.coq_CrVarLike_Ctrl s (int_to_pos n) (int_to_crval_u8 v)

let run_program (p : CrDsl.coq_CaracaraProgram) (s : CrProgramState.coq_ConcreteTransformerState)
    : CrProgramState.coq_ConcreteTransformerState =
  CrConcreteSemanticsTransformer.eval_cr_program_concrete p s

let print_state' indentation separator (ps : CrProgramState.coq_ConcreteTransformerState) =
  let header_map = ps.t_header_map in let ctrl_map = ps.t_ctrl_map in let state_map = ps.t_state_map in
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

(* The general concrete state is now a record whose [mod_states] map holds a
   [ModuleState] (transformer or parser) per module.  The test harness seeds and
   reads the *transformer* state of the (transformer) start module, so we unwrap
   [TransformerMod] on the way in and rewrap on the way out. *)
let get_mod_state (key : int) (gcs : CrGeneralProgramState.coq_GeneralConcreteState)
    : CrProgramState.coq_ConcreteTransformerState =
  match Maps.PMap.get (int_to_pos key) gcs.CrGeneralProgramState.mod_states with
  | CrProgramState.TransformerMod ts -> ts
  | CrProgramState.ParserMod _ -> failwith "get_mod_state: expected a transformer module"
  | CrProgramState.DeparserMod _ -> failwith "get_mod_state: expected a transformer module"
let set_mod_state (key : int) (ps : CrProgramState.coq_ConcreteTransformerState)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState)
    : CrGeneralProgramState.coq_GeneralConcreteState =
  CrGeneralProgramState.set_gps_mod_states gcs
    (Maps.PMap.set (int_to_pos key) (CrProgramState.TransformerMod ps)
       gcs.CrGeneralProgramState.mod_states)

(* Render a header map as "h<k>=<v>" entries, sorted by key, comma-separated. *)
let header_map_to_string hmap =
  let key p = coq_Z_to_int (BinNums.Zpos p) in
  let rec to_pairs = function
    | Datatypes.Coq_nil -> []
    | Datatypes.Coq_cons (Datatypes.Coq_pair (k, v), rest) ->
        (key k, crval_to_int v) :: to_pairs rest in
  let pairs =
    to_pairs (Maps.PTree.elements (Datatypes.snd hmap))
    |> Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) in
  Stdlib.String.concat ", "
    (Stdlib.List.map (fun (k, v) -> Printf.sprintf "h%d=%d" k v) pairs)

let print_general_state (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  let rec to_list acc = function
    | Datatypes.Coq_nil -> acc
    | Datatypes.Coq_cons (Datatypes.Coq_pair (mod_id, ms), rest) ->
        to_list ((coq_Z_to_int (BinNums.Zpos mod_id), ms) :: acc) rest
  in
  let pairs = to_list [] (Maps.PTree.elements (Datatypes.snd gcs.CrGeneralProgramState.mod_states)) in
  let sorted = Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs in
  Stdlib.List.iter (fun (id, ms) ->
    Printf.printf "Module %d:\n" id;
    match ms with
    | CrProgramState.TransformerMod ts -> print_state' "  " "" ts
    | CrProgramState.ParserMod ps ->
        print_endline ("  " ^ header_map_to_string ps.CrProgramState.p_header_map)
    | CrProgramState.DeparserMod ps ->
        print_endline ("  " ^ header_map_to_string ps.CrProgramState.p_header_map)) sorted

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

let print_malformed_gprog p name =
  match CrDslProperties.well_formed_general_programb p with
  | Datatypes.Coq_false -> Printf.printf "(%s) malformed\n" name
  | Datatypes.Coq_true -> ()

(* ------------------------------------------------------------------ *)
(* Parser test helpers: build a packet from bytes, run the parser FSM, *)
(* and render the resulting header map.                                *)

let rec coq_list_of_list = function
  | [] -> Datatypes.Coq_nil
  | x :: xs -> Datatypes.Coq_cons (x, coq_list_of_list xs)

let rec int_to_coq_nat (n : int) : Datatypes.nat =
  if n <= 0 then Datatypes.O else Datatypes.S (int_to_coq_nat (n - 1))

let rec coq_nat_to_int (n : Datatypes.nat) : int =
  match n with Datatypes.O -> 0 | Datatypes.S m -> 1 + coq_nat_to_int m

(* A Coq [list Header] from header ids (Header extracts to positive). *)
let headers_of_ints (ns : int Stdlib.List.t) : CrIdentifiers.coq_Header Datatypes.list =
  coq_list_of_list (Stdlib.List.map int_to_pos ns)

(* MSB-first 8 bits of byte [b] as Coq bools (in a native OCaml list). *)
let byte_bits (b : int) : Datatypes.bool Stdlib.List.t =
  Stdlib.List.init 8 (fun k ->
    if (b lsr (7 - k)) land 1 = 1 then Datatypes.Coq_true else Datatypes.Coq_false)

(* The MSB-first bytes concatenated into a Coq [bool list] packet. *)
let packet_of_bytes (bytes : int Stdlib.List.t) : Datatypes.bool Datatypes.list =
  coq_list_of_list (Stdlib.List.concat_map byte_bits bytes)

let mk_parser_state (packet : Datatypes.bool Datatypes.list)
    : CrProgramState.coq_ConcreteParserState =
  { CrProgramState.p_header_map = Maps.PMap.init (CrVal.UninitVal);
    p_packet = packet;
    p_cursor = Datatypes.O }

let run_parser (p : CrParser.coq_Parser) (bytes : int Stdlib.List.t)
    : CrGeneralProgramState.coq_ConcParserResult option =
  CrConcreteSemanticsParser.eval_parser_concrete p (mk_parser_state (packet_of_bytes bytes))

(* Seed the network's input packet (the shared bit map) from a byte list.  This
   threads through the modules: the start module parses it, and each module hands
   the residual (unparsed) bits to its downstream neighbours. *)
let set_net_packet (bytes : int Stdlib.List.t)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState)
    : CrGeneralProgramState.coq_GeneralConcreteState =
  { gcs with CrGeneralProgramState.sh_read_tape = packet_of_bytes bytes }

(* Render the network's output packet -- the write tape the sink deparser left
   behind -- as MSB-first bytes.  A trailing partial byte is rendered from the
   bits that are there. *)
let print_net_output (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  let bit_val = function Datatypes.Coq_true -> 1 | Datatypes.Coq_false -> 0 in
  let rec pack acc cur n = function
    | [] -> Stdlib.List.rev (if n = 0 then acc else cur :: acc)
    | b :: rest ->
      let cur = (cur lsl 1) lor bit_val b in
      if n + 1 = 8 then pack (cur :: acc) 0 0 rest else pack acc cur (n + 1) rest in
  let bits = listify_coq_list gcs.CrGeneralProgramState.sh_write_tape in
  let bytes = pack [] 0 0 bits in
  (* The bit count is printed because the bytes alone cannot tell an EMPTY
     packet from one zero byte -- both render as no visible digits or as "0"
     depending on how you squint -- and that is exactly the pair the
     both-rejected trap produces.  A deparser is total, so a header holding no
     integer emits its full width as zeros rather than emitting nothing; a
     fixture that cannot see the difference would let a program that emits
     nothing and a program that emits zeros agree. *)
  Printf.printf "[%s] %db\n"
    (Stdlib.String.concat ", " (Stdlib.List.map string_of_int bytes))
    (Stdlib.List.length bits)

(* How many bits of the input packet the network consumed, summed over its
   parsers. *)
let net_bits_read (gcs : CrGeneralProgramState.coq_GeneralConcreteState) : int =
  crval_to_int gcs.CrGeneralProgramState.sh_bits_read

let print_net_bits_read (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  Printf.printf "bits_read=%d\n" (net_bits_read gcs)

(* The three outcomes a network run can have, kept apart.  A rejected packet is
   now a STATE carrying [gps_valid = false]; [None] means the network did not
   run to completion at all (out of fuel, a dangling edge, a module state of the
   wrong kind).  Those two used to be the same [None], so a packet the parser
   refused was indistinguishable from a program that could not run -- and the
   "both rejected" case of the equivalence statement was unreachable for any
   network whose parser is not also its sink. *)
let print_net_outcome (r : CrGeneralProgramState.coq_GeneralConcreteState option) =
  match r with
  | None -> print_endline "incomplete (None)"
  | Some s ->
    Printf.printf "%s, bits_read=%d, residual=%db\n"
      (match s.CrGeneralProgramState.gps_valid with
       | Datatypes.Coq_true -> "accepted"
       | Datatypes.Coq_false -> "rejected")
      (net_bits_read s)
      (Stdlib.List.length (listify_coq_list s.CrGeneralProgramState.sh_read_tape))

(* The unconsumed tail each parser module ended holding.  The module-local state
   used to be rebuilt from the packet the parser was HANDED, at the cursor it
   STARTED from, so this printed the full input length for every parser no
   matter how much it had consumed. *)
let print_parser_residuals (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  let rec to_list acc = function
    | Datatypes.Coq_nil -> acc
    | Datatypes.Coq_cons (Datatypes.Coq_pair (mod_id, ms), rest) ->
        to_list ((coq_Z_to_int (BinNums.Zpos mod_id), ms) :: acc) rest in
  let pairs = to_list [] (Maps.PTree.elements (Datatypes.snd gcs.CrGeneralProgramState.mod_states)) in
  Stdlib.List.iter (fun (id, ms) ->
    match ms with
    | CrProgramState.ParserMod ps ->
        Printf.printf "Module %d: residual=%db, cursor=%d\n" id
          (Stdlib.List.length (listify_coq_list ps.CrProgramState.p_packet))
          (coq_nat_to_int ps.CrProgramState.p_cursor)
    | _ -> ())
    (Stdlib.List.sort (fun (a, _) (b, _) -> Stdlib.compare a b) pairs)

(* ------------------------------------------------------------------ *)
(* Memory *)
let mem_cell_key (off : int) : BinNums.positive = int_to_pos (off + 1)

let get_net_mem_region (region : int)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState)
    : CrVal.coq_CrVal CrVal.coq_Array =
  Maps.PMap.get (int_to_pos region) gcs.CrGeneralProgramState.sh_mem

(* Seed a width-[ty] value at [off] of a declared region.  Goes through
   [CrVal.st_val] rather than writing one cell, so a test seeds memory exactly
   the way a [StoreOp] would: [it_bytes ty] little-endian byte cells.

   The region must already be declared on the program --
   [init_general_concrete_state] allocates it at its declared length -- since
   writing into an unallocated region is exactly what the semantics refuses to
   do.  (The name predates the widening to [ty]; it seeds a value, not a cell.) *)
let set_net_mem_cell (region : int) (off : int) (ty : CrVal.coq_CrIntType) (v : int)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState)
    : CrGeneralProgramState.coq_GeneralConcreteState =
  match get_net_mem_region region gcs with
  | CrVal.Unallocated ->
      failwith (Printf.sprintf "set_net_mem_cell: region %d is not declared" region)
  | CrVal.Allocated _ as arr ->
      let arr' = CrVal.st_val ty arr
                   (CrVal.mk_int CrVal.u64 (int_to_coq_uint64 off))
                   (typed_int_to_crval ty v) in
      { gcs with CrGeneralProgramState.sh_mem =
          Maps.PMap.set (int_to_pos region) arr' gcs.CrGeneralProgramState.sh_mem }

(* Render a region's cells over its declared length: "-" for a cell that was
   never written, "!" for one holding a non-integer (an ErrorVal a failed load
   or a type-mismatched store left behind). *)
let print_net_mem_region (region : int)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  match get_net_mem_region region gcs with
  | CrVal.Unallocated -> Printf.printf "mem%d=<undeclared>\n" region
  | CrVal.Allocated blk ->
      let len = coq_Z_to_int blk.CrVal.arr_len in
      let cell i =
        match Maps.PMap.get (mem_cell_key i) blk.CrVal.arr_bytes with
        | CrVal.Uninit -> "-"
        | CrVal.Init (CrVal.IntVal (x, _)) -> string_of_int (coq_Z_to_int x)
        | CrVal.Init _ -> "!" in
      Printf.printf "mem%d=[%s]\n" region
        (Stdlib.String.concat ", " (Stdlib.List.init len cell))

(* How many bytes of [region] the run required -- one past the highest byte it
   touched, in bounds or not, so it is a COUNT and not an offset.  The memory
   analogue of [net_bits_read], and comparable for the same reason. *)
let print_net_mem_extent (region : int)
    (gcs : CrGeneralProgramState.coq_GeneralConcreteState) =
  Printf.printf "extent%d=%d\n" region
    (crval_to_int (Maps.PMap.get (int_to_pos region)
                     gcs.CrGeneralProgramState.sh_mem_extent))

(* Render the parsed headers ("h<k>=<v>", sorted), or "Reject" on parse failure. *)
(* Three outcomes, not two.  [None] no longer means "rejected" -- it means the
   run did not COMPLETE, which after [ParserWellFormed] is something only an
   ill-formed parser can do (out of fuel, or a transition into a state with no
   definition).  A rejected packet is [Some] with [pr_accept = false].  They are
   printed differently on purpose: a test that cannot tell them apart would let
   an ill-formed parser masquerade as one that simply rejects. *)
let print_parser_result (r : CrGeneralProgramState.coq_ConcParserResult option) =
  match r with
  | None -> print_endline "Incomplete"
  | Some res ->
    (match res.CrGeneralProgramState.pr_accept with
     | Datatypes.Coq_false -> print_endline "Reject"
     | Datatypes.Coq_true ->
       print_endline (header_map_to_string res.CrGeneralProgramState.pr_headers))

(* Read a whole network program from a file.  The sexp encoding is the one
   [CrTypeIF] derives, with three departures that make it writable from outside
   this tree (see the header comment there): numbers are decimal, a select
   case's [sc_pattern] is a [0b] literal, and [net_edges] is an explicit edge
   list rather than a closure.  Each of the first two also accepts the derived
   constructor form, so an older dump still loads.
   [~/proj/ect/bpf_to_ir] emits exactly this. *)
let load_general_program (f : Stdlib.String.t)
    : CrModule.coq_GeneralCaracaraProgram =
  let x = open_in f in
  let len = in_channel_length x in
  let str = really_input_string x len in
  close_in x;
  str |> Sexplib.Sexp.of_string
      |> CrTypeIF.CrModule.coq_GeneralCaracaraProgram_of_sexp

let find_modprog (name : Stdlib.String.t) =
  match TestModulePrograms.lookup_mod_test_program (str_to_coq_str name) with
  | Some p -> p
  | None -> failwith ("find_modprog: no module test program named " ^ name)

(* ------------------------------------------------------------------ *)
(* Printing a solver valuation.

   This is the counterexample [NotEquivalent] carries, and it used to be
   printed by [Z3Solver.sat_check] as a side effect of solving.  It is a
   caller's choice, not the solver's: which satisfying assignment Z3 returns is
   not a function of the query -- it shifts with whatever else the process has
   already solved -- so a test that pins the bytes is pinning something Z3 does
   not promise, while the VERDICT it is actually asserting is stable.  Hence
   printing on demand, from [EqCheck], where a human is going to read it. *)

let crwidth_bits (t : CrVal.coq_CrIntType) : int =
  match t with CrVal.W8 -> 8 | CrVal.W16 -> 16 | CrVal.W32 -> 32 | CrVal.W64 -> 64

(* One region's cells over its declared length.  "-" is [UninitVal] and "err"
   is [ErrorVal] -- both are ordinary contents, not failures: [byte_of_val]
   sends every non-[IntVal] to [ErrorVal], so storing an unwritten header fills
   its cells with it.  "?" is a key the map never bound, which for a valuation
   means the model gave no numeral for that cell. *)
let region_cells_to_string (blk : CrVal.coq_CrVal CrVal.coq_MemBlock) : Stdlib.String.t =
  let len = coq_Z_to_int blk.CrVal.arr_len in
  let cell i =
    match Maps.PMap.get (mem_cell_key i) blk.CrVal.arr_bytes with
    | CrVal.Init (CrVal.IntVal (x, ty)) ->
        Printf.sprintf "%s:u%d" (coq_Z_to_str x) (crwidth_bits ty)
    | CrVal.Init CrVal.UninitVal -> "-"
    | CrVal.Init CrVal.ErrorVal -> "err"
    | CrVal.Uninit -> "?" in
  Stdlib.String.concat ", " (Stdlib.List.init len cell)

let print_valuation (v : SmtTypes.coq_SmtValuation) =
  let (int_names, arr_names) = !last_valuation_names in
  (* Scalars before regions, each ascending by name -- the order
     [StringMap.bindings] used to hand the printer, so a dump is comparable
     across runs even though its CONTENTS are not stable. *)
  let sorted ns =
    Stdlib.List.sort_uniq Stdlib.compare (Stdlib.List.map coq_str_to_str ns) in
  print_endline "┌ SAT Valuation";
  Stdlib.List.iter (fun name ->
    match v.SmtTypes.sv_ints (str_to_coq_str name) with
    | CrVal.IntVal (x, ty) ->
        Printf.printf "| var( %s ) : u%d := %s\n" name (crwidth_bits ty) (coq_Z_to_str x)
    (* [eval_smt_arith] coerces every non-[IntVal] a valuation gives a scalar to
       [ErrorVal] -- matching the [ite (tag_is_int t) t tag_err] the lowering
       wraps a free tag in -- so "error" is what this variable will be READ as,
       whatever the model called it.  ([SmtArrSel] has no such coercion, which
       is why a region's cells above must reconstruct exactly.) *)
    | CrVal.ErrorVal -> Printf.printf "| var( %s ) := error\n" name
    | CrVal.UninitVal -> Printf.printf "| var( %s ) := <unbound>\n" name)
    (sorted int_names);
  Stdlib.List.iter (fun name ->
    match v.SmtTypes.sv_arrs (str_to_coq_str name) with
    | CrVal.Allocated blk ->
        Printf.printf "| mem( %s ) : len=%d := [%s]\n" name
          (coq_Z_to_int blk.CrVal.arr_len) (region_cells_to_string blk)
    | CrVal.Unallocated -> Printf.printf "| mem( %s ) := <unbound>\n" name)
    (sorted arr_names);
  print_endline "└"
