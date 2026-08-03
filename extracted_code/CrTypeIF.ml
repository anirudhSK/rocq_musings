(* Destructure a sexp record into a field lookup.  Shared by the two
   hand-written record converters below ([CrParser.coq_SelectCase] and
   [CrModule.coq_ModuleNetwork]); [where] names the caller in the error. *)
let sexp_record_field (where : string) (s : Sexplib.Sexp.t)
  : string -> Sexplib.Sexp.t =
  let fields =
    match s with
    | Sexplib.Sexp.List l ->
      Stdlib.List.filter_map
        (function Sexplib.Sexp.List [Sexplib.Sexp.Atom k; v] -> Some (k, v) | _ -> None)
        l
    | Sexplib.Sexp.Atom _ ->
      Sexplib.Conv.of_sexp_error (where ^ ": expected a record") s in
  fun name ->
    match Stdlib.List.assoc_opt name fields with
    | Some v -> v
    | None -> Sexplib.Conv.of_sexp_error (where ^ ": missing field " ^ name) s

module BinNums = struct
  include BinNums
  type positive = [%import: BinNums.positive]
  [@@deriving sexp]
  type coq_Z = [%import: BinNums.coq_Z]
  [@@deriving sexp]

(* Arbitrary precision matters here: a [uint64] operand can exceed OCaml's
   63-bit native int, so the conversions go through Zarith rather than
   [int_of_string]. *)
  let rec positive_of_zarith (n : Z.t) : positive =
    if Z.equal n Z.one then Coq_xH
    else if Z.equal (Z.logand n Z.one) Z.zero
    then Coq_xO (positive_of_zarith (Z.shift_right n 1))
    else Coq_xI (positive_of_zarith (Z.shift_right n 1))
  let rec zarith_of_positive (p : positive) : Z.t =
    match p with
    | Coq_xH -> Z.one
    | Coq_xO p' -> Z.shift_left (zarith_of_positive p') 1
    | Coq_xI p' -> Z.succ (Z.shift_left (zarith_of_positive p') 1)
  let zarith_of_coq_Z (z : coq_Z) : Z.t =
    match z with
    | Z0 -> Z.zero
    | Zpos p -> zarith_of_positive p
    | Zneg p -> Z.neg (zarith_of_positive p)
  let coq_Z_of_zarith (n : Z.t) : coq_Z =
    match Z.sign n with
    | 0 -> Z0
    | s when s > 0 -> Zpos (positive_of_zarith n)
    | _ -> Zneg (positive_of_zarith (Z.neg n))
  let decimal_of_sexp (s : Sexplib.Sexp.t) : Z.t option =
    match s with
    | Sexplib.Sexp.Atom a -> (try Some (Z.of_string a) with _ -> None)
    | Sexplib.Sexp.List _ -> None
  let coq_positive_of_sexp = positive_of_sexp
  let positive_of_sexp (s : Sexplib.Sexp.t) : positive =
    match decimal_of_sexp s with
    | Some n when Z.gt n Z.zero -> positive_of_zarith n
    | _ -> coq_positive_of_sexp s
  let sexp_of_positive (p : positive) : Sexplib.Sexp.t =
    Sexplib.Sexp.Atom (Z.to_string (zarith_of_positive p))
  let coq_coq_Z_of_sexp = coq_Z_of_sexp
  let coq_Z_of_sexp (s : Sexplib.Sexp.t) : coq_Z =
    match decimal_of_sexp s with
    | Some n -> coq_Z_of_zarith n
    | None -> coq_coq_Z_of_sexp s
  let sexp_of_coq_Z (z : coq_Z) : Sexplib.Sexp.t =
    Sexplib.Sexp.Atom (Z.to_string (zarith_of_coq_Z z))
end
module Datatypes = struct
  include Datatypes
  type nat = [%import: Datatypes.nat]
  [@@deriving sexp]

  let rec nat_of_int (n : int) : nat = if n <= 0 then O else S (nat_of_int (n - 1))
  let rec int_of_nat (n : nat) : int = match n with O -> 0 | S n' -> 1 + int_of_nat n'
  let coq_nat_of_sexp = nat_of_sexp
  let nat_of_sexp (s : Sexplib.Sexp.t) : nat =
    match s with
    | Sexplib.Sexp.Atom a ->
      (match int_of_string_opt a with
       | Some n when n >= 0 -> nat_of_int n
       | _ -> coq_nat_of_sexp s)
    | Sexplib.Sexp.List _ -> coq_nat_of_sexp s
  let sexp_of_nat (n : nat) : Sexplib.Sexp.t =
    Sexplib.Sexp.Atom (string_of_int (int_of_nat n))

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
  type uint64 = [%import: MyInts.uint64]
  [@@deriving sexp]
end
module CrVal = struct
include CrVal
type coq_CrWidth = [%import: CrVal.coq_CrWidth]
[@@deriving sexp]
type coq_CrIntType = [%import: CrVal.coq_CrIntType]
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
  type coq_MemRegion = [%import: CrIdentifiers.coq_MemRegion]
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

  (* A [list bool] prints as the binary literal it denotes: [0b00000001] is
     [[false;...;false;true]].  The list is MSB-first -- [CrParser.bits_to_Z]
     folds the head in as the high bit -- so the digits read left to right in
     list order.  Like [positive]/[nat]/[Z] above, this EMITS the sugar and
     ACCEPTS either it or the derived [Coq_cons] chain, so an existing dump
     still loads.

     Leading zeros are kept, and the empty list prints as [0b].  A pattern's
     width is not semantically load-bearing -- [select_case_matches_concrete]
     compares [bits_to_Z] of it against the slice, so [0b0011] and [0b11] mean
     the same thing -- but preserving the digit count is what makes the dump a
     faithful round-trip rather than a normalising one. *)
  let sexp_of_bits (bs : Datatypes.bool Datatypes.list) : Sexplib.Sexp.t =
    let buf = Buffer.create 16 in
    Buffer.add_string buf "0b";
    let rec go = function
      | Datatypes.Coq_nil -> ()
      | Datatypes.Coq_cons (b, rest) ->
        Buffer.add_char buf
          (match b with Datatypes.Coq_true -> '1' | Datatypes.Coq_false -> '0');
        go rest in
    go bs;
    Sexplib.Sexp.Atom (Buffer.contents buf)
  let bits_of_sexp (s : Sexplib.Sexp.t) : Datatypes.bool Datatypes.list =
    match s with
    | Sexplib.Sexp.Atom a
      when Stdlib.String.length a >= 2 && Stdlib.String.sub a 0 2 = "0b" ->
      let rec go i acc =
        if i < 2 then acc
        else
          let b =
            match Stdlib.String.get a i with
            | '0' -> Datatypes.Coq_false
            | '1' -> Datatypes.Coq_true
            | _ ->
              Sexplib.Conv.of_sexp_error
                "CrTypeIF.bits_of_sexp: a 0b literal takes only the digits 0 and 1" s in
          go (i - 1) (Datatypes.Coq_cons (b, acc)) in
      go (Stdlib.String.length a - 1) Datatypes.Coq_nil
    | _ -> Datatypes.list_of_sexp Datatypes.bool_of_sexp s

  (* Hand-written rather than derived, so that [sc_pattern] goes through the
     [0b] sugar above.  The field names match what the derived record converter
     would have produced. *)
  type coq_SelectCase = CrParser.coq_SelectCase
  let sexp_of_coq_SelectCase (c : coq_SelectCase) : Sexplib.Sexp.t =
    let field name v = Sexplib.Sexp.List [Sexplib.Sexp.Atom name; v] in
    Sexplib.Sexp.List [
      field "sc_header" (CrIdentifiers.sexp_of_coq_Header c.CrParser.sc_header);
      field "sc_start_index" (Datatypes.sexp_of_nat c.CrParser.sc_start_index);
      field "sc_end_index" (Datatypes.sexp_of_nat c.CrParser.sc_end_index);
      field "sc_pattern" (sexp_of_bits c.CrParser.sc_pattern);
      field "sc_target" (sexp_of_coq_ParserTarget c.CrParser.sc_target);
    ]
  let coq_SelectCase_of_sexp (s : Sexplib.Sexp.t) : coq_SelectCase =
    let field = sexp_record_field "CrTypeIF.coq_SelectCase_of_sexp" s in
    { CrParser.sc_header = CrIdentifiers.coq_Header_of_sexp (field "sc_header");
      CrParser.sc_start_index = Datatypes.nat_of_sexp (field "sc_start_index");
      CrParser.sc_end_index = Datatypes.nat_of_sexp (field "sc_end_index");
      CrParser.sc_pattern = bits_of_sexp (field "sc_pattern");
      CrParser.sc_target = coq_ParserTarget_of_sexp (field "sc_target") }
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

  type coq_Connections = CrDsl.coq_Connections
  type edge_list = (BinNums.positive * BinNums.positive) list
  let edges_of_sexp (s : Sexplib.Sexp.t) : edge_list =
    let pair = function
      | Sexplib.Sexp.List [a; b] ->
        (BinNums.positive_of_sexp a, BinNums.positive_of_sexp b)
      | s ->
        Sexplib.Conv.of_sexp_error
          "CrTypeIF.edges_of_sexp: expected an (src dst) pair" s in
    match s with
    | Sexplib.Sexp.List l -> Stdlib.List.map pair l
    | Sexplib.Sexp.Atom _ ->
      Sexplib.Conv.of_sexp_error
        "CrTypeIF.edges_of_sexp: expected a list of (src dst) pairs" s
  let sexp_of_edges (l : edge_list) : Sexplib.Sexp.t =
    Sexplib.Sexp.List
      (Stdlib.List.map
         (fun (a, b) ->
            Sexplib.Sexp.List [BinNums.sexp_of_positive a; BinNums.sexp_of_positive b])
         l)
  let connections_of_edges (l : edge_list) : coq_Connections =
    fun src dst ->
      if Stdlib.List.exists (fun (a, b) -> a = src && b = dst) l
      then Datatypes.Coq_true else Datatypes.Coq_false
  let edges_of_connections (names : BinNums.positive list) (c : coq_Connections)
    : edge_list =
    Stdlib.List.concat_map
      (fun s ->
         Stdlib.List.filter_map
           (fun d ->
              match c s d with
              | Datatypes.Coq_true -> Some (s, d)
              | Datatypes.Coq_false -> None)
           names)
      names
end
type coq_CaracaraProgram = CrDsl.coq_CaracaraProgram
let sexp_of_coq_CaracaraProgram = CrDsl.sexp_of_coq_CaracaraProgram
let coq_CaracaraProgram_of_sexp = CrDsl.coq_CaracaraProgram_of_sexp

module CrModule = struct
  include CrModule

  (* Hand-written rather than derived, because of [net_edges]; see
     [CrDsl.coq_Connections] above.  The field names match what the derived
     record converter would have produced, so a dumped network and a
     hand-written one look the same apart from the edge list. *)
  type coq_ModuleNetwork = CrModule.coq_ModuleNetwork
  let mod_names (ms : CrDsl.coq_CrModule Datatypes.list) : BinNums.positive list =
    let rec go acc = function
      | Datatypes.Coq_nil -> Stdlib.List.rev acc
      | Datatypes.Coq_cons (m, rest) -> go (CrModule.get_mod_name m :: acc) rest in
    go [] ms
  let sexp_of_coq_ModuleNetwork (n : coq_ModuleNetwork) : Sexplib.Sexp.t =
    let modules = n.CrModule.net_modules in
    Sexplib.Sexp.List [
      Sexplib.Sexp.List [Sexplib.Sexp.Atom "net_modules";
                         Datatypes.sexp_of_list CrDsl.sexp_of_coq_CrModule modules];
      Sexplib.Sexp.List [Sexplib.Sexp.Atom "net_edges";
                         CrDsl.sexp_of_edges
                           (CrDsl.edges_of_connections (mod_names modules)
                              n.CrModule.net_edges)];
      Sexplib.Sexp.List [Sexplib.Sexp.Atom "start_module";
                         CrIdentifiers.sexp_of_coq_ModuleName n.CrModule.start_module];
    ]
  let coq_ModuleNetwork_of_sexp (s : Sexplib.Sexp.t) : coq_ModuleNetwork =
    let field = sexp_record_field "CrTypeIF.coq_ModuleNetwork_of_sexp" s in
    { CrModule.net_modules =
        Datatypes.list_of_sexp CrDsl.coq_CrModule_of_sexp (field "net_modules");
      CrModule.net_edges =
        CrDsl.connections_of_edges (CrDsl.edges_of_sexp (field "net_edges"));
      CrModule.start_module =
        CrIdentifiers.coq_ModuleName_of_sexp (field "start_module") }

  type coq_MemRegionDecl = [%import: CrModule.coq_MemRegionDecl]
  [@@deriving sexp]
  type coq_GeneralCaracaraProgram = [%import: CrModule.coq_GeneralCaracaraProgram]
  [@@deriving sexp]
end
