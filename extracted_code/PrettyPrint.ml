(*
 * PrettyPrint -- render a .ir file's sexp as human-readable text.
 *
 *   pretty_print <prog.ir>        a CrModule.coq_GeneralCaracaraProgram
 *   pretty_print --mod <mod.ir>   a single CrDsl.coq_CrModule (Parser-,
 *                                 Deparser-, or TransformerModule)
 *
 * This is a display tool only -- it does not round-trip; `dump_sexp` /
 * `run_net` are the sexp-faithful and semantics-faithful views of a .ir file,
 * respectively.  Identifiers are rendered as <prefix><uid> using the same
 * prefixes Shim.print_state' uses (h = header, s = transformer state var,
 * c = ctrl, plus m = module, r = mem region, l = parser state label, which
 * have no state-printing precedent to match).
 *)

let pos_id (p : BinNums.positive) : int =
  Shim.coq_Z_to_int (BinNums.Zpos p)
let nat_int (n : Datatypes.nat) : int = Shim.coq_nat_to_int n
(* [MyInts.uint64] is transparently [BinNums.coq_Z] (see MyInts.mli / Integers.mli),
   so [Shim.coq_Z_to_str], written for [coq_Z], applies directly. *)
let u64_str (n : MyInts.uint64) : string = Shim.coq_Z_to_str n

let hdr (h : CrIdentifiers.coq_Header) : string = Printf.sprintf "h%d" (pos_id h)
let st (s : CrIdentifiers.coq_State) : string = Printf.sprintf "s%d" (pos_id s)
let ctrl (c : CrIdentifiers.coq_Ctrl) : string = Printf.sprintf "c%d" (pos_id c)
let modn (m : CrIdentifiers.coq_ModuleName) : string = Printf.sprintf "m%d" (pos_id m)
let region (r : CrIdentifiers.coq_MemRegion) : string = Printf.sprintf "r%d" (pos_id r)
let label (l : CrIdentifiers.coq_ParserStateLabel) : string = Printf.sprintf "l%d" (pos_id l)

(* [CrVal.coq_CrIntType] is transparently [CrVal.coq_CrWidth] (singleton
   record, constructor [mkCrIntType] erased), so no [it_width] projection. *)
let ty_str (t : CrVal.coq_CrIntType) : string =
  match t with
  | CrVal.W8 -> "u8" | CrVal.W16 -> "u16" | CrVal.W32 -> "u32" | CrVal.W64 -> "u64"

let binop_str (f : CrTransformer.coq_BinaryOp) : string =
  match f with
  | CrTransformer.AddOp -> "+" | CrTransformer.SubOp -> "-"
  | CrTransformer.AndOp -> "&" | CrTransformer.OrOp -> "|"
  | CrTransformer.XorOp -> "^" | CrTransformer.MulOp -> "*"
  | CrTransformer.DivOp -> "/" | CrTransformer.ModOp -> "%"

let cmpop_str (o : CrTransformer.coq_CmpOp) : string =
  match o with
  | CrTransformer.CmpEq -> "==" | CrTransformer.CmpGt -> ">" | CrTransformer.CmpLt -> "<"

let operand_str (o : CrTransformer.coq_Operand) : string =
  match o with
  | CrTransformer.OpCtrlPlane c -> ctrl c
  | CrTransformer.OpHeader h -> hdr h
  | CrTransformer.OpConst n -> u64_str n
  | CrTransformer.OpState s -> st s

let matchvalue_str (v : CrTransformer.coq_MatchValue) : string =
  match v with
  | CrTransformer.MatchConst (k, ty) -> Printf.sprintf "%s:%s" (u64_str k) (ty_str ty)
  | CrTransformer.MatchHeader h -> hdr h

let matchpattern_str (mp : CrTransformer.coq_MatchPattern) : string =
  match Shim.listify_coq_list mp with
  | [] -> "true"
  | conds ->
    conds
    |> Stdlib.List.map (fun (Datatypes.Coq_pair (Datatypes.Coq_pair (h, op), mv)) ->
         Printf.sprintf "%s %s %s" (hdr h) (cmpop_str op) (matchvalue_str mv))
    |> Stdlib.String.concat " && "

let hdrop_str (op : CrTransformer.coq_HdrOp) : string =
  match op with
  | CrTransformer.StatefulOp (f, ty, a1, a2, target) ->
    Printf.sprintf "%s := %s %s %s : %s"
      (st target) (operand_str a1) (binop_str f) (operand_str a2) (ty_str ty)
  | CrTransformer.StatelessOp (f, ty, a1, a2, target) ->
    Printf.sprintf "%s := %s %s %s : %s"
      (hdr target) (operand_str a1) (binop_str f) (operand_str a2) (ty_str ty)
  | CrTransformer.CastStateOp (from_ty, to_ty, arg, target) ->
    Printf.sprintf "%s := cast(%s : %s -> %s)"
      (st target) (operand_str arg) (ty_str from_ty) (ty_str to_ty)
  | CrTransformer.CastHeaderOp (from_ty, to_ty, arg, target) ->
    Printf.sprintf "%s := cast(%s : %s -> %s)"
      (hdr target) (operand_str arg) (ty_str from_ty) (ty_str to_ty)
  | CrTransformer.LoadOp (ty, r, off, target) ->
    Printf.sprintf "%s := load %s[%s] : %s" (hdr target) (region r) (operand_str off) (ty_str ty)
  | CrTransformer.StatefulLoadOp (ty, r, off, target) ->
    Printf.sprintf "%s := load %s[%s] : %s" (st target) (region r) (operand_str off) (ty_str ty)
  | CrTransformer.StoreOp (ty, r, off, v) ->
    Printf.sprintf "store %s[%s] := %s : %s" (region r) (operand_str off) (operand_str v) (ty_str ty)

let print_transformer (indent : string)
    (states : CrIdentifiers.coq_State Datatypes.list)
    (ctrls : CrIdentifiers.coq_Ctrl Datatypes.list)
    (t : CrTransformer.coq_Transformer) : unit =
  let states' = Shim.listify_coq_list states |> Stdlib.List.map st in
  let ctrls' = Shim.listify_coq_list ctrls |> Stdlib.List.map ctrl in
  if states' <> [] then
    Printf.printf "%sstate vars: %s\n" indent (Stdlib.String.concat ", " states');
  if ctrls' <> [] then
    Printf.printf "%sctrl vars: %s\n" indent (Stdlib.String.concat ", " ctrls');
  let print_rule kind i mp actions =
    Printf.printf "%srule %d [%s] match %s:\n" indent i kind (matchpattern_str mp);
    Shim.listify_coq_list actions
    |> Stdlib.List.iter (fun a -> Printf.printf "%s  %s\n" indent (hdrop_str a)) in
  Shim.listify_coq_list t
  |> Stdlib.List.iteri (fun i rule ->
       match rule with
       | CrTransformer.Seq (CrTransformer.SeqCtr (mp, actions)) -> print_rule "seq" (i + 1) mp actions
       | CrTransformer.Par (CrTransformer.ParCtr (mp, actions)) -> print_rule "par" (i + 1) mp actions)

let parsertarget_str (tgt : CrParser.coq_ParserTarget) : string =
  match tgt with
  | CrParser.TargetState l -> label l
  | CrParser.Accept -> "accept"
  | CrParser.Reject -> "reject"

let selbits_str (b : CrParser.coq_SelBits) : string =
  match b with
  | CrParser.SelHdr (h, s, e) -> Printf.sprintf "%s[%d:%d)" (hdr h) (nat_int s) (nat_int e)
  | CrParser.Peek (off, w) -> Printf.sprintf "peek(+%d, %d)" (nat_int off) (nat_int w)

(* MSB-first, matching how [sc_pattern] is stored; see CLAUDE.md. *)
let bits_str (bs : Datatypes.bool Datatypes.list) : string =
  "0b" ^ (Shim.listify_coq_list bs
          |> Stdlib.List.map (function Datatypes.Coq_true -> "1" | Datatypes.Coq_false -> "0")
          |> Stdlib.String.concat "")

let parserop_str (op : CrParser.coq_ParserOp) : string =
  match op with
  | CrParser.SeekForward w -> Printf.sprintf "seek %d bits" (nat_int w)
  | CrParser.ExtractOpConstructor (h, w, ty) ->
    Printf.sprintf "extract %s : %d bits as %s" (hdr h) (nat_int w) (ty_str ty)

let print_transition (indent : string) (t : CrParser.coq_Transition) : unit =
  match t with
  | CrParser.Unconditional tgt -> Printf.printf "%s-> %s\n" indent (parsertarget_str tgt)
  | CrParser.Select (cases, default) ->
    Printf.printf "%sselect {\n" indent;
    Shim.listify_coq_list cases
    |> Stdlib.List.iter (fun c ->
         Printf.printf "%s  %s matches %s -> %s\n" indent
           (selbits_str c.CrParser.sc_origin) (bits_str c.CrParser.sc_pattern)
           (parsertarget_str c.CrParser.sc_target));
    Printf.printf "%s  default -> %s\n" indent (parsertarget_str default);
    Printf.printf "%s}\n" indent

let print_parser_state (indent : string) (d : CrParser.coq_ParserStateDef) : unit =
  Printf.printf "%sstate %s:\n" indent (label d.CrParser.psd_label);
  (match d.CrParser.psd_action with
   | Datatypes.Some op -> Printf.printf "%s  %s\n" indent (parserop_str op)
   | Datatypes.None -> ());
  print_transition (indent ^ "  ") d.CrParser.psd_trans

let print_parser (indent : string) (p : CrParser.coq_Parser) : unit =
  Printf.printf "%sstart: %s\n" indent (label p.CrParser.parser_start);
  Shim.listify_coq_list p.CrParser.parser_states
  |> Stdlib.List.iter (print_parser_state indent)

let emitop_str (e : CrDeparser.coq_EmitOp) : string =
  match e with
  | CrDeparser.EmitOpConstructor (h, w) -> Printf.sprintf "emit %s (%d bits)" (hdr h) (nat_int w)

(* [CrDeparser.coq_Deparser] is transparently [coq_EmitOp list] (singleton
   record, constructor [mkDeparser] erased). *)
let print_deparser (indent : string) (d : CrDeparser.coq_Deparser) : unit =
  Shim.listify_coq_list d
  |> Stdlib.List.iter (fun e -> Printf.printf "%s%s\n" indent (emitop_str e))

let print_module (indent : string) (m : CrDsl.coq_CrModule) : unit =
  match m with
  | CrDsl.ParserModule (name, p) ->
    Printf.printf "%smodule %s [parser]:\n" indent (modn name);
    print_parser (indent ^ "  ") p
  | CrDsl.DeparserModule (name, d) ->
    Printf.printf "%smodule %s [deparser]:\n" indent (modn name);
    print_deparser (indent ^ "  ") d
  | CrDsl.TransformerModule (name, states, ctrls, t) ->
    Printf.printf "%smodule %s [transformer]:\n" indent (modn name);
    print_transformer (indent ^ "  ") states ctrls t

let print_general_program (p : CrModule.coq_GeneralCaracaraProgram) : unit =
  match p with
  | CrModule.GeneralCaracaraProgramDef (inp_len, regions, net) ->
    Printf.printf "GeneralCaracaraProgram\n";
    Printf.printf "  input_len: %d bytes\n" (nat_int inp_len);
    (match Shim.listify_coq_list regions with
     | [] -> Printf.printf "  regions: (none)\n"
     | rs ->
       Printf.printf "  regions:\n";
       rs |> Stdlib.List.iter (fun r ->
         Printf.printf "    %s: len %d\n" (region r.CrModule.mr_id) (nat_int r.CrModule.mr_len)));
    Printf.printf "  network:\n";
    Printf.printf "    start: %s\n" (modn net.CrModule.start_module);
    let names = CrTypeIF.CrModule.mod_names net.CrModule.net_modules in
    let edges = CrTypeIF.CrDsl.edges_of_connections names net.CrModule.net_edges in
    (match edges with
     | [] -> Printf.printf "    edges: (none)\n"
     | es ->
       Printf.printf "    edges: %s\n"
         (Stdlib.String.concat ", "
            (Stdlib.List.map (fun (a, b) -> Printf.sprintf "%s -> %s" (modn a) (modn b)) es)));
    Shim.listify_coq_list net.CrModule.net_modules
    |> Stdlib.List.iter (print_module "    ")

let read_file (path : string) : string =
  let ic = open_in path in
  let len = in_channel_length ic in
  let s = really_input_string ic len in
  close_in ic; s

let load_module (path : string) : CrTypeIF.CrDsl.coq_CrModule =
  read_file path |> Sexplib.Sexp.of_string |> CrTypeIF.CrDsl.coq_CrModule_of_sexp

let usage () =
  prerr_endline "usage: pretty_print <prog.ir>";
  prerr_endline "       pretty_print --mod <mod.ir>";
  prerr_endline "  Prints a GeneralCaracaraProgram (or, with --mod, a single";
  prerr_endline "  Parser-/Deparser-/TransformerModule) sexp dump in a readable form.";
  exit 1

let () =
  (* Skip Sys.argv.(0) (program name).
     Note: the extracted `List` module shadows Stdlib's; use Stdlib.List. *)
  match Stdlib.List.tl (Array.to_list Sys.argv) with
  | ["--mod"; path] -> print_module "" (load_module path)
  | [path] when Stdlib.String.length path > 0 && Stdlib.String.get path 0 <> '-' ->
    print_general_program (Shim.load_general_program path)
  | _ -> usage ()
