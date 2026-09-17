(* IrSize -- structural size metrics for a Caracara program.

   The "how large is the program being checked" column of the evaluation
   table.  Everything here counts syntax, not semantics: it walks the IR a
   benchmark actually hands to the checker, so the number quoted next to a
   timing is the number for the thing that was timed.

   Two shapes of program are counted, matching the checker's two entry points:
   a [CaracaraProgram] (one transformer, [SmtQuery.equivalence_checker_cr_dsl])
   and a [GeneralCaracaraProgram] (a module network,
   [SmtModuleQuery.modnet_equivalence_checker]).  A single-transformer program
   is reported as a one-module network so the two are comparable in one table.

   Note on [net_edges]: the Rocq type is a total function [ModuleName ->
   ModuleName -> bool], not a list, so edges cannot be enumerated from it
   directly.  They are counted by probing the function over the module names
   actually present, which is exactly what [CrModule.restricted_edges] means by
   an edge. *)

type t = {
  modules      : int;
  parsers      : int;
  transformers : int;
  deparsers    : int;
  edges        : int;
  parser_states: int;   (* summed over every parser module *)
  transitions  : int;   (* select cases + unconditional jumps *)
  extracts     : int;   (* ParserOp: extract and seek *)
  rules        : int;   (* match-action rules, summed over transformers *)
  match_terms  : int;   (* conjuncts across all rule match patterns *)
  hdr_ops      : int;   (* the IR's primitive operations *)
  mem_ops      : int;   (* the load/store subset of hdr_ops *)
  emits        : int;   (* deparser emit operations *)
  regions      : int;   (* declared memory regions *)
  region_bytes : int;   (* summed declared region length *)
  states       : int;   (* declared state variables, summed over modules *)
  ctrls        : int;   (* declared control-plane variables *)
  pkt_len      : int;   (* declared input packet length, in bits *)
}

let zero = {
  modules = 0; parsers = 0; transformers = 0; deparsers = 0; edges = 0;
  parser_states = 0; transitions = 0; extracts = 0;
  rules = 0; match_terms = 0; hdr_ops = 0; mem_ops = 0; emits = 0;
  regions = 0; region_bytes = 0; states = 0; ctrls = 0; pkt_len = 0;
}

(* The extracted code uses Coq's list and nat, not OCaml's. *)
let l = Shim.listify_coq_list
let n = Shim.coq_nat_to_int

let is_mem_op (op : CrTransformer.coq_HdrOp) =
  match op with
  | CrTransformer.LoadOp _ | CrTransformer.StatefulLoadOp _
  | CrTransformer.StoreOp _ -> true
  | _ -> false

(* A rule contributes its match conjuncts and its action's operations. *)
let count_rule acc (r : CrTransformer.coq_MatchActionRule) =
  let mp, ops =
    match r with
    | CrTransformer.Seq (CrTransformer.SeqCtr (mp, ops)) -> mp, ops
    | CrTransformer.Par (CrTransformer.ParCtr (mp, ops)) -> mp, ops
  in
  let ops = l ops in
  { acc with
    rules       = acc.rules + 1;
    match_terms = acc.match_terms + Stdlib.List.length (l mp);
    hdr_ops     = acc.hdr_ops + Stdlib.List.length ops;
    mem_ops     = acc.mem_ops
                  + Stdlib.List.length (Stdlib.List.filter is_mem_op ops); }

let count_transformer acc (t : CrTransformer.coq_Transformer) =
  Stdlib.List.fold_left count_rule acc (l t)

(* A parser state contributes its optional extraction and its transition; a
   select's cases are counted individually, since each is a distinct edge the
   symbolic walk has to consider, and the default is one more. *)
let count_parser_state acc (d : CrParser.coq_ParserStateDef) =
  let acc =
    { acc with
      parser_states = acc.parser_states + 1;
      extracts = acc.extracts + (match d.CrParser.psd_action with
                                 | Some _ -> 1 | None -> 0) }
  in
  match d.CrParser.psd_trans with
  | CrParser.Unconditional _ -> { acc with transitions = acc.transitions + 1 }
  | CrParser.Select (cases, _) ->
    { acc with
      transitions = acc.transitions + Stdlib.List.length (l cases) + 1 }

let count_parser acc (p : CrParser.coq_Parser) =
  Stdlib.List.fold_left count_parser_state acc (l p.CrParser.parser_states)

let count_module acc (m : CrDsl.coq_CrModule) =
  let acc = { acc with modules = acc.modules + 1 } in
  match m with
  | CrDsl.ParserModule (_, p) ->
    count_parser { acc with parsers = acc.parsers + 1 } p
  | CrDsl.DeparserModule (_, d) ->
    { acc with deparsers = acc.deparsers + 1;
               emits = acc.emits + Stdlib.List.length (l d) }
  | CrDsl.TransformerModule (_, s, c, t) ->
    count_transformer
      { acc with transformers = acc.transformers + 1;
                 states = acc.states + Stdlib.List.length (l s);
                 ctrls  = acc.ctrls  + Stdlib.List.length (l c) } t

(* [net_edges] is a total function, so an edge is found by asking about every
   ordered pair of names present -- the same restriction [restricted_edges]
   applies. *)
let count_edges (net : CrModule.coq_ModuleNetwork) =
  let names =
    Stdlib.List.map CrModule.get_mod_name (l net.CrModule.net_modules) in
  Stdlib.List.fold_left
    (fun acc src ->
       Stdlib.List.fold_left
         (fun acc dst ->
            match net.CrModule.net_edges src dst with
            | Datatypes.Coq_true -> acc + 1
            | Datatypes.Coq_false -> acc)
         acc names)
    0 names

let of_general (p : CrModule.coq_GeneralCaracaraProgram) : t =
  match p with
  | CrModule.GeneralCaracaraProgramDef (len, regions, net) ->
    let regions = l regions in
    let acc =
      Stdlib.List.fold_left count_module zero (l net.CrModule.net_modules) in
    { acc with
      pkt_len      = n len;
      edges        = count_edges net;
      regions      = Stdlib.List.length regions;
      region_bytes =
        Stdlib.List.fold_left
          (fun a d -> a + n d.CrModule.mr_len) 0 regions; }

(* A single-transformer program has no network around it; report it as the
   one-module network it is, so a row for it lines up with the others. *)
let of_program (p : CrDsl.coq_CaracaraProgram) : t =
  match p with
  | CrDsl.CaracaraProgramDef (_, s, c, t) ->
    let acc =
      count_transformer
        { zero with modules = 1; transformers = 1;
                    states = Stdlib.List.length (l s);
                    ctrls  = Stdlib.List.length (l c) } t
    in
    acc

(* The two numbers a size column usually wants: how many rules/states there are
   to reason about, and how many primitive operations sit under them. *)
let nodes (m : t) = m.rules + m.parser_states + m.emits
let ops   (m : t) = m.hdr_ops + m.extracts + m.transitions + m.emits

let header = "modules,parsers,transformers,deparsers,edges,parser_states,\
              transitions,extracts,rules,match_terms,hdr_ops,mem_ops,emits,\
              regions,region_bytes,states,ctrls,pkt_len,nodes,ops"

let to_csv (m : t) =
  Stdlib.String.concat ","
    (Stdlib.List.map Stdlib.string_of_int
       [ m.modules; m.parsers; m.transformers; m.deparsers; m.edges;
         m.parser_states; m.transitions; m.extracts; m.rules; m.match_terms;
         m.hdr_ops; m.mem_ops; m.emits; m.regions; m.region_bytes;
         m.states; m.ctrls; m.pkt_len; nodes m; ops m ])

(* A compact one-line rendering for the human-readable table. *)
let to_short (m : t) =
  Stdlib.Printf.sprintf "%dm/%dr/%dp/%do"
    m.modules m.rules m.parser_states (ops m)
