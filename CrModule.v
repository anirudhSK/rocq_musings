From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrDsl.
From MyProject Require Import Maps.
From MyProject Require Import PosWrapper.

Definition get_mod_name (m : CrModule) : ModuleName :=
  match m with
  | ParserModule name _ => name
  | TransformerModule name _ _ _ => name
  end.

Definition get_conn_src (c : Connection) : ModuleName :=
  match c with
    ConnectionDef src _ _ => src
  end.

Definition get_conn_dst (c : Connection) : ModuleName :=
  match c with
    ConnectionDef _ dst _ => dst
  end.

Definition get_conn_name (c : Connection) : ConnectionName :=
  match c with
    ConnectionDef _ _ n => n
  end.

(* A ModuleNetwork is a directed graph of CrModules connected by typed edges
   (Connections).  Each module occupies one slot in net_modules, keyed by the
   positive integer wrapped inside its ModuleName.  Each connection occupies
   one slot in net_connections, keyed by its ConnectionName's id.

   Presence is checked via ?? (PTree access, returns option); the PMap
   default is a dummy value that is never semantically meaningful.
   max_mod_id and max_conn_id track the highest key ever allocated so that
   new insertions can pick a fresh key without scanning the whole map. *)
Record ModuleNetwork : Type := mkModuleNetwork {
  net_modules     : PMap.t CrModule;
  net_connections : PMap.t Connection;
  start_module    : ModuleName;
  max_mod_id      : positive;
  max_conn_id     : positive;
}.

Definition lookup_module (net : ModuleNetwork) (name : ModuleName)
    : option CrModule :=
  (net_modules net) ?? (unwrap name).

(* ------------------------------------------------------------------ *)
(* 5b. PMap iteration helpers                                         *)
(* ------------------------------------------------------------------ *)

Definition listify_map {T : Type} (m : PMap.t T) : list T :=
  List.map snd (PTree.elements (snd m)).

(* Extract all modules from net_modules. *)
Definition all_modules (net : ModuleNetwork) : list CrModule :=
  listify_map (net_modules net).

(* Extract all connections from net_connections. *)
Definition all_connections (net : ModuleNetwork) : list Connection :=
  listify_map (net_connections net).

(* ------------------------------------------------------------------ *)
(* 6.  Connection traversal                                           *)
(* ------------------------------------------------------------------ *)

Definition outgoing_connections (net : ModuleNetwork) (src : ModuleName)
    : list Connection :=
  filter (fun c => module_name_equal (get_conn_src c) src)
         (all_connections net).

Definition incoming_connections (net : ModuleNetwork) (dst : ModuleName)
    : list Connection :=
  filter (fun c => module_name_equal (get_conn_dst c) dst)
         (all_connections net).

Definition upstream_modules (net : ModuleNetwork) (dst : ModuleName)
    : list ModuleName :=
  map get_conn_src (incoming_connections net dst).

Definition downstream_modules (net : ModuleNetwork) (src : ModuleName)
    : list ModuleName :=
  map get_conn_dst (outgoing_connections net src).

(* ------------------------------------------------------------------ *)
(* 7b. Reachability and DAG check                                     *)
(* ------------------------------------------------------------------ *)

(* `reachable net src dst` holds when dst is reachable from src by
   following one or more connections forward through the network. *)
Inductive reachable (net : ModuleNetwork) : ModuleName -> ModuleName -> Prop :=
| reachable_step : forall src dst,
  In dst (downstream_modules net src) ->
  reachable net src dst
| reachable_trans : forall src mid dst,
  reachable net src mid ->
  reachable net mid dst ->
  reachable net src dst.

(* A network is a DAG when no module can reach itself. *)
Definition is_dag (net : ModuleNetwork) : Prop :=
  forall m, ~ reachable net m m.

(* ------------------------------------------------------------------ *)
(* 8.  Module classification                                          *)
(* ------------------------------------------------------------------ *)

(* Decide whether a module is a parser or transformer. *)
Definition is_parser_module (m : CrModule) : bool :=
  match m with
  | ParserModule _ _ => true
  | TransformerModule _ _ _ _ => false
  end.

Definition is_transformer_module (m : CrModule) : bool :=
  match m with
  | ParserModule _ _ => false
  | TransformerModule _ _ _ _ => true
  end.

(* Collect all parser modules in a network. *)
Definition parser_modules (net : ModuleNetwork) : list CrModule :=
  filter is_parser_module (all_modules net).

(* Collect all transformer modules in a network. *)
Definition transformer_modules (net : ModuleNetwork) : list CrModule :=
  filter is_transformer_module (all_modules net).

(* ------------------------------------------------------------------ *)
(* 9.  Source / sink identification                                   *)
(* ------------------------------------------------------------------ *)

(* A source module has no incoming connections (packet entry point). *)
Definition is_source (net : ModuleNetwork) (m : CrModule) : bool :=
  match incoming_connections net (get_mod_name m) with
  | [] => true
  | _  => false
  end.

(* A sink module has no outgoing connections (packet exit point). *)
Definition is_sink (net : ModuleNetwork) (m : CrModule) : bool :=
  match outgoing_connections net (get_mod_name m) with
  | [] => true
  | _  => false
  end.

Definition source_modules (net : ModuleNetwork) : list CrModule :=
  filter (is_source net) (all_modules net).

Definition sink_modules (net : ModuleNetwork) : list CrModule :=
  filter (is_sink net) (all_modules net).

(* ------------------------------------------------------------------ *)
(* 7.  Well-formedness                                                *)
(* ------------------------------------------------------------------ *)

(* Every module is stored at the key matching its name UID. *)
Definition mod_names_consistent (net : ModuleNetwork) : Prop :=
  List.Forall (fun '(k, m) =>
    k = unwrap (get_mod_name m))
    (PTree.elements (snd (net_modules net))).

(* Every endpoint of every connection refers to a known module. *)
Definition endpoints_defined (net : ModuleNetwork) : Prop :=
  List.Forall (fun c =>
    match lookup_module net (get_conn_src c),
          lookup_module net (get_conn_dst c) with
    | Some _, Some _ => True
    | _,      _      => False
    end) (all_connections net) /\
    match lookup_module net (start_module net) with
    | Some _ => True
    | None   => False
    end.

(* Predicate: every connection is stored at the key matching its name UID. *)
Definition conn_names_consistent (net : ModuleNetwork) : Prop :=
  List.Forall (fun '(k, c) =>
    k = unwrap (get_conn_name c))
    (PTree.elements (snd (net_connections net))).

Definition max_mod_is_max (net : ModuleNetwork) : Prop :=
  forall m,
    In m (all_modules net) ->
    Pos.le (unwrap (get_mod_name m)) (max_mod_id net).

Definition max_conn_is_max (net : ModuleNetwork) : Prop :=
  forall c,
    In c (all_connections net) ->
    Pos.le (unwrap (get_conn_name c)) (max_conn_id net).

(* A well-formed ModuleNetwork satisfies all conditions. *)
Definition wf_module_network (net : ModuleNetwork) : Prop :=
  mod_names_consistent net /\
  endpoints_defined net /\
  conn_names_consistent net /\
  max_mod_is_max net /\
  max_conn_is_max net /\
  is_dag net.

(* ------------------------------------------------------------------ *)
(* 10. GeneralCaracaraProgram                                         *)
(* ------------------------------------------------------------------ *)

(* Generalises CaracaraProgramDef (which holds a single Transformer) to a
   full ModuleNetwork, fulfilling the TODO in CrDsl.v.

   Headers and States are declared globally; the network captures all
   parsing and transformation logic as an explicit module graph. *)
Inductive GeneralCaracaraProgram : Type :=
  | GeneralCaracaraProgramDef :
      list Header ->
      ModuleNetwork ->
      GeneralCaracaraProgram.

Definition get_headers_from_general (p : GeneralCaracaraProgram) : list Header :=
  match p with GeneralCaracaraProgramDef h _ => h end.

Definition get_network_from_general (p : GeneralCaracaraProgram) : ModuleNetwork :=
  match p with GeneralCaracaraProgramDef _ net => net end.

Definition get_states_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option (list State) :=
  let modnet := get_network_from_general p in
  match (net_modules modnet) ?? (unwrap m) with
  | Some (TransformerModule _ states _ _) => Some states
  | _ => None
  end.

Definition get_ctrls_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option (list Ctrl) :=
  let modnet := get_network_from_general p in
  match (net_modules modnet) ?? (unwrap m) with
  | Some (TransformerModule _ _ ctrls _) => Some ctrls
  | _ => None
  end.

Definition get_transformer_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option Transformer :=
  let modnet := get_network_from_general p in
  match (net_modules modnet) ?? (unwrap m) with
  | Some (TransformerModule _ _ _ t) => Some t
  | _ => None
  end.

(* Well-formedness of a GeneralCaracaraProgram requires a well-formed network. *)
Definition wf_general_program (p : GeneralCaracaraProgram) : Prop :=
  wf_module_network (get_network_from_general p).

(* ------------------------------------------------------------------ *)
(* 11. Embedding the original CaracaraProgram                         *)
(* ------------------------------------------------------------------ *)

Definition add_program_to_network (net : ModuleNetwork) (p : CaracaraProgram) : ModuleNetwork :=
  let max_mod_id' := Pos.add (max_mod_id net) 1 in
  let tm := TransformerModule
    (wrap max_mod_id')
    (get_states_from_prog p)
    (get_ctrls_from_prog p)
    (get_transformer_from_prog p) in
  let net_modules' := PMap.set max_mod_id' tm (net_modules net) in
  {|
    net_modules := net_modules';
    max_mod_id := max_mod_id';
    (* * * * *)
    net_connections := net_connections net;
    start_module := start_module net;
    max_conn_id := max_conn_id net;
  |}.

Definition add_connection_to_network (net : ModuleNetwork) (c : Connection) : ModuleNetwork :=
  let max_conn_id' := Pos.add (max_conn_id net) 1 in
  let net_connections' := PMap.set max_conn_id' c (net_connections net) in
  {|
    net_connections := net_connections';
    max_conn_id := max_conn_id';
    (* * * * *)
    net_modules := net_modules net;
    start_module := start_module net;
    max_mod_id := max_mod_id net;
  |}.

Definition set_start_module (net : ModuleNetwork) (m : ModuleName) : ModuleNetwork :=
  {|
    start_module := m;
    (* * * * *)
    net_modules := net_modules net;
    net_connections := net_connections net;
    max_mod_id := max_mod_id net;
    max_conn_id := max_conn_id net;
  |}.

Definition init_general_from_net (net : ModuleNetwork) : GeneralCaracaraProgram :=
  GeneralCaracaraProgramDef [] net.

(* Dummy values used only as PMap defaults; never semantically accessed. *)
Definition dummy_module : CrModule :=
  TransformerModule (ModuleNameCtr 1) [] [] [].
Definition dummy_connection : Connection :=
  ConnectionDef (ModuleNameCtr 1) (ModuleNameCtr 1) (ConnectionNameCtr 1).

Definition empty_net : ModuleNetwork :=
  mkModuleNetwork
    (PMap.init dummy_module)
    (PMap.init dummy_connection)
    (ModuleNameCtr 1) 1 1.
