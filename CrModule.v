From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrTransformer.
From MyProject Require Import CrDsl.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From MyProject Require Import CrProgramState.
From MyProject Require Import PosWrapper.
From MyProject Require Import SmtExpr.

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

(* A ModuleNetwork is a directed graph of CrModules connected by typed edges (Connections). *)
Record ModuleNetwork : Type := mkModuleNetwork {
  net_modules     : list CrModule;
  net_connections : list Connection;
  start_module    : ModuleName;
}.

Definition lookup_module (net : ModuleNetwork) (name : ModuleName)
    : option CrModule :=
  find (fun m => module_name_equal (get_mod_name m) name) (net_modules net).

(* ------------------------------------------------------------------ *)

Definition outgoing_connections (net : ModuleNetwork) (src : ModuleName)
    : list Connection :=
  filter (fun c => module_name_equal (get_conn_src c) src)
         (net_connections net).

Definition incoming_connections (net : ModuleNetwork) (dst : ModuleName)
    : list Connection :=
  filter (fun c => module_name_equal (get_conn_dst c) dst)
         (net_connections net).

Definition upstream_modules (net : ModuleNetwork) (dst : ModuleName)
    : list ModuleName :=
  map get_conn_src (incoming_connections net dst).

Definition downstream_modules (net : ModuleNetwork) (src : ModuleName)
    : list ModuleName :=
  map get_conn_dst (outgoing_connections net src).

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

Definition is_dag (net : ModuleNetwork) : Prop :=
  forall m, ~ reachable net m m.

Definition no_fan_out (net : ModuleNetwork) : Prop :=
  forall m, List.length (downstream_modules net m) <= 1.

Definition no_fan_in (net : ModuleNetwork) : Prop :=
  forall m, List.length (upstream_modules net m) <= 1.

(* ------------------------------------------------------------------ *)

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

Definition parser_modules (net : ModuleNetwork) : list CrModule :=
  filter is_parser_module (net_modules net).

Definition transformer_modules (net : ModuleNetwork) : list CrModule :=
  filter is_transformer_module (net_modules net).

(* ------------------------------------------------------------------ *)

Definition is_source (net : ModuleNetwork) (m : CrModule) : bool :=
  match incoming_connections net (get_mod_name m) with
  | [] => true
  | _  => false
  end.

Definition is_sink (net : ModuleNetwork) (m : CrModule) : bool :=
  match outgoing_connections net (get_mod_name m) with
  | [] => true
  | _  => false
  end.

Definition source_modules (net : ModuleNetwork) : list CrModule :=
  filter (is_source net) (net_modules net).

Definition sink_modules (net : ModuleNetwork) : list CrModule :=
  filter (is_sink net) (net_modules net).

Definition single_sink (net : ModuleNetwork) : Prop :=
  List.length (sink_modules net) = 1.

(* ------------------------------------------------------------------ *)

(* Module names are pairwise distinct in net_modules. *)
Definition mod_names_unique (net : ModuleNetwork) : Prop :=
  Coqlib.list_norepet (map get_mod_name (net_modules net)).

(* Connection names are pairwise distinct in net_connections. *)
Definition conn_names_unique (net : ModuleNetwork) : Prop :=
  Coqlib.list_norepet (map get_conn_name (net_connections net)).

(* Every endpoint of every connection refers to a known module, and the
   designated start module exists in the network. *)
Definition endpoints_defined (net : ModuleNetwork) : Prop :=
  List.Forall (fun c =>
    match lookup_module net (get_conn_src c),
          lookup_module net (get_conn_dst c) with
    | Some _, Some _ => True
    | _,      _      => False
    end) (net_connections net) /\
    match lookup_module net (start_module net) with
    | Some _ => True
    | None   => False
    end.

(* A well-formed ModuleNetwork satisfies all conditions. *)
Definition wf_module_network (net : ModuleNetwork) : Prop :=
  mod_names_unique net /\
  conn_names_unique net /\
  endpoints_defined net /\
  is_dag net.

(* ------------------------------------------------------------------ *)

Inductive GeneralCaracaraProgram : Type :=
  | GeneralCaracaraProgramDef :
      list Header -> (* Input Header Format *)
      ModuleNetwork ->
      list Header -> (* Output Header Format *)
      GeneralCaracaraProgram.

Definition get_headers_from_general (p : GeneralCaracaraProgram) : list Header :=
  match p with GeneralCaracaraProgramDef h _ _ => h end.

Definition get_network_from_general (p : GeneralCaracaraProgram) : ModuleNetwork :=
  match p with GeneralCaracaraProgramDef _ net _ => net end.

Definition get_signature_from_general (p : GeneralCaracaraProgram) : list Header :=
  match p with GeneralCaracaraProgramDef _ _ sig => sig end.

Definition module_states (m : CrModule) : list State :=
  match m with
  | ParserModule _ _ => []
  | TransformerModule _ s _ _ => s
  end.
Definition get_states_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option (list State) :=
  match lookup_module (get_network_from_general p) m with
  | Some m' => Some (module_states m')
  | _ => None
  end.

Definition module_ctrls (m : CrModule) : list Ctrl :=
  match m with
  | ParserModule _ _ => []
  | TransformerModule _ _ c _ => c
  end.
Definition get_ctrls_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option (list Ctrl) :=
  match lookup_module (get_network_from_general p) m with
  | Some m' => Some (module_ctrls m')
  | _ => None
  end.

Definition get_transformer_from_general (p : GeneralCaracaraProgram) (m : ModuleName) : option Transformer :=
  match lookup_module (get_network_from_general p) m with
  | Some (TransformerModule _ _ _ t) => Some t
  | _ => None
  end.

Definition inject_headers {T : Type} (packet : PMap.t T) (local : ProgramState T)
    : ProgramState T :=
  {| ctrl_map   := ctrl_map local;
     header_map := packet;
     state_map  := state_map local |}.

Definition GeneralProgramState (T : Type) : Type := PMap.t (ProgramState T).
Definition GeneralConcreteState : Type := GeneralProgramState CrVal.
Definition GeneralSymbolicState : Type := GeneralProgramState SmtArithExpr.

Definition get_sink_states {T : Type}
  (net : ModuleNetwork)
  (ledger : PMap.t T)
  : list T :=
  List.fold_right
    (fun m acc =>
      match ledger ?? (unwrap (get_mod_name m)) with
      | Some ps => ps :: acc
      | None => acc
      end) [] (sink_modules net).

(* ------------------------------------------------------------------ *)

(* One past the largest module uid in use — the next fresh id to allocate.
   Invariant: forall m_id in net, m_id < max_mod_uid net. *)
Definition max_mod_uid (net : ModuleNetwork) : positive :=
  match net_modules net with
  | [] => 1%positive
  | ms => Pos.succ (List.fold_left
            (fun acc m => Pos.max acc (unwrap (get_mod_name m)))
            ms 1%positive)
  end.

Definition max_conn_uid (net : ModuleNetwork) : positive :=
  List.fold_left
    (fun acc c => Pos.max acc (unwrap (get_conn_name c)))
    (net_connections net) 1%positive.

Definition add_program_to_network (net : ModuleNetwork) (p : CaracaraProgram) : ModuleNetwork * ModuleName :=
  let new_id := max_mod_uid net in
  let tm := TransformerModule
    (wrap new_id)
    (get_states_from_prog p)
    (get_ctrls_from_prog p)
    (get_transformer_from_prog p) in
  ({|
    net_modules     := net_modules net ++ [tm];
    net_connections := net_connections net;
    start_module    := start_module net;
  |}, wrap new_id).

Definition add_connection_to_network (net : ModuleNetwork) (from to : ModuleName) : ModuleNetwork :=
  let new_id := Pos.succ (max_conn_uid net) in
  let c := ConnectionDef from to (wrap new_id) in
  {|
    net_modules     := net_modules net;
    net_connections := net_connections net ++ [c];
    start_module    := start_module net;
  |}.

Definition set_start_module (net : ModuleNetwork) (m : ModuleName) : ModuleNetwork :=
  {|
    net_modules     := net_modules net;
    net_connections := net_connections net;
    start_module    := m;
  |}.

Definition empty_net : ModuleNetwork :=
  {|
    net_modules     := [];
    net_connections := [];
    start_module    := ModuleNameCtr 1;
  |}.
