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
  | ParserModule     name _ => name
  | TransformerModule name _ => name
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
   one slot in net_connections, keyed by its ConnectionName's id.  The
   option wrapper lets keys be logically deleted without rebalancing the tree.

   max_mod_id and max_conn_id track the highest key ever allocated so that
   new insertions can pick a fresh key without scanning the whole map. *)
Record ModuleNetwork : Type := mkModuleNetwork {
  net_modules     : PMap.t (option CrModule);
  net_connections : PMap.t (option Connection);
  start_module    : ModuleName;
  max_mod_id      : positive;
  max_conn_id     : positive;
}.

Definition lookup_module (net : ModuleNetwork) (name : ModuleName)
    : option CrModule :=
  PMap.get (unwrap name) (net_modules net).

(* ------------------------------------------------------------------ *)
(* 5b. PMap iteration helpers                                         *)
(* ------------------------------------------------------------------ *)

(* Extract all present (Some) modules from net_modules. *)
Definition all_modules (net : ModuleNetwork) : list CrModule :=
  List.flat_map
    (fun '(_, opt_m) => match opt_m with
    | Some m => [m]
    | None => []
    end)
    (PTree.elements (snd (net_modules net))).

(* Extract all present (Some) connections from net_connections. *)
Definition all_connections (net : ModuleNetwork) : list Connection :=
  List.flat_map
    (fun '(_, opt_c) => match opt_c with
    | Some c => [c]
    | None => []
    end)
    (PTree.elements (snd (net_connections net))).

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
(* 7.  Well-formedness                                                *)
(* ------------------------------------------------------------------ *)

(* Every module is stored at the key matching its name UID. *)
Definition mod_names_consistent (net : ModuleNetwork) : Prop :=
  List.Forall (fun '(k, opt_m) =>
    match opt_m with
    | Some m => (k = (unwrap (get_mod_name m)))
    | None   => True
    end) (PTree.elements (snd (net_modules net))).

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
  List.Forall (fun '(k, opt_c) =>
    match opt_c with
    | Some c => k = (unwrap (get_conn_name c))
    | None   => True
    end) (PTree.elements (snd (net_connections net))).

Definition max_mod_is_max (net : ModuleNetwork) : Prop :=
  forall m,
    In m (all_modules net) ->
    Pos.le (unwrap (get_mod_name m)) (max_mod_id net).

Definition max_conn_is_max (net : ModuleNetwork) : Prop :=
  forall c,
    In c (all_connections net) ->
    Pos.le (unwrap (get_conn_name c)) (max_conn_id net).

(* A well-formed ModuleNetwork satisfies all three conditions. *)
Definition wf_module_network (net : ModuleNetwork) : Prop :=
  mod_names_consistent net /\
  endpoints_defined net /\
  conn_names_consistent net /\
  max_mod_is_max net /\
  max_conn_is_max net.

(* ------------------------------------------------------------------ *)
(* 8.  Module classification                                          *)
(* ------------------------------------------------------------------ *)

(* Decide whether a module is a parser or transformer. *)
Definition is_parser_module (m : CrModule) : bool :=
  match m with
  | ParserModule     _ _ => true
  | TransformerModule _ _ => false
  end.

Definition is_transformer_module (m : CrModule) : bool :=
  match m with
  | ParserModule     _ _ => false
  | TransformerModule _ _ => true
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
(* 10. GeneralCaracaraProgram                                         *)
(* ------------------------------------------------------------------ *)

(* Generalises CaracaraProgramDef (which holds a single Transformer) to a
   full ModuleNetwork, fulfilling the TODO in CrDsl.v.

   Headers and States are declared globally; the network captures all
   parsing and transformation logic as an explicit module graph. *)
Inductive GeneralCaracaraProgram : Type :=
  | GeneralCaracaraProgramDef :
      list Header ->
      list State  ->
      list Ctrl   ->
      ModuleNetwork ->
      GeneralCaracaraProgram.

Definition get_headers_from_general (p : GeneralCaracaraProgram) : list Header :=
  match p with GeneralCaracaraProgramDef h _ _ _ => h end.

Definition get_states_from_general (p : GeneralCaracaraProgram) : list State :=
  match p with GeneralCaracaraProgramDef _ s _ _ => s end.

Definition get_ctrls_from_general (p : GeneralCaracaraProgram) : list Ctrl :=
  match p with GeneralCaracaraProgramDef _ _ c _ => c end.

Definition get_network_from_general (p : GeneralCaracaraProgram) : ModuleNetwork :=
  match p with GeneralCaracaraProgramDef _ _ _ net => net end.

(* Well-formedness of a GeneralCaracaraProgram requires a well-formed network. *)
Definition wf_general_program (p : GeneralCaracaraProgram) : Prop :=
  wf_module_network (get_network_from_general p).

(* ------------------------------------------------------------------ *)
(* 11. Embedding the original CaracaraProgram                         *)
(* ------------------------------------------------------------------ *)

(* The original single-transformer program is a special case: a network
   with exactly one TransformerModule and no connections. *)
Definition add_transformer_module (net : ModuleNetwork) (t : Transformer) : ModuleNetwork :=
  let mod_id := Pos.add (max_mod_id net) 1 in
  let m := TransformerModule (wrap mod_id) t in
  let mods_map := PMap.set mod_id (Some m) (net_modules net) in {|
    net_modules := mods_map;
    net_connections := net_connections net;
    start_module := start_module net;
    max_mod_id := mod_id;
    max_conn_id := max_conn_id net
  |}.

(* ------------------------------------------------------------------ *)
(* 12. Basic lemmas                                                   *)
(* ------------------------------------------------------------------ *)

Definition empty_net : ModuleNetwork :=
  mkModuleNetwork (PMap.init None) (PMap.init None) (ModuleNameCtr 1) 1 1.

Lemma add_transformer_wf_lemma_1 :
  forall (n : ModuleNetwork) (t : Transformer),
    mod_names_consistent n ->
    mod_names_consistent (add_transformer_module n t).
Proof.
  intros n t H.
  unfold mod_names_consistent, add_transformer_module in *.
  simpl.
  apply Forall_forall.
  intros [k opt_m] Hin.
  (* Convert list membership to a tree lookup. *)
  apply PTree.elements_complete in Hin.
  set (mod_id := Pos.add (max_mod_id n) 1) in *.
  destruct (Pos.eq_dec k mod_id) as [Heq | Hne].
  - (* k is the freshly inserted key: check consistency for the new module. *)
    subst k. rewrite PTree.gss in Hin. injection Hin as <-.
    simpl. reflexivity.
  - (* k is an old key: the tree entry is unchanged, so the hypothesis applies. *)
    rewrite PTree.gso in Hin by exact Hne.
    apply PTree.elements_correct in Hin.
    exact (proj1 (Forall_forall _ _) H (k, opt_m) Hin).
Qed.

Lemma add_transformer_wf_lemma_2 :
  forall (n : ModuleNetwork) (t : Transformer),
    endpoints_defined n ->
    endpoints_defined (add_transformer_module n t).
Proof.
Admitted.

Lemma add_transformer_wf_lemma_3 :
  forall (n : ModuleNetwork) (t : Transformer),
    conn_names_consistent n ->
    conn_names_consistent (add_transformer_module n t).
Proof.
Admitted.

Lemma add_transformer_wf_lemma_4 :
  forall (n : ModuleNetwork) (t : Transformer),
    max_mod_is_max n ->
    max_mod_is_max (add_transformer_module n t).
Proof.
Admitted.

Lemma add_transformer_wf_lemma_5 :
  forall (n : ModuleNetwork) (t : Transformer),
    max_conn_is_max n ->
    max_conn_is_max (add_transformer_module n t).
Proof.
Admitted.

Lemma add_transformer_wf_lemma :
  forall (n : ModuleNetwork) (t : Transformer),
    wf_module_network n ->
    wf_module_network (add_transformer_module n t).
Proof with try assumption.
  unfold wf_module_network, add_transformer_module.
  simpl.
  intros.
  destruct H as [H1 [H2 [H3 [H4 H5]]]].
  split; [apply add_transformer_wf_lemma_1 |]...
  split; [apply add_transformer_wf_lemma_2 |]...
  split; [apply add_transformer_wf_lemma_3 |]...
  split; [apply add_transformer_wf_lemma_4 |]...
Qed.