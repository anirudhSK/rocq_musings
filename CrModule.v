From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import ListUtils.
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
From MyProject Require Import PosGraphLemmas.
From MyProject Require Import SmtExpr.

Definition get_mod_name (m : CrModule) : ModuleName :=
  match m with
  | ParserModule name _ => name
  | TransformerModule name _ _ _ => name
  end.

(* A ModuleNetwork is a directed graph of CrModules whose edges are given by
   the boolean adjacency function [net_edges].  The function is total with a
   default of [false]; edges from/to module names not in [net_modules] are
   ignored by [restricted_edges] below, which is the relation actually used
   for reachability and acyclicity. *)
Record ModuleNetwork : Type := mkModuleNetwork {
  net_modules  : list CrModule;
  net_edges    : Connections;
  start_module : ModuleName;
}.

Definition lookup_module (net : ModuleNetwork) (name : ModuleName)
    : option CrModule :=
  find (fun m => posesque_eqb (get_mod_name m) name) (net_modules net).

(* ------------------------------------------------------------------ *)

Definition upstream_modules (net : ModuleNetwork) (dst : ModuleName)
    : list ModuleName :=
  filter (fun src => net_edges net src dst)
         (map get_mod_name (net_modules net)).

Definition downstream_modules (net : ModuleNetwork) (src : ModuleName)
    : list ModuleName :=
  filter (fun dst => net_edges net src dst)
         (map get_mod_name (net_modules net)).

(* ------------------------------------------------------------------ *)

(* Boolean membership test for module names in the network. *)
Definition in_names (net : ModuleNetwork) (m : ModuleName) : bool :=
  existsb (posesque_eqb m) (map get_mod_name (net_modules net)).

(* Edges restricted to pairs of names that both appear in [net_modules].
   This folds the endpoint-closure invariant directly into the edge
   relation: edges to or from unknown module names are silently dropped. *)
Definition restricted_edges (net : ModuleNetwork)
    (src dst : ModuleName) : bool :=
  in_names net src && in_names net dst && net_edges net src dst.

(* A direct edge from [src] to [dst] in the network (restricted form). *)
Definition edge (net : ModuleNetwork) (src dst : ModuleName) : Prop :=
  restricted_edges net src dst = true.

(* The network is a DAG iff its restricted edge relation contains no
   cycle.  Defined in terms of the generic [PosGraphLemmas] development. *)
Definition is_dag (net : ModuleNetwork) : Prop :=
  PosGraphLemmas.is_dag (restricted_edges net).

(* Boolean acyclicity check via bounded DFS over the module names. *)
Definition is_dagb (net : ModuleNetwork) : bool :=
  PosGraphLemmas.is_dagb (restricted_edges net)
                         (map get_mod_name (net_modules net)).

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
  negb (existsb (fun src => net_edges net src (get_mod_name m))
                (map get_mod_name (net_modules net))).

Definition is_sink (net : ModuleNetwork) (m : CrModule) : bool :=
  negb (existsb (fun dst => net_edges net (get_mod_name m) dst)
                (map get_mod_name (net_modules net))).

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
Definition mod_names_uniqueb (net : ModuleNetwork) : bool :=
  negb (has_duplicates posesque_eqb (map get_mod_name (net_modules net))).

(* The designated start module exists in the network.  The edge-closure
   condition that used to live alongside this is now folded into
   [restricted_edges]. *)
Definition start_module_defined (net : ModuleNetwork) : Prop :=
  match lookup_module net (start_module net) with
  | Some _ => True
  | None => False
  end.
Definition start_module_definedb (net : ModuleNetwork) : bool :=
  match lookup_module net (start_module net) with
  | Some _ => true
  | None => false
  end.
Lemma start_module_defined_prop_bool_lemma :
  forall n,
    start_module_defined n <-> start_module_definedb n = true.
Proof.
  intros n.
  unfold start_module_defined, start_module_definedb.
  destruct (lookup_module n (start_module n));
    split; intros; (exact I || reflexivity || contradiction || discriminate).
Qed.

Lemma in_names_iff :
  forall net m,
    in_names net m = true <-> In m (map get_mod_name (net_modules net)).
Proof.
  intros net m. unfold in_names. split.
  - intros H. apply existsb_exists in H. destruct H as [x [Hin Heq]].
    apply posesque_eqb_iff in Heq. subst. exact Hin.
  - intros Hin. apply existsb_exists. exists m. split.
    + exact Hin.
    + apply posesque_eqb_iff. reflexivity.
Qed.

(* Because [restricted_edges] already enforces endpoint closure, the
   Prop/bool equivalence holds unconditionally. *)
Lemma is_dag_prop_bool_lemma :
  forall n, is_dag n <-> is_dagb n = true.
Proof.
  intros n. unfold is_dag, is_dagb.
  apply PosGraphLemmas.is_dag_prop_bool_lemma.
  intros u v Hg. unfold restricted_edges in Hg.
  apply andb_true_iff in Hg. destruct Hg as [Hin _].
  apply andb_true_iff in Hin. destruct Hin as [Hu Hv].
  split; apply in_names_iff; assumption.
Qed.

(* A well-formed ModuleNetwork satisfies all conditions. *)
Definition wf_module_network (net : ModuleNetwork) : Prop :=
  mod_names_unique net /\
  start_module_defined net /\
  is_dag net.

Definition wf_module_networkb (net : ModuleNetwork) : bool :=
  (mod_names_uniqueb net) &&
  (start_module_definedb net) &&
  (is_dagb net).

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

Definition add_program_to_network (net : ModuleNetwork) (p : CaracaraProgram) : ModuleNetwork * ModuleName :=
  let new_id := max_mod_uid net in
  let tm := TransformerModule
    (wrap new_id)
    (get_states_from_prog p)
    (get_ctrls_from_prog p)
    (get_transformer_from_prog p) in
  ({|
    net_modules  := net_modules net ++ [tm];
    net_edges    := net_edges net;
    start_module := start_module net;
  |}, wrap new_id).

(* TODO: Performance. Each call wraps the previous [net_edges] in another
   closure, so after k connections a single edge query walks a chain of k
   closures (O(k) per query). *)
Definition add_connection_to_network (net : ModuleNetwork) (from to : ModuleName) : ModuleNetwork :=
  {|
    net_modules  := net_modules net;
    net_edges    := fun src dst =>
      (posesque_eqb src from && posesque_eqb dst to)
      || net_edges net src dst;
    start_module := start_module net;
  |}.

Definition set_start_module (net : ModuleNetwork) (m : ModuleName) : ModuleNetwork :=
  {|
    net_modules  := net_modules net;
    net_edges    := net_edges net;
    start_module := m;
  |}.

Definition empty_net : ModuleNetwork :=
  {|
    net_modules  := [];
    net_edges    := fun _ _ => false;
    start_module := ModuleNameCtr 1;
  |}.
