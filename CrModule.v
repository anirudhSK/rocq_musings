From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import ListUtils.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import Strings.String.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrDeparser.
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
  | DeparserModule name _ => name
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
  | DeparserModule _ _ => false
  | TransformerModule _ _ _ _ => false
  end.

Definition is_deparser_module (m : CrModule) : bool :=
  match m with
  | DeparserModule _ _ => true
  | ParserModule _ _ => false
  | TransformerModule _ _ _ _ => false
  end.

Definition is_transformer_module (m : CrModule) : bool :=
  match m with
  | ParserModule _ _ => false
  | DeparserModule _ _ => false
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
Lemma mod_names_unique_prop_bool_lemma :
  forall n, mod_names_unique n <-> mod_names_uniqueb n = true.
Proof.
  intros n. unfold mod_names_unique, mod_names_uniqueb.
  split; intros H.
  - apply negb_true_iff.
    apply has_duplicates_false_iff_norepet. assumption.
  - apply has_duplicates_false_iff_norepet.
    apply negb_true_iff in H. assumption.
Qed.

(* The designated start module exists in the network.  The edge-closure
   condition that used to live alongside this is now folded into
   [restricted_edges]. *)
Definition start_module_is_parser (net : ModuleNetwork) : Prop :=
  match lookup_module net (start_module net) with
  | Some (ParserModule _ _) => True
  | _ => False
  end.
Definition start_module_is_parserb (net : ModuleNetwork) : bool :=
  match lookup_module net (start_module net) with
  | Some (ParserModule _ _) => true
  | _ => false
  end.
Lemma start_module_is_parser_prop_bool_lemma :
  forall n,
    start_module_is_parser n <-> start_module_is_parserb n = true.
Proof.
  intros n.
  unfold start_module_is_parser, start_module_is_parserb.
  destruct (lookup_module n (start_module n)); split; intros.
  - destruct c eqn:Hc; try reflexivity; try exfalso; assumption. 
  - destruct c eqn:Hc; try apply I; try congruence. 
  - exfalso. assumption.
  - congruence.
Qed.

Definition end_modules_are_deparsers (net : ModuleNetwork) : Prop :=
  List.Forall (fun m =>
    match m with
    | DeparserModule _ _ => True
    | _ => False
    end) (sink_modules net).
Definition end_modules_are_deparsersb (net : ModuleNetwork) : bool :=
  List.forallb (fun m =>
    match m with
    | DeparserModule _ _ => true
    | _ => false
    end) (sink_modules net).
Lemma end_modules_are_deparsers_prop_bool_lemma :
  forall n,
    end_modules_are_deparsers n <-> end_modules_are_deparsersb n = true.
Proof.
  intros n. unfold end_modules_are_deparsers, end_modules_are_deparsersb.
  split; intros H.
  - apply List.forallb_forall. intros m Hm.
    destruct m eqn:Hd.
    + apply List.Forall_forall with (x := ParserModule m0 p) in H; try assumption.
      exfalso. assumption.
    + apply List.Forall_forall with (x := DeparserModule m0 d) in H; try assumption.
      reflexivity.
    + apply List.Forall_forall with (x := TransformerModule m0 s c t) in H; try assumption.
      exfalso. assumption.
  - apply List.Forall_forall. intros m Hm.
    destruct m eqn:Hd.
    + apply List.forallb_forall with (x := ParserModule m0 p) in H; try assumption.
      congruence.
    + apply List.forallb_forall with (x := DeparserModule m0 d) in H; try assumption.
      exact I.
    + apply List.forallb_forall with (x := TransformerModule m0 s c t) in H; try assumption.
      congruence.
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
  is_dag net /\
  start_module_is_parser net /\
  end_modules_are_deparsers net.

Definition wf_module_networkb (net : ModuleNetwork) : bool :=
  (mod_names_uniqueb net) &&
  (is_dagb net) &&
  (start_module_is_parserb net) &&
  (end_modules_are_deparsersb net).

Lemma wf_module_network_prop_bool_lemma :
  forall n, wf_module_network n <-> wf_module_networkb n = true.
Proof.
  intros n. unfold wf_module_network, wf_module_networkb.
  split; intros H.
  - destruct H as [H1 [H2 [H3 H4]]].
    repeat rewrite andb_true_iff. repeat split.
    + apply mod_names_unique_prop_bool_lemma. exact H1.
    + apply is_dag_prop_bool_lemma. exact H2.
    + apply start_module_is_parser_prop_bool_lemma. exact H3.
    + apply end_modules_are_deparsers_prop_bool_lemma. exact H4.
  - repeat rewrite andb_true_iff in H. destruct H as [[[H1 H2] H3] H4]. repeat split.
    + apply mod_names_unique_prop_bool_lemma. exact H1.
    + apply is_dag_prop_bool_lemma. exact H2.
    + apply start_module_is_parser_prop_bool_lemma. exact H3.
    + apply end_modules_are_deparsers_prop_bool_lemma. exact H4.
Qed.

(* ------------------------------------------------------------------ *)

Inductive GeneralCaracaraProgram : Type :=
  | GeneralCaracaraProgramDef :
      nat -> (* input packet length *)
      ModuleNetwork ->
      GeneralCaracaraProgram.

Definition get_inp_len_from_general (p : GeneralCaracaraProgram) : nat :=
  match p with GeneralCaracaraProgramDef l _ => l end.

Definition get_network_from_general (p : GeneralCaracaraProgram) : ModuleNetwork :=
  match p with GeneralCaracaraProgramDef _ net => net end.

Definition module_states (m : CrModule) : list State :=
  match m with
  | ParserModule _ _ => []
  | DeparserModule _ _ => []
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
  | DeparserModule _ _ => []
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

(* Parser counterpart of [add_program_to_network]: append a parser module
   wrapping [p] and return its fresh name. *)
Definition add_parser_to_network (net : ModuleNetwork) (p : Parser) : ModuleNetwork * ModuleName :=
  let new_id := max_mod_uid net in
  let pm := ParserModule (wrap new_id) p in
  ({|
    net_modules  := net_modules net ++ [pm];
    net_edges    := net_edges net;
    start_module := start_module net;
  |}, wrap new_id).

(* Deparser counterpart of [add_parser_to_network]: append a deparser module
   wrapping [d] and return its fresh name. *)
Definition add_deparser_to_network (net : ModuleNetwork) (d : Deparser) : ModuleNetwork * ModuleName :=
  let new_id := max_mod_uid net in
  let dm := DeparserModule (wrap new_id) d in
  ({|
    net_modules  := net_modules net ++ [dm];
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
