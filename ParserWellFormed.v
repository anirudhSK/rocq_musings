(* ================================================================== *)
(* Well-formedness for parsers.                                       *)
(*                                                                    *)
(* [run_parser_concrete] returns [None] in exactly two situations: it  *)
(* ran out of fuel, or a transition named a state with no definition.  *)
(* Neither is a verdict about the packet -- a rejected packet is       *)
(* [Some] with [pr_accept := false] -- so both are things a program    *)
(* the checker is allowed to see should not be able to do.  The three  *)
(* conditions here rule them out, and                                  *)
(* [ParserTerminationLemmas.eval_parser_no_fuel_starvation] is the     *)
(* proof that they do.                                                 *)
(*                                                                    *)
(* All three are decidable, and each comes with a [...b] twin and an   *)
(* iff lemma, so [well_formed_moduleb] can keep deciding what          *)
(* [well_formed_module] states -- the same Prop/bool pairing the       *)
(* transformer conditions already use.                                 *)
(* ================================================================== *)
From Stdlib Require Import List.
From Stdlib Require Import Bool.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import PosGraphLemmas.
From MyProject Require Import ListUtils.
From MyProject Require Import Coqlib.

(* ------------------------------------------------------------------ *)
(* The transition graph                                                *)
(* ------------------------------------------------------------------ *)

(* Every target a transition can take.  For a [Select] that is the default
   AND every case's target: which one fires depends on header values and, with
   a [Peek], on the packet, so anything downstream of a select must
   over-approximate. *)
Definition transition_targets (t : Transition) : list ParserTarget :=
  match t with
  | Unconditional tgt => [tgt]
  | Select cases default => default :: List.map sc_target cases
  end.

(* The [TargetState] labels among them; [Accept] and [Reject] terminate the
   parse and so are not edges. *)
Definition target_labels (ts : list ParserTarget) : list ParserStateLabel :=
  List.fold_right
    (fun t acc => match t with
                  | TargetState s => s :: acc
                  | Accept => acc
                  | Reject => acc
                  end)
    [] ts.

Definition state_successors (d : ParserStateDef) : list ParserStateLabel :=
  target_labels (transition_targets (psd_trans d)).

Definition parser_labels (p : Parser) : list ParserStateLabel :=
  List.map psd_label (parser_states p).

Definition defined_label (p : Parser) (l : ParserStateLabel) : bool :=
  match lookup_def p l with
  | Some _ => true
  | None => false
  end.

(* ------------------------------------------------------------------ *)
(* (1) Closure: every label named actually exists                      *)
(* ------------------------------------------------------------------ *)

Definition parser_closedb (p : Parser) : bool :=
  defined_label p (parser_start p) &&
  List.forallb
    (fun d => List.forallb (defined_label p) (state_successors d))
    (parser_states p).

Definition parser_closed (p : Parser) : Prop := parser_closedb p = true.

(* ------------------------------------------------------------------ *)
(* (2) Progress: every cycle consumes at least one bit                 *)
(* ------------------------------------------------------------------ *)

(* A state CONSUMES when its action moves the cursor.  A zero-width op does
   not, which is why this is not simply [psd_action <> None].  (Were widths
   [positive] rather than [nat] this would be exactly "has an action"; the
   [Nat.ltb 0] is what that representation buys, and all it buys.)

   A [Peek] in the transition is deliberately absent: a lookahead examines
   bits without consuming them, so it leaves the cursor where it was and
   cannot be what makes a cycle terminate. *)
Definition op_consumes (po : ParserOp) : bool :=
  match po with
  | SeekForward w => Nat.ltb 0 w
  | ExtractOpConstructor _ w _ => Nat.ltb 0 w
  end.

Definition state_consumes (d : ParserStateDef) : bool :=
  match psd_action d with
  | None => false
  | Some po => op_consumes po
  end.

(* The NON-CONSUMING fragment of the transition graph: an edge [src -> dst]
   when [src]'s definition does not move the cursor and can jump to [dst].

   Both endpoints are restricted to labels that have definitions, exactly as
   [CrModule.restricted_edges] restricts to known module names.  That folds
   condition (1) into the edge relation, so a dangling target cannot make the
   acyclicity check pass vacuously, and it is what discharges the endpoint
   hypothesis of [is_dag_prop_bool_lemma]. *)
Definition nonconsuming_edges (p : Parser) (src dst : ParserStateLabel) : bool :=
  match lookup_def p src with
  | None => false
  | Some d =>
      negb (state_consumes d) &&
      defined_label p dst &&
      List.existsb (fun l => posesque_eqb l dst) (state_successors d)
  end.

(* A parser makes progress iff its non-consuming fragment is acyclic.

   This does NOT ask the parser to be a DAG.  A cycle through any state that
   extracts or seeks contributes no edge here at all, so P4-style loops --
   a state revisited once per cursor position -- pass.  What it rules out is
   a cycle in which EVERY state is non-consuming, which is a true infinite
   loop: the cursor never moves, the transitions are deterministic and the
   header map is unchanged, so the whole configuration repeats forever.

   It is a syntactic approximation of "no (state, cursor) pair repeats".  The
   parsers it rejects but that property admits are those whose non-consuming
   cycle is dynamically unreachable, which is undecidable in general; the
   price of keeping a [...b] twin. *)
Definition parser_progresses (p : Parser) : Prop :=
  PosGraphLemmas.is_dag (nonconsuming_edges p).

Definition parser_progressesb (p : Parser) : bool :=
  PosGraphLemmas.is_dagb (nonconsuming_edges p) (parser_labels p).

(* ------------------------------------------------------------------ *)
(* (3) Unique labels                                                   *)
(* ------------------------------------------------------------------ *)

(* [lookup_def] takes the FIRST match, so without this a parser can carry two
   definitions for a label with only one of them reachable.  Not needed for
   totality, but it is the same hygiene [well_formed_module] already demands
   of a transformer's states and ctrls. *)
Definition parser_labels_uniqueb (p : Parser) : bool :=
  negb (has_duplicates posesque_eqb (parser_labels p)).

(* ------------------------------------------------------------------ *)

Definition well_formed_parser (p : Parser) : Prop :=
  parser_closed p /\
  list_norepet (parser_labels p) /\
  parser_progresses p.

Definition well_formed_parserb (p : Parser) : bool :=
  parser_closedb p && parser_labels_uniqueb p && parser_progressesb p.

(* ------------------------------------------------------------------ *)
(* Bridging lemmas                                                     *)
(* ------------------------------------------------------------------ *)

Lemma defined_label_In :
  forall p l, defined_label p l = true -> In l (parser_labels p).
Proof.
  intros p l H. unfold defined_label, lookup_def in H.
  destruct (find (fun d => posesque_eqb (psd_label d) l) (parser_states p))
    as [d|] eqn:Hf; [ | discriminate ].
  apply find_some in Hf. destruct Hf as [Hin Heq].
  apply posesque_eqb_iff in Heq. subst l.
  unfold parser_labels. apply in_map. exact Hin.
Qed.

Lemma lookup_def_In :
  forall p l d, lookup_def p l = Some d -> In l (parser_labels p).
Proof.
  intros p l d H. apply defined_label_In.
  unfold defined_label. rewrite H. reflexivity.
Qed.

(* The endpoint hypothesis [is_dag_prop_bool_lemma] needs. *)
Lemma nonconsuming_edges_endpoints :
  forall p u v,
    nonconsuming_edges p u v = true ->
    In u (parser_labels p) /\ In v (parser_labels p).
Proof.
  intros p u v H. unfold nonconsuming_edges in H.
  destruct (lookup_def p u) as [d|] eqn:Hd; [ | discriminate ].
  apply andb_prop in H. destruct H as [H _].
  apply andb_prop in H. destruct H as [_ Hdef].
  split.
  - eapply lookup_def_In. exact Hd.
  - apply defined_label_In. exact Hdef.
Qed.

Lemma parser_progresses_prop_bool_lemma :
  forall p, parser_progresses p <-> parser_progressesb p = true.
Proof.
  intros p. unfold parser_progresses, parser_progressesb.
  apply PosGraphLemmas.is_dag_prop_bool_lemma.
  apply nonconsuming_edges_endpoints.
Qed.

Lemma parser_labels_unique_prop_bool_lemma :
  forall p, list_norepet (parser_labels p) <-> parser_labels_uniqueb p = true.
Proof.
  intros p. unfold parser_labels_uniqueb. split.
  - intros Hnr.
    apply PosGraphLemmas.has_duplicates_false_iff_norepet in Hnr.
    rewrite Hnr. reflexivity.
  - intros Hb.
    apply PosGraphLemmas.has_duplicates_false_iff_norepet.
    destruct (has_duplicates posesque_eqb (parser_labels p)); [ discriminate | reflexivity ].
Qed.

Theorem well_formed_parser_prop_bool_lemma :
  forall p, well_formed_parser p <-> well_formed_parserb p = true.
Proof.
  intros p. unfold well_formed_parser, well_formed_parserb, parser_closed.
  split.
  - intros [Hc [Hnr Hpr]].
    apply andb_true_intro. split.
    + apply andb_true_intro. split.
      * exact Hc.
      * apply parser_labels_unique_prop_bool_lemma. exact Hnr.
    + apply parser_progresses_prop_bool_lemma. exact Hpr.
  - intros H.
    apply andb_prop in H. destruct H as [H Hpr].
    apply andb_prop in H. destruct H as [Hc Hnr].
    split; [ exact Hc | split ].
    + apply parser_labels_unique_prop_bool_lemma. exact Hnr.
    + apply parser_progresses_prop_bool_lemma. exact Hpr.
Qed.
