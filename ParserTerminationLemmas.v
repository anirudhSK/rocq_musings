(* ================================================================== *)
(* The concrete parser evaluator is total on well-formed parsers.     *)
(*                                                                    *)
(* [run_parser_concrete] returns [None] only when the run did not     *)
(* complete: the fuel ran out, or a transition named a state with no  *)
(* definition.  This file proves [well_formed_parser] rules both out, *)
(* so on a parser the checker is allowed to see the evaluator always  *)
(* delivers a verdict -- and the fuel constant in                     *)
(* [eval_parser_concrete] is big enough to be no constraint at all.   *)
(*                                                                    *)
(* The argument is a strictly decreasing measure, lexicographic in    *)
(* (bits left to read, rank of the state) and flattened to a [nat]:   *)
(*                                                                    *)
(*   parser_measure p lbl ps                                          *)
(*     = (|packet| - cursor) * |labels| + rank p lbl                  *)
(*                                                                    *)
(* A CONSUMING step drops the first term by at least |labels|, which  *)
(* dominates any rank increase because [rank < |labels|].  A          *)
(* NON-CONSUMING step leaves the cursor alone and strictly drops the  *)
(* rank, since a non-consuming edge must go "down" an acyclic graph.  *)
(* Bounded loops are admitted by the first component -- a state may   *)
(* be revisited once per cursor position -- which is what makes this  *)
(* weaker than requiring the parser itself to be a DAG.               *)
(*                                                                    *)
(* [rank] is a REACHABLE-SET CARDINALITY rather than a topological    *)
(* rank: the set of labels reachable from [lbl] by non-consuming      *)
(* edges.  Along an edge [u -> v] that set strictly shrinks -- it can *)
(* only lose members, and it loses [v], which is reachable from [u]   *)
(* but not from itself in an acyclic graph.  That needs only          *)
(* reachability and a counting lemma, both of which                   *)
(* [PosGraphLemmas] already has; a topological order would have had   *)
(* to be built from scratch.                                          *)
(* ================================================================== *)
From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrParser.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import ParserWellFormed.
From MyProject Require Import PosGraphLemmas.
From MyProject Require Import Coqlib.
From MyProject Require Import ListUtils.

Local Open Scope nat_scope.
Local Open Scope list_scope.

(* ------------------------------------------------------------------ *)
(* Reachability plumbing                                               *)
(* ------------------------------------------------------------------ *)

Lemma reaches_edge :
  forall (g : ParserStateLabel -> ParserStateLabel -> bool) u v, g u v = true -> reaches g u v.
Proof.
  intros g u v H. exists []. simpl. split; [exact H | exact I].
Qed.

Lemma reaches_trans :
  forall (g : ParserStateLabel -> ParserStateLabel -> bool) u v w,
    reaches g u v -> reaches g v w -> reaches g u w.
Proof.
  intros g u v w [m1 H1] [m2 H2].
  exists (m1 ++ v :: m2).
  rewrite <- app_assoc. simpl.
  apply (is_walk_app g u m1 v (m2 ++ [w])); [exact H1 | exact H2].
Qed.

Lemma list_norepet_filter :
  forall (f : ParserStateLabel -> bool) l,
    list_norepet l -> list_norepet (filter f l).
Proof.
  intros f l H. induction H as [| hd tl Hnin Hnr IH]; simpl.
  - constructor.
  - destruct (f hd) eqn:Hf.
    + constructor; [ | exact IH ].
      intros Hin. apply Hnin. apply filter_In in Hin. tauto.
    + exact IH.
Qed.

(* ------------------------------------------------------------------ *)
(* The rank                                                            *)
(* ------------------------------------------------------------------ *)

(* Labels reachable from [lbl] along non-consuming edges. *)
Definition nc_reach (p : Parser) (lbl : ParserStateLabel)
    : list ParserStateLabel :=
  List.filter
    (fun l' => reachableb_v (nonconsuming_edges p) (parser_labels p)
                 (List.length (parser_labels p)) [] lbl l')
    (parser_labels p).

Definition rank (p : Parser) (lbl : ParserStateLabel) : nat :=
  List.length (nc_reach p lbl).

Lemma nc_reach_sound :
  forall p lbl l',
    In l' (nc_reach p lbl) ->
    In l' (parser_labels p) /\ reaches (nonconsuming_edges p) lbl l'.
Proof.
  intros p lbl l' H. unfold nc_reach in H.
  apply filter_In in H. destruct H as [Hin Hb].
  split; [exact Hin | ].
  eapply reachableb_v_sound. exact Hb.
Qed.

Lemma nc_reach_complete :
  forall p lbl l',
    list_norepet (parser_labels p) ->
    In l' (parser_labels p) ->
    reaches (nonconsuming_edges p) lbl l' ->
    In l' (nc_reach p lbl).
Proof.
  intros p lbl l' Hnr Hin [mid Hwalk].
  unfold nc_reach. apply filter_In. split; [exact Hin | ].
  (* Shorten the walk so its interior repeats no vertex, hence is no
     longer than the label list -- which is the fuel [nc_reach] uses. *)
  destruct (shorten_walk_nodup _ _ _ _ Hwalk) as [mid' [Hw' [Hdup' _]]].
  assert (Hmid_in : forall w, In w mid' -> In w (parser_labels p)).
  { intros w Hw. eapply walk_mid_in_nodes;
      [ apply nonconsuming_edges_endpoints | exact Hw' | exact Hw ]. }
  assert (Hnd : list_norepet mid').
  { apply has_duplicates_false_iff_norepet. exact Hdup'. }
  eapply walk_reachableb_v.
  - exact Hmid_in.
  - intros w _ Hc. exact Hc.
  - apply list_norepet_NoDup. exact Hnd.
  - exact Hw'.
  - apply norepet_incl_length; [ exact Hnd | exact Hmid_in ].
Qed.

(* In an acyclic graph nothing reaches itself, so a label is never in its
   own reachable set. *)
Lemma nc_reach_irrefl :
  forall p lbl,
    parser_progresses p -> ~ In lbl (nc_reach p lbl).
Proof.
  intros p lbl Hdag Hin.
  apply nc_reach_sound in Hin. destruct Hin as [_ Hr].
  exact (Hdag lbl Hr).
Qed.

(* The key step: a non-consuming edge strictly drops the rank. *)
Lemma rank_decreases :
  forall p u v,
    well_formed_parser p ->
    nonconsuming_edges p u v = true ->
    rank p v < rank p u.
Proof.
  intros p u v [_ [Hnr Hdag]] Hedge.
  unfold rank.
  (* [v :: nc_reach p v] is duplicate-free and sits inside [nc_reach p u]. *)
  assert (Hincl : forall w, In w (v :: nc_reach p v) -> In w (nc_reach p u)).
  { intros w Hw. destruct Hw as [Heq | Hw].
    - subst w. apply nc_reach_complete; [ exact Hnr | | ].
      + exact (proj2 (nonconsuming_edges_endpoints _ _ _ Hedge)).
      + apply reaches_edge. exact Hedge.
    - apply nc_reach_sound in Hw. destruct Hw as [Hwin Hwr].
      apply nc_reach_complete; [ exact Hnr | exact Hwin | ].
      eapply reaches_trans; [ apply reaches_edge; exact Hedge | exact Hwr ]. }
  assert (Hnodup : list_norepet (v :: nc_reach p v)).
  { constructor.
    - apply nc_reach_irrefl. exact Hdag.
    - apply list_norepet_filter. exact Hnr. }
  pose proof (norepet_incl_length _ _ Hnodup Hincl) as Hlen.
  simpl in Hlen. lia.
Qed.

(* And a rank is always below the number of labels, which is what lets a
   consuming step's progress dominate any rank increase. *)
Lemma rank_lt_labels :
  forall p lbl,
    well_formed_parser p ->
    In lbl (parser_labels p) ->
    rank p lbl < List.length (parser_labels p).
Proof.
  intros p lbl [_ [Hnr Hdag]] Hin.
  unfold rank.
  assert (Hincl : forall w, In w (lbl :: nc_reach p lbl) -> In w (parser_labels p)).
  { intros w [Heq | Hw]; [ subst w; exact Hin | ].
    exact (proj1 (nc_reach_sound _ _ _ Hw)). }
  assert (Hnodup : list_norepet (lbl :: nc_reach p lbl)).
  { constructor.
    - apply nc_reach_irrefl. exact Hdag.
    - apply list_norepet_filter. exact Hnr. }
  pose proof (norepet_incl_length _ _ Hnodup Hincl) as Hlen.
  simpl in Hlen. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* What a step does to the parser state                                *)
(* ------------------------------------------------------------------ *)

Lemma apply_extract_packet :
  forall po ps ps',
    apply_extract_concrete po ps = Some ps' -> p_packet ps' = p_packet ps.
Proof.
  intros po ps ps' H. destruct po; simpl in H;
    destruct (Nat.leb _ _) eqn:Hle; inversion H; reflexivity.
Qed.

Lemma apply_extract_cursor_bound :
  forall po ps ps',
    apply_extract_concrete po ps = Some ps' ->
    p_cursor ps' <= List.length (p_packet ps').
Proof.
  intros po ps ps' H. destruct po; simpl in H;
    destruct (Nat.leb (p_cursor ps + width) (List.length (p_packet ps))) eqn:Hle;
    inversion H; subst; simpl; apply Nat.leb_le in Hle; exact Hle.
Qed.

Lemma apply_extract_cursor_ge :
  forall po ps ps',
    apply_extract_concrete po ps = Some ps' -> p_cursor ps <= p_cursor ps'.
Proof.
  intros po ps ps' H. destruct po; simpl in H;
    destruct (Nat.leb _ _) eqn:Hle; inversion H; subst; simpl; lia.
Qed.

Lemma apply_extract_cursor_gt :
  forall po ps ps',
    op_consumes po = true ->
    apply_extract_concrete po ps = Some ps' -> p_cursor ps < p_cursor ps'.
Proof.
  intros po ps ps' Hc H. destruct po; simpl in Hc, H;
    apply Nat.ltb_lt in Hc;
    destruct (Nat.leb _ _) eqn:Hle; inversion H; subst; simpl; lia.
Qed.

Lemma apply_extract_cursor_eq :
  forall po ps ps',
    op_consumes po = false ->
    apply_extract_concrete po ps = Some ps' -> p_cursor ps' = p_cursor ps.
Proof.
  intros po ps ps' Hc H. destruct po; simpl in Hc, H;
    (destruct width as [| w]; [ | simpl in Hc; discriminate ]);
    destruct (Nat.leb _ _) eqn:Hle; inversion H; subst; simpl; lia.
Qed.

(* Everything the main proof needs to know about applying a state's action,
   in one statement.  Packaged this way because the action is a MATCH on
   [psd_action], and neither [destruct ... eqn:] nor [remember] will abstract
   a match out of the goal -- but a plain [rewrite] with this equation will. *)
Lemma action_result :
  forall def ps,
    (match psd_action def with
     | None => Some ps
     | Some po => apply_extract_concrete po ps
     end) = None
    \/ exists ps',
         (match psd_action def with
          | None => Some ps
          | Some po => apply_extract_concrete po ps
          end) = Some ps'
         /\ p_packet ps' = p_packet ps
         /\ (p_cursor ps <= List.length (p_packet ps) ->
             p_cursor ps' <= List.length (p_packet ps'))
         /\ (state_consumes def = true -> p_cursor ps < p_cursor ps')
         /\ (state_consumes def = false -> p_cursor ps' = p_cursor ps).
Proof.
  intros def ps. unfold state_consumes.
  destruct (psd_action def) as [po |] eqn:Hpo.
  - destruct (apply_extract_concrete po ps) as [ps' |] eqn:Hac.
    + right. exists ps'. repeat split.
      * eapply apply_extract_packet. exact Hac.
      * intros _. eapply apply_extract_cursor_bound. exact Hac.
      * intros Hc. eapply apply_extract_cursor_gt; [ exact Hc | exact Hac ].
      * intros Hc. eapply apply_extract_cursor_eq; [ exact Hc | exact Hac ].
    + left. reflexivity.
  - right. exists ps. repeat split.
    + intros H. exact H.
    + intros Hc. discriminate.
Qed.

(* ------------------------------------------------------------------ *)
(* Where a transition can go                                           *)
(* ------------------------------------------------------------------ *)

Lemma resolve_select_target :
  forall ps cases default,
    resolve_select_concrete ps cases default = default \/
    exists c, In c cases /\ resolve_select_concrete ps cases default = sc_target c.
Proof.
  intros ps cases default. induction cases as [| c rest IH]; simpl.
  - left. reflexivity.
  - destruct (select_case_matches_concrete ps c) eqn:Hm.
    + right. exists c. split; [ left; reflexivity | reflexivity ].
    + destruct IH as [Hd | [c' [Hin Heq]]].
      * left. exact Hd.
      * right. exists c'. split; [ right; exact Hin | exact Heq ].
Qed.

Lemma In_target_labels :
  forall ts s, In (TargetState s) ts -> In s (target_labels ts).
Proof.
  intros ts s H. induction ts as [| t rest IH]; simpl in *.
  - contradiction.
  - destruct H as [Heq | H].
    + subst t. simpl. left. reflexivity.
    + destruct t; simpl; try (right; apply IH; exact H); apply IH; exact H.
Qed.

Lemma eval_transition_successor :
  forall ps t next,
    eval_transition_concrete ps t = Some (TargetState next) ->
    In next (target_labels (transition_targets t)).
Proof.
  intros ps t next H. destruct t as [tgt | cases default]; simpl in H.
  - inversion H. subst tgt. simpl. left. reflexivity.
  - destruct (select_bits_available_concrete ps cases); [ | discriminate ].
    inversion H as [Hres].
    destruct (resolve_select_target ps cases default) as [Hd | [c [Hin Heq]]].
    + apply In_target_labels. simpl. left. rewrite <- Hd, Hres. reflexivity.
    + apply In_target_labels. simpl. right.
      apply in_map_iff. exists c. split; [ | exact Hin ].
      rewrite <- Heq, Hres. reflexivity.
Qed.

(* Closure: a successor of a defined state is itself defined. *)
Lemma closed_successor_defined :
  forall p lbl def next,
    parser_closed p ->
    lookup_def p lbl = Some def ->
    In next (state_successors def) ->
    defined_label p next = true.
Proof.
  intros p lbl def next Hc Hd Hin.
  unfold parser_closed, parser_closedb in Hc.
  apply andb_prop in Hc. destruct Hc as [_ Hall].
  rewrite forallb_forall in Hall.
  unfold lookup_def in Hd. apply find_some in Hd. destruct Hd as [Hdin _].
  specialize (Hall def Hdin). rewrite forallb_forall in Hall.
  exact (Hall next Hin).
Qed.

(* ------------------------------------------------------------------ *)
(* The measure                                                         *)
(* ------------------------------------------------------------------ *)

Definition parser_measure (p : Parser) (lbl : ParserStateLabel)
    (ps : ConcreteParserState) : nat :=
  (List.length (p_packet ps) - p_cursor ps) * List.length (parser_labels p)
  + rank p lbl.

(* ------------------------------------------------------------------ *)
(* Totality                                                            *)
(* ------------------------------------------------------------------ *)

Theorem run_parser_no_fuel_starvation :
  forall n p lbl ps fuel,
    well_formed_parser p ->
    In lbl (parser_labels p) ->
    p_cursor ps <= List.length (p_packet ps) ->
    parser_measure p lbl ps <= n ->
    n < fuel ->
    run_parser_concrete p lbl ps fuel <> None.
Proof.
  intros n. induction n as [n IH] using (well_founded_induction lt_wf).
  intros p lbl ps fuel Hwf Hin Hcur Hm Hnf.
  destruct fuel as [| fuel']; [ lia | ].
  simpl.
  (* The state is defined, by [In lbl (parser_labels p)]. *)
  destruct (lookup_def p lbl) as [def |] eqn:Hdef.
  2:{ exfalso. unfold parser_labels in Hin. apply in_map_iff in Hin.
      destruct Hin as [d [Hlbl Hdin]].
      unfold lookup_def in Hdef.
      pose proof (find_none _ _ Hdef d Hdin) as Hfalse.
      cbn beta in Hfalse. subst lbl.
      rewrite posesque_eqb_refl in Hfalse. discriminate. }
  (* Apply the action.  [rewrite Hact], not [destruct ... eqn:] -- the action
     is a match on [psd_action def] and neither [destruct] nor [remember]
     abstracts a match out of the goal. *)
  destruct (action_result def ps) as [Hnone | [ps' (Hact & Hpkt & Hbound & Hgt & Hsame)]].
  { rewrite Hnone. discriminate. }
  rewrite Hact.
  assert (Hcur' : p_cursor ps' <= List.length (p_packet ps')) by (apply Hbound; exact Hcur).
  destruct (eval_transition_concrete ps' (psd_trans def)) as [tgt |] eqn:Htr;
    [ | discriminate ].
  destruct tgt as [next | |]; [ | discriminate | discriminate ].
  (* The recursive case: show the measure strictly dropped. *)
  assert (Hnext_succ : In next (state_successors def)).
  { unfold state_successors. eapply eval_transition_successor. exact Htr. }
  assert (Hnext_def : defined_label p next = true).
  { eapply closed_successor_defined;
      [ exact (proj1 Hwf) | exact Hdef | exact Hnext_succ ]. }
  assert (Hnext_in : In next (parser_labels p)).
  { apply defined_label_In. exact Hnext_def. }
  assert (Hdrop : parser_measure p next ps' < parser_measure p lbl ps).
  { unfold parser_measure. rewrite Hpkt.
    destruct (state_consumes def) eqn:Hcons.
    - (* Consuming: the cursor advanced, so the first term fell by |labels|,
         which beats any rank increase since every rank is below |labels|. *)
      specialize (Hgt eq_refl).
      pose proof (rank_lt_labels p next Hwf Hnext_in) as Hrk.
      rewrite Hpkt in Hcur'.
      assert (Hle : List.length (p_packet ps) - p_cursor ps'
                    <= List.length (p_packet ps) - p_cursor ps - 1) by lia.
      assert (Hpos : 1 <= List.length (p_packet ps) - p_cursor ps) by lia.
      set (N := List.length (parser_labels p)) in *.
      set (a := List.length (p_packet ps) - p_cursor ps) in *.
      set (b := List.length (p_packet ps) - p_cursor ps') in *.
      assert (Hmul : b * N <= (a - 1) * N) by (apply Nat.mul_le_mono_r; lia).
      assert (Hexp : (a - 1) * N + N = a * N).
      { replace a with ((a - 1) + 1) at 2 by lia.
        rewrite Nat.mul_add_distr_r. lia. }
      lia.
    - (* Non-consuming: the cursor is unchanged and the rank strictly fell. *)
      specialize (Hsame eq_refl). rewrite Hsame.
      assert (Hedge : nonconsuming_edges p lbl next = true).
      { unfold nonconsuming_edges. rewrite Hdef, Hcons, Hnext_def. simpl.
        apply existsb_exists. exists next.
        split; [ exact Hnext_succ | apply posesque_eqb_refl ]. }
      pose proof (rank_decreases p lbl next Hwf Hedge) as Hrk. lia. }
  (* Recurse.  The new measure is below [n], and below [fuel']. *)
  eapply IH.
  - instantiate (1 := parser_measure p next ps'). lia.
  - exact Hwf.
  - exact Hnext_in.
  - exact Hcur'.
  - reflexivity.
  - lia.
Qed.

(* The fuel [eval_parser_concrete] passes is exactly adequate: the measure at
   the start is [(|packet| - 0) * N + rank <= |packet| * N + (N - 1)], and the
   fuel is [N * (|packet| + 1)], one more. *)
Theorem eval_parser_no_fuel_starvation :
  forall p ps,
    well_formed_parser p ->
    p_cursor ps = 0 ->
    eval_parser_concrete p ps <> None.
Proof.
  intros p ps Hwf Hcur0.
  unfold eval_parser_concrete.
  assert (Hstart : In (parser_start p) (parser_labels p)).
  { apply defined_label_In.
    destruct Hwf as [Hc _]. unfold parser_closed, parser_closedb in Hc.
    apply andb_prop in Hc. exact (proj1 Hc). }
  pose proof (rank_lt_labels p (parser_start p) Hwf Hstart) as Hrk.
  (* [parser_labels] and [parser_states] have the same length. *)
  assert (Hlen : List.length (parser_labels p) = List.length (parser_states p)).
  { unfold parser_labels. apply length_map. }
  eapply run_parser_no_fuel_starvation with
    (n := parser_measure p (parser_start p) ps).
  - exact Hwf.
  - exact Hstart.
  - rewrite Hcur0. lia.
  - reflexivity.
  - unfold parser_measure. rewrite Hcur0, Nat.sub_0_r, Hlen in *.
    rewrite Nat.mul_succ_r. nia.
Qed.

Print Assumptions run_parser_no_fuel_starvation.
Print Assumptions eval_parser_no_fuel_starvation.
