From Stdlib Require Import List.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import Coqlib.
From MyProject Require Import ListUtils.
From Stdlib Require Import PArith.BinPos.


Local Open Scope list_scope.
Local Open Scope nat_scope.

Section PosGraph.
Context {A : Type} {PA : Posesque A}.

Definition graph := A -> A -> bool.

Fixpoint is_walk (g : graph) (vs : list A) : Prop :=
  match vs with
  | [] => True
  | [_] => True
  | u :: (v :: _) as rest => g u v = true /\ is_walk g rest
  end.

Definition reaches (g : graph) (x y : A) : Prop :=
  exists mid : list A,
    is_walk g (x :: mid ++ [y]).

(* [reachableb] is the specification of bounded reachability: a plain
   fuel-bounded DFS with no pruning. *)
Fixpoint reachableb (g : graph) (nodes : list A) (fuel : nat)
                     (src dst : A) : bool :=
  match fuel with
  | O => g src dst
  | S fuel' =>
      g src dst
      || existsb (fun w => g src w && reachableb g nodes fuel' w dst) nodes
  end.

(* Boolean membership test in a list of [A]. *)
Definition in_listb (l : list A) (x : A) : bool :=
  existsb (fun y => posesque_eqb y x) l.

Lemma in_listb_spec :
  forall l x, in_listb l x = true <-> In x l.
Proof.
  intros l x. unfold in_listb. rewrite existsb_exists. split.
  - intros [y [Hy Heq]]. apply posesque_eqb_iff in Heq. subst y. exact Hy.
  - intros Hin. exists x. split; [exact Hin | apply posesque_eqb_refl].
Qed.

(* [reachableb_v] is the performant implementation: it carries a [visited]
   set and prunes any neighbour already on the current search path.  This
   prevents the exponential re-exploration of the unpruned [reachableb].
   It is proved equivalent (for the [is_dagb] use, two-sided) below. *)
Fixpoint reachableb_v (g : graph) (nodes : list A) (fuel : nat)
                      (visited : list A) (src dst : A) : bool :=
  match fuel with
  | O => g src dst
  | S fuel' =>
      g src dst
      || existsb (fun w => g src w
                           && negb (in_listb visited w)
                           && reachableb_v g nodes fuel' (w :: visited) w dst)
                 nodes
  end.

Definition is_dag (g : graph) : Prop :=
  forall x : A, ~ reaches g x x.

Definition is_dagb (g : graph) (nodes : list A) : bool :=
  forallb (fun x => negb (reachableb_v g nodes (length nodes) [] x x)) nodes.

(* ------------------------------------------------------------------ *)
(* Relating walks to bounded reachability                             *)
(* ------------------------------------------------------------------ *)

Lemma reachableb_sound :
  forall g nodes fuel src dst,
    reachableb g nodes fuel src dst = true ->
    reaches g src dst.
Proof.
  intros g nodes fuel.
  induction fuel as [|fuel' IH]; intros src dst H.
  - (* fuel = 0 : direct edge *)
    simpl in H. exists []. simpl. split; [exact H | exact I].
  - simpl in H. apply orb_prop in H. destruct H as [H | H].
    + (* direct edge *)
      exists []. simpl. split; [exact H | exact I].
    + apply existsb_exists in H. destruct H as [w [_ Hw]].
      apply andb_prop in Hw. destruct Hw as [Hedge Hrec].
      apply IH in Hrec. destruct Hrec as [mid Hwalk].
      (* edge src -> w, then walk w ... dst *)
      exists (w :: mid).
      simpl. split.
      * exact Hedge.
      * exact Hwalk.
Qed.

(* ------------------------------------------------------------------ *)
(* Bridging the pruned implementation [reachableb_v] to the spec       *)
(* [reachableb].                                                       *)
(* ------------------------------------------------------------------ *)

(* Soundness: the pruned search only ever takes a subset of the branches
   of the unpruned search (it adds the [negb (in_listb visited w)]
   conjunct), so whatever it finds, [reachableb] finds too — for any
   [visited]. *)
Lemma reachableb_v_sound_aux :
  forall g nodes fuel visited src dst,
    reachableb_v g nodes fuel visited src dst = true ->
    reachableb g nodes fuel src dst = true.
Proof.
  intros g nodes fuel.
  induction fuel as [|fuel' IH]; intros visited src dst H.
  - simpl in *. exact H.
  - simpl in H. simpl. apply orb_prop in H. destruct H as [H | H].
    + rewrite H. reflexivity.
    + apply orb_true_intro. right.
      apply existsb_exists in H. destruct H as [w [Hwin Hw]].
      apply existsb_exists. exists w. split; [exact Hwin |].
      apply andb_prop in Hw. destruct Hw as [Hw1 Hrec].
      apply andb_prop in Hw1. destruct Hw1 as [Hedge _Hnv].
      apply andb_true_intro. split; [exact Hedge |].
      apply IH in Hrec. exact Hrec.
Qed.

Lemma reachableb_v_sound :
  forall g nodes fuel src dst,
    reachableb_v g nodes fuel [] src dst = true ->
    reaches g src dst.
Proof.
  intros g nodes fuel src dst H.
  apply reachableb_v_sound_aux in H.
  apply (reachableb_sound g nodes fuel src dst H).
Qed.

(* Completeness: a walk whose intermediate vertices avoid [visited] (and
   that fits in [fuel]) is found by the pruned search.  The disjointness
   invariant is exactly what justifies skipping the pruned branches: the
   next vertex on such a walk is never already in [visited]. *)
Lemma walk_reachableb_v :
  forall g nodes mid src dst fuel visited,
    (forall w, In w mid -> In w nodes) ->
    (forall w, In w mid -> ~ In w visited) ->
    NoDup mid ->
    is_walk g (src :: mid ++ [dst]) ->
    length mid <= fuel ->
    reachableb_v g nodes fuel visited src dst = true.
Proof.
  intros g nodes mid. induction mid as [|m mid' IH];
    intros src dst fuel visited Hin Hdisj Hnd Hwalk Hlen.
  - (* mid = [] : single edge src -> dst *)
    simpl in Hwalk. destruct Hwalk as [Hedge _].
    destruct fuel; simpl.
    + exact Hedge.
    + rewrite Hedge. reflexivity.
  - (* mid = m :: mid' *)
    simpl in Hwalk. destruct Hwalk as [Hedge Hrest].
    destruct fuel as [|fuel'].
    + simpl in Hlen. lia.
    + simpl. apply orb_true_intro. right.
      apply existsb_exists. exists m. split.
      * apply Hin. left. reflexivity.
      * apply andb_true_intro. split.
        -- apply andb_true_intro. split.
           ++ exact Hedge.
           ++ (* m is not in visited *)
              apply negb_true_iff.
              destruct (in_listb visited m) eqn:Hmv; [| reflexivity].
              exfalso. apply in_listb_spec in Hmv.
              apply (Hdisj m (or_introl eq_refl) Hmv).
        -- (* recurse with m added to visited *)
           apply IH.
           ++ intros w Hw. apply Hin. right. exact Hw.
           ++ (* intermediate vertices avoid (m :: visited) *)
              intros w Hw Hwin. simpl in Hwin. destruct Hwin as [Heq | Hwin].
              ** subst w. inversion Hnd; subst. contradiction.
              ** apply (Hdisj w (or_intror Hw) Hwin).
           ++ inversion Hnd; subst. assumption.
           ++ exact Hrest.
           ++ simpl in Hlen. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Shortening walks: a walk whose intermediate vertices all lie in     *)
(* [nodes] can be reduced to one with no repeated intermediate vertex, *)
(* hence with at most |nodes| intermediate vertices.                   *)
(* ------------------------------------------------------------------ *)

Lemma is_walk_app :
  forall g a l1 w l2,
    is_walk g (a :: l1 ++ [w]) ->
    is_walk g (w :: l2) ->
    is_walk g (a :: l1 ++ w :: l2).
Proof.
  intros g a l1. revert a.
  induction l1 as [|b l1' IH]; intros a w l2 H1 H2.
  - (* l1 = [] : walk is a :: [w], second is w :: l2 *)
    simpl in H1. destruct H1 as [Hedge _].
    simpl. destruct l2 as [|c l2'].
    + simpl. split; [exact Hedge | exact I].
    + simpl. split; [exact Hedge | exact H2].
  - (* l1 = b :: l1' *)
    simpl in H1. destruct H1 as [Hedge Hrest].
    simpl. split.
    + exact Hedge.
    + change (is_walk g (b :: l1' ++ w :: l2)).
      apply IH.
      * exact Hrest.
      * exact H2.
Qed.

Lemma walk_mid_in_nodes :
  forall g nodes x mid y,
    (forall u v, g u v = true -> In u nodes /\ In v nodes) ->
    is_walk g (x :: mid ++ [y]) ->
    forall w, In w mid -> In w nodes.
Proof.
  intros g nodes x mid. revert x.
  induction mid as [|m mid' IH]; intros x y Hedges Hwalk w Hw.
  - simpl in Hw. contradiction.
  - simpl in Hwalk. destruct Hwalk as [Hedge Hrest].
    simpl in Hw. destruct Hw as [Heq | Hw].
    + subst w. apply (Hedges x m Hedge).
    + eapply IH; eauto.
Qed.

(* ------------------------------------------------------------------ *)
(* Pigeonhole: a reaches-walk can be made short.                       *)
(* ------------------------------------------------------------------ *)

Lemma remove_one_repeat :
  forall g x y mid,
    is_walk g (x :: mid ++ [y]) ->
    has_duplicates posesque_eqb mid = true ->
    exists mid',
      is_walk g (x :: mid' ++ [y]) /\ length mid' < length mid.
Proof.
  intros g x y mid Hwalk Hdup.
  (* Find a duplicated element and split. *)
  (* From has_duplicates = true, get w appearing twice. *)
  assert (exists (l1 : list A) (w : A) (l2 l3 : list A),
            mid = l1 ++ w :: l2 ++ w :: l3) as Hsplit.
  { clear Hwalk. induction mid as [|a mid' IH].
    - simpl in Hdup. discriminate.
    - simpl in Hdup.
      destruct (existsb (fun y0 => posesque_eqb y0 a) mid') eqn:Hex.
      + apply existsb_exists in Hex. destruct Hex as [b [Hbin Hbeq]].
        apply posesque_eqb_iff in Hbeq. subst b.
        apply in_split in Hbin. destruct Hbin as [l2 [l3 Hmid']].
        exists [], a, l2, l3. simpl. rewrite Hmid'. reflexivity.
      + apply IH in Hdup. destruct Hdup as [l1 [w [l2 [l3 Heq]]]].
        exists (a :: l1), w, l2, l3. simpl. rewrite Heq. reflexivity. }
  destruct Hsplit as [l1 [w [l2 [l3 Hmid]]]].
  subst mid.
  (* The walk is x :: l1 ++ w :: l2 ++ w :: l3 ++ [y].
     Cut out the segment between the two w's:
     new walk: x :: l1 ++ w :: l3 ++ [y]. *)
  exists (l1 ++ w :: l3).
  split.
  - (* build the shortened walk *)
    (* original: is_walk g (x :: (l1 ++ w :: l2 ++ w :: l3) ++ [y]) *)
    (* We will split the original into prefix walk to w and suffix walk
       from the second w. *)
    (* Use is_walk_app with a:=x, l1 := l1 ++ [w], l2 := l3 ++ [y]. *)
    (* First, extract that the prefix x :: l1 ++ [w] is a walk, and that
       w :: l3 ++ [y] is a walk. *)
    assert (Hpre : is_walk g (x :: l1 ++ [w])).
    { (* prefix of the original walk *)
      revert Hwalk. clear.
      generalize (l2 ++ w :: l3 ++ [y]).
      intro tail. revert x.
      induction l1 as [|a l1' IH]; intros x Hwalk.
      - simpl. simpl in Hwalk. destruct Hwalk as [Hedge _].
        split; [exact Hedge | exact I].
      - simpl in Hwalk. destruct Hwalk as [Hedge Hrest].
        simpl. split.
        + exact Hedge.
        + change (is_walk g (a :: l1' ++ [w])).
          apply IH. exact Hrest. }
    assert (Hsuf : is_walk g (w :: l3 ++ [y])).
    { (* suffix of the original walk: skip x :: l1 ++ [w] ++ l2 *)
      revert Hwalk. clear.
      (* The original tail after the first w is: w :: l2 ++ w :: l3 ++ [y].
         We need a walk from the SECOND w.  First obtain the walk starting
         at the first w, then peel l2 to reach the second w. *)
      (* Get walk starting at first w. *)
      assert (Hstart :
        forall pre z,
          is_walk g (z :: pre ++ (w :: l2 ++ w :: l3 ++ [y])) ->
          is_walk g (w :: l2 ++ w :: l3 ++ [y])).
      { induction pre as [|a pre' IH]; intros z Hw.
        - simpl in Hw. destruct Hw as [_ Hrest]. exact Hrest.
        - apply (IH a).
          change (is_walk g (z :: a :: pre' ++ w :: l2 ++ w :: l3 ++ [y]))
            in Hw.
          destruct Hw as [_ Hrest]. exact Hrest. }
      intro Hwalk.
      assert (Hwfull : is_walk g (w :: l2 ++ w :: l3 ++ [y])).
      { apply (Hstart l1 x).
        (* Hwalk : is_walk g (x :: (l1 ++ w :: l2 ++ w :: l3) ++ [y]) *)
        replace (l1 ++ w :: l2 ++ w :: l3 ++ [y])
           with ((l1 ++ w :: l2 ++ w :: l3) ++ [y]).
        2:{ rewrite <- app_assoc. simpl.
            rewrite <- app_assoc. simpl. reflexivity. }
        exact Hwalk. }
      (* Now peel l2 from w :: l2 ++ w :: ... to reach the second w. *)
      revert Hwfull. clear.
      assert (Hpeel :
        forall pre z,
          is_walk g (z :: pre ++ (w :: l3 ++ [y])) ->
          is_walk g (w :: l3 ++ [y])).
      { induction pre as [|a pre' IH]; intros z Hw.
        - simpl in Hw. destruct Hw as [_ Hrest]. exact Hrest.
        - apply (IH a).
          change (is_walk g (z :: a :: pre' ++ w :: l3 ++ [y])) in Hw.
          destruct Hw as [_ Hrest]. exact Hrest. }
      intro Hwfull. apply (Hpeel l2 w). exact Hwfull. }
    (* combine prefix (x..w) and suffix (w..y) *)
    replace (x :: (l1 ++ w :: l3) ++ [y])
       with (x :: l1 ++ w :: (l3 ++ [y])).
    2:{ rewrite <- app_assoc. simpl. reflexivity. }
    apply is_walk_app.
    + exact Hpre.
    + exact Hsuf.
  - (* length decreases: we removed [w] ++ l2 (at least one element) *)
    repeat rewrite length_app. simpl.
    repeat rewrite length_app. simpl. lia.
Qed.

Lemma shorten_walk_nodup :
  forall g x y mid,
    is_walk g (x :: mid ++ [y]) ->
    exists mid',
      is_walk g (x :: mid' ++ [y]) /\
      has_duplicates posesque_eqb mid' = false /\
      length mid' <= length mid.
Proof.
  intros g x y mid.
  remember (length mid) as n eqn:Hn.
  revert mid Hn.
  induction n as [n IH] using (well_founded_induction lt_wf);
    intros mid Hn Hwalk.
  destruct (has_duplicates posesque_eqb mid) eqn:Hdup.
  - destruct (remove_one_repeat g x y mid Hwalk Hdup)
      as [mid' [Hwalk' Hlen]].
    destruct (IH (length mid') ltac:(lia) mid' eq_refl Hwalk')
      as [mid'' [Hw'' [Hd'' Hl'']]].
    exists mid''. split; [exact Hw'' | split; [exact Hd'' | lia]].
  - exists mid. split; [exact Hwalk | split; [exact Hdup | lia]].
Qed.

Lemma list_norepet_NoDup :
  forall (l : list A), list_norepet l -> NoDup l.
Proof.
  intros l H. induction H; constructor; assumption.
Qed.

Lemma norepet_incl_length :
  forall (l m : list A),
    list_norepet l ->
    (forall w, In w l -> In w m) ->
    length l <= length m.
Proof.
  intros l m Hnr Hincl.
  apply NoDup_incl_length.
  - apply list_norepet_NoDup. exact Hnr.
  - intros w Hw. apply Hincl. exact Hw.
Qed.

Lemma has_duplicates_false_iff_norepet :
  forall l, has_duplicates posesque_eqb l = false <-> list_norepet l.
Proof.
  intros l.
  split.
  - apply (has_duplicates_correct A posesque_eqb (@posesque_eqb_refl A _) (@posesque_eqb_sym A _)).
  - intros Hnr. induction Hnr.
    + reflexivity.
    + simpl.
      assert (Hex : existsb (fun y => posesque_eqb y hd) tl = false).
      { destruct (existsb (fun y => posesque_eqb y hd) tl) eqn:E; [ | reflexivity ].
        exfalso. apply H. apply (in_listb_spec tl hd). unfold in_listb. exact E. }
      rewrite Hex. apply IHHnr.
Qed.

(* ------------------------------------------------------------------ *)
(* Main lemma                                                          *)
(* ------------------------------------------------------------------ *)

Lemma is_dag_prop_bool_lemma :
  forall (g : graph) (nodes : list A),
    (forall u v, g u v = true -> In u nodes /\ In v nodes) ->
    (is_dag g <-> is_dagb g nodes = true).
Proof.
  intros g nodes Hedges. split.
  - (* is_dag -> is_dagb *)
    intros Hdag.
    unfold is_dagb. apply forallb_forall.
    intros x Hx.
    apply negb_true_iff.
    destruct (reachableb_v g nodes (length nodes) [] x x) eqn:Hr.
    + (* contradiction: reachableb_v finds a self-walk *)
      exfalso. apply (Hdag x).
      apply (reachableb_v_sound g nodes (length nodes) x x Hr).
    + reflexivity.
  - (* is_dagb -> is_dag *)
    intros Hdagb x [mid Hwalk].
    (* shorten the walk to a no-duplicate one *)
    destruct (shorten_walk_nodup g x x mid Hwalk)
      as [mid' [Hwalk' [Hnodup _]]].
    (* its intermediate vertices are in nodes *)
    assert (Hin : forall w, In w mid' -> In w nodes).
    { apply (walk_mid_in_nodes g nodes x mid' x Hedges Hwalk'). }
    (* the shortened walk has no repeated intermediate vertex *)
    assert (Hnd : NoDup mid').
    { apply list_norepet_NoDup. apply has_duplicates_false_iff_norepet. exact Hnodup. }
    (* hence its length is <= |nodes| *)
    assert (Hlen : length mid' <= length nodes).
    { apply norepet_incl_length.
      - apply has_duplicates_false_iff_norepet. exact Hnodup.
      - exact Hin. }
    (* so the pruned search finds it (visited starts empty) *)
    assert (Hr : reachableb_v g nodes (length nodes) [] x x = true).
    { apply (walk_reachableb_v g nodes mid' x x (length nodes) []).
      - exact Hin.
      - intros w _ Hwin. exact Hwin.
      - exact Hnd.
      - exact Hwalk'.
      - exact Hlen. }
    (* but is_dagb says it must be false *)
    unfold is_dagb in Hdagb.
    rewrite forallb_forall in Hdagb.
    (* x is in nodes because the walk has at least one edge from x *)
    assert (Hxin : In x nodes).
    { (* first edge of the walk: g x (head of mid' ++ [x]) *)
      destruct mid' as [|m ms].
      - simpl in Hwalk'. destruct Hwalk' as [Hedge _].
        apply (Hedges x x Hedge).
      - simpl in Hwalk'. destruct Hwalk' as [Hedge _].
        apply (Hedges x m Hedge). }
    specialize (Hdagb x Hxin).
    apply negb_true_iff in Hdagb.
    rewrite Hr in Hdagb. discriminate.
Qed.

End PosGraph.
