(* Concrete<->symbolic parser commutation lemmas: the supporting machinery for
   [SmtParserQuery]'s soundness and completeness (the parser analogue of
   [ConcreteToSymbolicLemmas] for transformers).  Culminates in
   [eval_parser_commute]. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.
From MyProject Require Import Integers.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import Maps.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import ParserWellFormed.
From MyProject Require Import ParserTerminationLemmas.

From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrSymbolicSemanticsModule.

(* ====================================================================== *)
(* Presence: which bits of a symbolic bitstream are actually THERE.        *)
(*                                                                        *)
(* A read tape concretizes through [present_bits] -- keep the positions    *)
(* whose [cvc] holds under [f] -- because [merge_bitstream] pads the       *)
(* shorter branch of a [select] with absent positions and a concrete run   *)
(* leaves only the branch it took.  See TODO 1.1.1 for why concretizing    *)
(* read tapes POSITIONALLY is not merely unprovable but gives a wrong      *)
(* verdict.                                                               *)
(*                                                                        *)
(* Two things are developed here, both groundwork for parser commutation:  *)
(*                                                                        *)
(*   - [merge_bitstream_present_true]/[_false]: the merged residual's      *)
(*     present bits are exactly the SELECTED branch's.  This is the        *)
(*     bitstream half of: a merged result concretizes to the branch that   *)
(*     the valuation picks.  It needs no invariant.                        *)
(*                                                                        *)
(*   - [pprefix]: the presence-prefix invariant.  Absent positions are a   *)
(*     SUFFIX, so [present_bits l f] is a PREFIX of the positional         *)
(*     concretization rather than a compaction of scattered survivors.     *)
(*     Without it the concrete packet and the symbolic one share no index  *)
(*     correspondence and the parser argument has nothing to induct on.    *)
(*     It is the read-tape analogue of [wt_unconditional].                 *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* [present_bits] algebra.                                                 *)
(* ---------------------------------------------------------------------- *)

Lemma present_bits_nil : forall f, present_bits [] f = [].
Proof. reflexivity. Qed.

(* The uniform cons equation: no case split at the call site. *)
Lemma present_bits_cons : forall b l f,
  present_bits (b :: l) f =
  (if eval_smt_bool (cvc b) f then [eval_smt_bool (cvv b) f] else [])
    ++ present_bits l f.
Proof.
  intros b l f. unfold present_bits. cbn [List.filter].
  destruct (eval_smt_bool (cvc b) f); reflexivity.
Qed.

Lemma present_bits_app : forall l1 l2 f,
  present_bits (l1 ++ l2) f = present_bits l1 f ++ present_bits l2 f.
Proof.
  intros l1 l2 f. unfold present_bits.
  rewrite List.filter_app, List.map_app. reflexivity.
Qed.

Lemma present_bits_absent : forall l f,
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) l ->
  present_bits l f = [].
Proof.
  intros l f H. induction H as [| b r Hb Hr IH]; [reflexivity |].
  rewrite present_bits_cons, Hb. exact IH.
Qed.

(* Mapping a transformation that preserves both components' denotation
   preserves the present bits.  This is what makes the [l1 = []] case of the
   merge lemmas go through, where the merged list is a [List.map]. *)
Lemma present_bits_map_ext :
  forall (g : ConditionalVal SmtBoolExpr -> ConditionalVal SmtBoolExpr) l f,
    (forall b, eval_smt_bool (cvc (g b)) f = eval_smt_bool (cvc b) f) ->
    (forall b, eval_smt_bool (cvv (g b)) f = eval_smt_bool (cvv b) f) ->
    present_bits (List.map g l) f = present_bits l f.
Proof.
  intros g l f Hc Hv. induction l as [| b r IH]; cbn [List.map]; [reflexivity |].
  rewrite !present_bits_cons, Hc, Hv, IH. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* The boolean if-then-else the merges are built from.                     *)
(* ---------------------------------------------------------------------- *)

Lemma smt_bool_ite_eval : forall c a b f,
  eval_smt_bool (smt_bool_ite c a b) f =
  if eval_smt_bool c f then eval_smt_bool a f else eval_smt_bool b f.
Proof.
  intros c a b f. unfold smt_bool_ite. cbn [eval_smt_bool].
  destruct (eval_smt_bool c f), (eval_smt_bool a f), (eval_smt_bool b f);
    reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* A merged residual's present bits are the selected branch's.             *)
(* ---------------------------------------------------------------------- *)

(* Note what this does NOT need: no hypothesis about either branch.  The
   padding [merge_bitstream] adds is absent under the selecting valuation
   wherever it lands, so [List.filter] removes it regardless of shape.  The
   presence-prefix invariant below is about a different problem -- keeping an
   INDEX correspondence with the concrete packet -- not about this. *)
Lemma merge_bitstream_present_true : forall cond l1 l2 f,
  eval_smt_bool cond f = true ->
  present_bits (merge_bitstream cond l1 l2) f = present_bits l1 f.
Proof.
  intros cond l1. induction l1 as [| c1 r1 IH]; intros l2 f Hc.
  - (* the whole merge is padding, hence absent *)
    cbn [merge_bitstream]. rewrite present_bits_nil.
    apply present_bits_absent. apply List.Forall_map.
    apply List.Forall_forall. intros x _. cbn [cvc].
    rewrite smt_bool_ite_eval, Hc. reflexivity.
  - destruct l2 as [| c2 r2]; cbn [merge_bitstream];
      rewrite !present_bits_cons; cbn [cvc cvv];
      rewrite !smt_bool_ite_eval, Hc, (IH _ _ Hc); reflexivity.
Qed.

Lemma merge_bitstream_present_false : forall cond l1 l2 f,
  eval_smt_bool cond f = false ->
  present_bits (merge_bitstream cond l1 l2) f = present_bits l2 f.
Proof.
  intros cond l1. induction l1 as [| c1 r1 IH]; intros l2 f Hc.
  - cbn [merge_bitstream]. apply present_bits_map_ext;
      intros b; cbn [cvc cvv]; rewrite smt_bool_ite_eval, Hc; reflexivity.
  - destruct l2 as [| c2 r2]; cbn [merge_bitstream];
      rewrite !present_bits_cons; cbn [cvc cvv];
      rewrite !smt_bool_ite_eval, Hc, (IH _ _ Hc); reflexivity.
Qed.

(* ====================================================================== *)
(* The presence-prefix invariant.                                         *)
(* ====================================================================== *)

(* Stated inductively rather than as "exists k, firstn k present and skipn k
   absent".  The two are equivalent ([pprefix_split] below recovers the
   split form), but every preservation proof here is an induction over a
   bitstream, and the inductive form is what those inductions can consume. *)
Inductive pprefix (f : SmtValuation) : list (ConditionalVal SmtBoolExpr) -> Prop :=
| pp_absent : forall l,
    List.Forall (fun b => eval_smt_bool (cvc b) f = false) l ->
    pprefix f l
| pp_cons : forall b l,
    eval_smt_bool (cvc b) f = true ->
    pprefix f l ->
    pprefix f (b :: l).

Lemma pprefix_nil : forall f, pprefix f [].
Proof. intros f. apply pp_absent. constructor. Qed.

Lemma pprefix_all_present : forall f l,
  List.Forall (fun b => eval_smt_bool (cvc b) f = true) l -> pprefix f l.
Proof.
  intros f l H. induction H as [| b r Hb Hr IH].
  - apply pprefix_nil.
  - apply pp_cons; assumption.
Qed.

(* The payoff.  [present_bits] is a PREFIX of the positional concretization,
   so a concrete packet and the symbolic one it came from agree index by
   index as far as the concrete one goes.  That is the correspondence the
   parser commutation proof inducts on; without it [List.filter] could
   compact around gaps and no such correspondence would exist. *)
Theorem pprefix_present_bits_is_prefix : forall f l,
  pprefix f l ->
  exists k, present_bits l f
          = List.firstn k (List.map (fun b => eval_smt_bool (cvv b) f) l).
Proof.
  intros f l H. induction H as [l Hab | b r Hb Hr [k IH]].
  - exists 0. cbn [List.firstn]. apply present_bits_absent. exact Hab.
  - exists (S k). rewrite present_bits_cons, Hb.
    cbn [List.map List.firstn]. rewrite IH. reflexivity.
Qed.

(* The split form, for when a proof wants the witness explicitly. *)
Lemma pprefix_split : forall f l,
  pprefix f l ->
  exists k,
    List.Forall (fun b => eval_smt_bool (cvc b) f = true)  (List.firstn k l) /\
    List.Forall (fun b => eval_smt_bool (cvc b) f = false) (List.skipn  k l).
Proof.
  intros f l H. induction H as [l Hab | b r Hb Hr [k [Ht Hf]]].
  - exists 0. cbn [List.firstn List.skipn]. split; [constructor | exact Hab].
  - exists (S k). cbn [List.firstn List.skipn].
    split; [apply List.Forall_cons; assumption | exact Hf].
Qed.

(* ---------------------------------------------------------------------- *)
(* Preservation.                                                           *)
(* ---------------------------------------------------------------------- *)

(* A parser hands on [List.skipn cursor packet], so the residual inherits the
   invariant from the packet. *)
Lemma pprefix_skipn : forall f n l, pprefix f l -> pprefix f (List.skipn n l).
Proof.
  intros f n l H. revert n.
  induction H as [l Hab | b r Hb Hr IH]; intros n.
  - apply pp_absent. revert l Hab. induction n as [| n IHn]; intros l Hab.
    + exact Hab.
    + destruct l as [| x xs]; cbn [List.skipn]; [constructor |].
      apply IHn. inversion Hab; assumption.
  - destruct n as [| n]; cbn [List.skipn].
    + apply pp_cons; assumption.
    + apply IH.
Qed.

(* A merge preserves it, taking the invariant from whichever branch the
   valuation selects -- the [pprefix] counterpart of
   [merge_bitstream_present_true]. *)
Lemma merge_bitstream_absent : forall cond l1 l2 f,
  eval_smt_bool cond f = true ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) l1 ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = false)
              (merge_bitstream cond l1 l2).
Proof.
  intros cond l1. induction l1 as [| c1 r1 IH]; intros l2 f Hc Hab.
  - cbn [merge_bitstream]. apply List.Forall_map.
    apply List.Forall_forall. intros x _. cbn [cvc].
    rewrite smt_bool_ite_eval, Hc. reflexivity.
  - inversion Hab as [| ? ? Hh Ht]; subst.
    destruct l2 as [| c2 r2]; cbn [merge_bitstream];
      (apply List.Forall_cons;
        [ cbn [cvc]; rewrite smt_bool_ite_eval, Hc; exact Hh
        | apply IH; assumption ]).
Qed.

(* The base case: a SOURCE parser reads the network's input packet, whose
   every position is unconditionally present.  Together with [pprefix_skipn]
   and [pprefix_merge_true] this is what will discharge the invariant along a
   whole chain -- the packet enters all-present, each parser hands on a
   [List.skipn] of what it had, and each [select] merges. *)
Lemma pprefix_symbolic_input_bits : forall f n,
  pprefix f (symbolic_input_bits n).
Proof.
  intros f n. apply pprefix_all_present.
  unfold symbolic_input_bits. apply List.Forall_map.
  apply List.Forall_forall. intros i _. reflexivity.
Qed.

Theorem pprefix_merge_true : forall f cond l1 l2,
  eval_smt_bool cond f = true ->
  pprefix f l1 ->
  pprefix f (merge_bitstream cond l1 l2).
Proof.
  intros f cond l1 l2 Hc H. revert l2.
  induction H as [l Hab | b r Hb Hr IH]; intros l2.
  - apply pp_absent. apply merge_bitstream_absent; assumption.
  - destruct l2 as [| c2 r2]; cbn [merge_bitstream];
      (apply pp_cons;
        [ cbn [cvc]; rewrite smt_bool_ite_eval, Hc; exact Hb | apply IH ]).
Qed.

(* The [cond = false] direction.  Both are needed, and not symmetrically:
   [resolve_select_symbolic] merges with the case condition in the THEN
   position and the REST of the cases in the else, so a valuation that falls
   through to the default takes the false branch once per case. *)
Lemma merge_bitstream_absent_false : forall cond l1 l2 f,
  eval_smt_bool cond f = false ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) l2 ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = false)
              (merge_bitstream cond l1 l2).
Proof.
  intros cond l1. induction l1 as [| c1 r1 IH]; intros l2 f Hc Hab.
  - cbn [merge_bitstream]. apply List.Forall_map.
    eapply List.Forall_impl; [| exact Hab]. intros a Ha. cbn [cvc].
    rewrite smt_bool_ite_eval, Hc. exact Ha.
  - destruct l2 as [| c2 r2]; cbn [merge_bitstream].
    + apply List.Forall_cons.
      * cbn [cvc]. rewrite smt_bool_ite_eval, Hc. reflexivity.
      * apply IH; [exact Hc | constructor].
    + inversion Hab as [| ? ? Hh Ht]; subst.
      apply List.Forall_cons.
      * cbn [cvc]. rewrite smt_bool_ite_eval, Hc. exact Hh.
      * apply IH; assumption.
Qed.

Lemma pprefix_map_ext : forall g l f,
  (forall b, eval_smt_bool (cvc (g b)) f = eval_smt_bool (cvc b) f) ->
  pprefix f l -> pprefix f (List.map g l).
Proof.
  intros g l f Hc H. induction H as [l Hab | b r Hb Hr IH].
  - apply pp_absent. apply List.Forall_map.
    eapply List.Forall_impl; [| exact Hab]. intros a Ha. rewrite Hc. exact Ha.
  - cbn [List.map]. apply pp_cons; [rewrite Hc; exact Hb | exact IH].
Qed.

Theorem pprefix_merge_false : forall f cond l1 l2,
  eval_smt_bool cond f = false ->
  pprefix f l2 ->
  pprefix f (merge_bitstream cond l1 l2).
Proof.
  intros f cond l1. induction l1 as [| c1 r1 IH]; intros l2 Hc H.
  - cbn [merge_bitstream]. apply pprefix_map_ext; [| exact H].
    intros b. cbn [cvc]. rewrite smt_bool_ite_eval, Hc. reflexivity.
  - destruct l2 as [| c2 r2]; cbn [merge_bitstream].
    + apply pp_absent. apply List.Forall_cons.
      * cbn [cvc]. rewrite smt_bool_ite_eval, Hc. reflexivity.
      * apply merge_bitstream_absent_false; [exact Hc | constructor].
    + inversion H; subst.
      * (* the whole of [l2] is absent, so the merge is too *)
        apply pp_absent.
        match goal with H' : List.Forall _ (_ :: _) |- _ =>
          inversion H' as [| ? ? Hh Ht]; subst end.
        apply List.Forall_cons.
        -- cbn [cvc]. rewrite smt_bool_ite_eval, Hc. exact Hh.
        -- apply merge_bitstream_absent_false; assumption.
      * apply pp_cons.
        -- cbn [cvc]. rewrite smt_bool_ite_eval, Hc. assumption.
        -- apply IH; assumption.
Qed.

(* ====================================================================== *)
(* Value-level sublemmas for the commutation proof.                       *)
(* ====================================================================== *)




(* ====================================================================== *)
(* Threading the invariant through a parser run.                          *)
(*                                                                        *)
(* Every way [run_parser_symbolic] can produce a residual is one of the    *)
(* four cases above: the empty list (all the non-accepting exits), a       *)
(* [List.skipn] of the packet (Accept), a recursive call, or a merge of    *)
(* select branches.  So the invariant survives a whole run, and the        *)
(* packet it starts from is the only thing that has to satisfy it.        *)
(* ====================================================================== *)

(* Extraction never touches the packet -- it moves the cursor and writes a
   header -- which is what lets the invariant pass through an action
   untouched. *)
Lemma apply_extract_symbolic_packet : forall po ps ps',
  apply_extract_symbolic po ps = Some ps' -> p_packet ps' = p_packet ps.
Proof.
  intros po ps ps' H. destruct po as [w | h w t]; cbn [apply_extract_symbolic] in H;
    destruct (Nat.leb (p_cursor ps + w) (List.length (p_packet ps)));
    try discriminate; inversion H; reflexivity.
Qed.

Lemma pprefix_merge_results : forall f cond r1 r2,
  pprefix f (pr_residual r1) ->
  pprefix f (pr_residual r2) ->
  pprefix f (pr_residual (merge_results cond r1 r2)).
Proof.
  intros f cond r1 r2 H1 H2. cbn [merge_results pr_residual].
  (* the valuation decides which branch the merge denotes; both directions
     of the merge preservation are used here, one per case *)
  destruct (eval_smt_bool cond f) eqn:E.
  - apply pprefix_merge_true; assumption.
  - apply pprefix_merge_false; assumption.
Qed.

Lemma pprefix_resolve_select : forall f run_tgt ps cases default,
  (forall tgt, pprefix f (pr_residual (run_tgt tgt))) ->
  pprefix f (pr_residual (resolve_select_symbolic run_tgt ps cases default)).
Proof.
  intros f run_tgt ps cases default H.
  induction cases as [| c rest IH]; cbn [resolve_select_symbolic].
  - apply H.
  - apply pprefix_merge_results; [apply H | exact IH].
Qed.

Theorem pprefix_run_parser_symbolic : forall f p fuel lbl ps guard,
  pprefix f (p_packet ps) ->
  pprefix f (pr_residual (run_parser_symbolic p lbl ps guard fuel)).
Proof.
  intros f p fuel. induction fuel as [| fuel' IH]; intros lbl ps guard Hpp.
  - cbn [run_parser_symbolic pr_residual]. apply pprefix_nil.
  - cbn [run_parser_symbolic].
    destruct (lookup_def p lbl) as [d |]; [| apply pprefix_nil].
    destruct (psd_action d) as [po |].
    + destruct (apply_extract_symbolic po ps) as [ps2 |] eqn:He;
        [| apply pprefix_nil].
      assert (Hpp2 : pprefix f (p_packet ps2)).
      { rewrite (apply_extract_symbolic_packet _ _ _ He). exact Hpp. }
      destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [pr_residual];
          [ apply IH; exact Hpp2
          | apply pprefix_skipn; exact Hpp2
          | apply pprefix_nil ].
      * destruct (select_bits_available_symbolic ps2 cases);
          [| apply pprefix_nil].
        apply pprefix_resolve_select. intros tgt.
        destruct tgt as [next | |]; cbn [pr_residual];
          [ apply IH; exact Hpp2
          | apply pprefix_skipn; exact Hpp2
          | apply pprefix_nil ].
    + destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [pr_residual];
          [ apply IH; exact Hpp
          | apply pprefix_skipn; exact Hpp
          | apply pprefix_nil ].
      * destruct (select_bits_available_symbolic ps cases);
          [| apply pprefix_nil].
        apply pprefix_resolve_select. intros tgt.
        destruct tgt as [next | |]; cbn [pr_residual];
          [ apply IH; exact Hpp
          | apply pprefix_skipn; exact Hpp
          | apply pprefix_nil ].
Qed.

Theorem pprefix_eval_parser_symbolic : forall f p ps,
  pprefix f (p_packet ps) ->
  pprefix f (pr_residual (eval_parser_symbolic p ps)).
Proof.
  intros f p ps H. unfold eval_parser_symbolic.
  apply pprefix_run_parser_symbolic. exact H.
Qed.

(* ====================================================================== *)
(* Concrete <-> symbolic parser commutation.                              *)
(*                                                                        *)
(* The concrete run takes ONE path; the symbolic run merges all of them.   *)
(* Two consequences shape everything below.                               *)
(*                                                                        *)
(* First, the two runs see packets of DIFFERENT LENGTHS.  The concrete     *)
(* one reads [present_bits (p_packet ps) f], which by [pprefix] is a       *)
(* prefix of the symbolic packet -- strictly shorter wherever a merge left *)
(* padding.  So the symbolic bounds check ([cursor + width <= n]) can      *)
(* succeed where the concrete one ([<= k], k <= n) fails.  When it does,   *)
(* the symbolic run reads padding and carries on down a path the concrete  *)
(* run does not have.  It still REJECTS, because [slice_valid] conjoins    *)
(* the presence of every consumed position into the guard and those        *)
(* positions are absent -- but its headers, residual and [pr_bits_read]    *)
(* are whatever that phantom path produced.                               *)
(*                                                                        *)
(* So the conclusion is a RELATION, not an equality: the verdicts always   *)
(* agree, the rest agrees only when the verdict is accept.  That is the    *)
(* same shape as [eval_general_program_commute] and for the same reason;   *)
(* see TODO 1.1.1.  Do not try to strengthen it.                           *)
(*                                                                        *)
(* Second, the two runs carry different FUEL, since each is sized from     *)
(* the packet it was handed.  [run_parser_concrete_fuel_mono] is what      *)
(* lets the induction pair them anyway.                                    *)
(* ====================================================================== *)

(* ---------------------------------------------------------------------- *)
(* Fuel monotonicity.                                                      *)
(*                                                                         *)
(* [run_parser_concrete] returns [None] only when the run did not COMPLETE, *)
(* so a completed run stays completed with more fuel -- the extra is simply *)
(* never looked at.  Nothing in the tree said so; [ParserTerminationLemmas] *)
(* proves fuel is ADEQUATE, which is a different statement.                *)
(* ---------------------------------------------------------------------- *)

Lemma run_parser_concrete_fuel_mono : forall n p lbl ps m r,
  run_parser_concrete p lbl ps n = Some r ->
  (n <= m)%nat ->
  run_parser_concrete p lbl ps m = Some r.
Proof.
  induction n as [| n' IH]; intros p lbl ps m r H Hle.
  - cbn in H. discriminate.
  - destruct m as [| m']; [ lia |].
    cbn [run_parser_concrete] in H |- *.
    destruct (lookup_def p lbl) as [def |]; [| discriminate].
    destruct (match psd_action def with
              | None => Some ps
              | Some po => apply_extract_concrete po ps
              end) as [ps' |]; [| exact H].
    destruct (eval_transition_concrete ps' (psd_trans def)) as [tgt |]; [| exact H].
    destruct tgt as [next | |]; [| exact H | exact H].
    apply IH; [ exact H | lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* Node-level correspondences.                                             *)
(* ---------------------------------------------------------------------- *)

(* [SmtBitsToInt] denotes the concrete [bits_to_Z] of the evaluated bits.

   The accumulator generalization has to be stated over the anonymous inner
   [fix] of [eval_smt_arith]'s [SmtBitsToInt] arm, written out literally here
   because it has no name to refer to.  It cannot be given one: the fold calls
   [eval_smt_bool] on a sublist element, so it has to sit inside the mutual
   block, and a higher-order [List.fold_left] there would not pass the guard
   checker.  If that arm is ever reworded, this [assert] is where the
   mismatch will show up. *)
Lemma eval_smt_bits_to_int : forall bits f,
  eval_smt_arith (SmtBitsToInt bits) f
  = mk_int u64 (bits_to_Z (List.map (fun b => eval_smt_bool b f) bits)).
Proof.
  intros bits f.
  assert (Hgen : forall bs acc,
    (fix go (bs0 : list SmtBoolExpr) (acc0 : Z) {struct bs0} : Z :=
       match bs0 with
       | nil => acc0
       | b :: rest =>
           go rest (Z.add (Z.mul 2 acc0)
                          (if eval_smt_bool b f then 1%Z else 0%Z))
       end) bs acc
    = List.fold_left
        (fun (a : Z) (b : bool) => Z.add (Z.mul 2 a) (if b then 1%Z else 0%Z))
        (List.map (fun b => eval_smt_bool b f) bs) acc).
  { induction bs as [| b r IH]; intros acc; [ reflexivity |].
    cbn [List.map List.fold_left]. apply IH. }
  cbn [eval_smt_arith]. f_equal. unfold bits_to_Z. apply Hgen.
Qed.

(* ---------------------------------------------------------------------- *)
(* The shape of a bitstream under [f]: a present prefix of length [k] and   *)
(* an absent tail.  Everything about the two packets' differing lengths     *)
(* goes through this one lemma.                                            *)
(* ---------------------------------------------------------------------- *)

Lemma present_bits_all_present : forall l f,
  List.Forall (fun b => eval_smt_bool (cvc b) f = true) l ->
  present_bits l f = List.map (fun b => eval_smt_bool (cvv b) f) l.
Proof.
  intros l f H. induction H as [| b r Hb Hr IH]; [ reflexivity |].
  rewrite present_bits_cons, Hb, IH. reflexivity.
Qed.

Lemma pprefix_shape : forall f l,
  pprefix f l ->
  exists k,
    (k <= List.length l)%nat /\
    present_bits l f
      = List.map (fun b => eval_smt_bool (cvv b) f) (List.firstn k l) /\
    List.Forall (fun b => eval_smt_bool (cvc b) f = true)  (List.firstn k l) /\
    List.Forall (fun b => eval_smt_bool (cvc b) f = false) (List.skipn  k l).
Proof.
  intros f l H.
  destruct (pprefix_split f l H) as [k [Ht Hf]].
  exists (Nat.min k (List.length l)).
  assert (Hfn : List.firstn (Nat.min k (List.length l)) l = List.firstn k l).
  { rewrite <- List.firstn_firstn, List.firstn_all. reflexivity. }
  assert (Hsk : List.skipn (Nat.min k (List.length l)) l = List.skipn k l).
  { destruct (Nat.le_ge_cases k (List.length l)) as [Hle | Hge].
    - rewrite Nat.min_l by exact Hle. reflexivity.
    - rewrite Nat.min_r by exact Hge.
      rewrite List.skipn_all, List.skipn_all2 by lia. reflexivity. }
  rewrite Hfn, Hsk.
  split; [ apply Nat.le_min_r |].
  split; [| split; assumption ].
  rewrite <- (List.firstn_skipn k l) at 1.
  rewrite present_bits_app, (present_bits_all_present _ _ Ht),
          (present_bits_absent _ _ Hf), List.app_nil_r.
  reflexivity.
Qed.

Lemma Forall_firstn : forall {A} (P : A -> Prop) n l,
  List.Forall P l -> List.Forall P (List.firstn n l).
Proof.
  intros A P n l H. revert n.
  induction H as [| x r Hx Hr IH]; intros n; destruct n; cbn [List.firstn];
    try constructor; auto.
Qed.

Lemma Forall_skipn : forall {A} (P : A -> Prop) n l,
  List.Forall P l -> List.Forall P (List.skipn n l).
Proof.
  intros A P n l H. revert n.
  induction H as [| x r Hx Hr IH]; intros n; destruct n; cbn [List.skipn];
    try constructor; auto.
Qed.

(* [slice_valid] is a conjunction of presence flags, so it denotes exactly
   "every position in the range is present". *)
Lemma eval_fold_and_cvc : forall (L : list (ConditionalVal SmtBoolExpr)) f,
  eval_smt_bool (List.fold_right SmtBoolAnd SmtTrue (List.map cvc L)) f
  = List.forallb (fun b => eval_smt_bool (cvc b) f) L.
Proof.
  intros L f. induction L as [| b r IH]; [ reflexivity |].
  cbn [List.map List.fold_right List.forallb eval_smt_bool]. rewrite IH.
  reflexivity.
Qed.

Lemma eval_slice_valid : forall (pkt : list (ConditionalVal SmtBoolExpr)) cur w f,
  eval_smt_bool (slice_valid pkt cur w) f
  = List.forallb (fun b => eval_smt_bool (cvc b) f)
      (List.firstn w (List.skipn cur pkt)).
Proof. intros. unfold slice_valid. apply eval_fold_and_cvc. Qed.

(* ---------------------------------------------------------------------- *)
(* A range inside the present prefix: the guard holds and the two slices    *)
(* are the same bits.                                                      *)
(* ---------------------------------------------------------------------- *)

Lemma slice_range_in_prefix :
  forall f (l : list (ConditionalVal SmtBoolExpr)) k cur w,
  List.Forall (fun b => eval_smt_bool (cvc b) f = true) (List.firstn k l) ->
  (cur + w <= k)%nat ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = true)
              (List.firstn w (List.skipn cur l)).
Proof.
  intros f l k cur w Hp Hle.
  rewrite List.firstn_skipn_comm.
  replace (List.firstn (cur + w) l)
    with (List.firstn (cur + w) (List.firstn k l))
    by (rewrite List.firstn_firstn, Nat.min_l by lia; reflexivity).
  apply Forall_skipn, Forall_firstn. exact Hp.
Qed.

Lemma present_slice_eq :
  forall f (l : list (ConditionalVal SmtBoolExpr)) k cur w,
  present_bits l f
    = List.map (fun b => eval_smt_bool (cvv b) f) (List.firstn k l) ->
  (cur + w <= k)%nat ->
  bit_slice (present_bits l f) cur w
    = List.map (fun b => eval_smt_bool (cvv b) f)
               (List.firstn w (List.skipn cur l)).
Proof.
  intros f l k cur w Hpb Hle. unfold bit_slice. rewrite Hpb.
  rewrite List.skipn_map, List.firstn_map.
  f_equal.
  rewrite List.skipn_firstn_comm, List.firstn_firstn, Nat.min_l by lia.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* A range that runs PAST the present prefix: the guard is false.           *)
(*                                                                         *)
(* This is the case that makes the two evaluators' differing bounds checks  *)
(* harmless.  The symbolic side checks against the symbolic packet's        *)
(* length and so proceeds; the range it consumed contains position [k],     *)
(* which is absent, so [slice_valid] -- and with it [pr_accept] -- is       *)
(* false.  The concrete side simply rejected.  Same verdict, different      *)
(* everything else, which is why the top-level statement is a relation.     *)
(*                                                                         *)
(* [cur <= k] is not decoration: it is the loop invariant.  While the two   *)
(* runs are in lockstep the concrete bounds check has passed at every step, *)
(* which is exactly what keeps the cursor inside the present prefix.        *)
(* Without it a zero-width op past the prefix would pass the symbolic guard *)
(* while failing the concrete check, and the verdicts would part.           *)
(* ---------------------------------------------------------------------- *)

Lemma slice_range_out_of_prefix :
  forall f (l : list (ConditionalVal SmtBoolExpr)) k cur w,
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) (List.skipn k l) ->
  (cur <= k)%nat -> (k < cur + w)%nat -> (cur + w <= List.length l)%nat ->
  List.forallb (fun b => eval_smt_bool (cvc b) f)
               (List.firstn w (List.skipn cur l)) = false.
Proof.
  intros f l k cur w Habs Hcur Hk Hlen.
  (* position [k] exists and is absent *)
  destruct (List.skipn k l) as [| x rest] eqn:Hsk.
  { exfalso. assert (List.length (List.skipn k l) = 0)%nat by (rewrite Hsk; reflexivity).
    rewrite List.length_skipn in *. lia. }
  assert (Hx : eval_smt_bool (cvc x) f = false)
    by (inversion Habs; assumption).
  (* it lies inside the consumed range *)
  assert (Hsplit : List.skipn cur l
                   = List.firstn (k - cur) (List.skipn cur l) ++ (x :: rest)).
  { assert (Hk2 : List.skipn k l = List.skipn (k - cur) (List.skipn cur l))
      by (rewrite List.skipn_skipn; f_equal; lia).
    rewrite <- Hsk, Hk2, List.firstn_skipn. reflexivity. }
  assert (HlenA : List.length (List.firstn (k - cur) (List.skipn cur l)) = (k - cur)%nat).
  { rewrite List.firstn_length_le; [ reflexivity |].
    rewrite List.length_skipn. lia. }
  assert (Hin : List.In x (List.firstn w (List.skipn cur l))).
  { rewrite Hsplit, List.firstn_app, HlenA.
    apply List.in_or_app. right.
    destruct (w - (k - cur))%nat as [| m] eqn:Hm; [ lia |].
    cbn [List.firstn]. left. reflexivity. }
  destruct (List.forallb (fun b => eval_smt_bool (cvc b) f)
                         (List.firstn w (List.skipn cur l))) eqn:Hfb;
    [| reflexivity ].
  exfalso.
  rewrite List.forallb_forall in Hfb.
  specialize (Hfb x Hin). rewrite Hx in Hfb. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* The packet shape, bundled.  [k] is how far the present prefix runs; the  *)
(* concrete packet is exactly the first [k] positions' values.              *)
(* ---------------------------------------------------------------------- *)

Definition pkt_shape (f : SmtValuation)
    (l : list (ConditionalVal SmtBoolExpr)) (k : nat) : Prop :=
  (k <= List.length l)%nat /\
  present_bits l f = List.map (fun b => eval_smt_bool (cvv b) f) (List.firstn k l) /\
  List.Forall (fun b => eval_smt_bool (cvc b) f = true)  (List.firstn k l) /\
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) (List.skipn  k l).

Lemma pprefix_pkt_shape : forall f l,
  pprefix f l -> exists k, pkt_shape f l k.
Proof.
  intros f l H. destruct (pprefix_shape f l H) as [k [H1 [H2 [H3 H4]]]].
  exists k. unfold pkt_shape. auto.
Qed.

Lemma pkt_shape_present_len : forall f l k,
  pkt_shape f l k -> List.length (present_bits l f) = k.
Proof.
  intros f l k [Hle [Hpb _]].
  rewrite Hpb, List.length_map, List.firstn_length_le by exact Hle. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* One extraction.                                                         *)
(* ---------------------------------------------------------------------- *)

(* One-node evaluation equations.  Rewriting [eval_smt_arith] a node at a
   time is necessary rather than fastidious: [cbn] reduces the whole term,
   and a [SmtBitsToInt] or [SmtArithConst] that has already been reduced no
   longer matches the lemma that characterises it.  Same trap as the block
   at the top of [MemCommuteLemmas]. *)
Lemma eval_smt_cast_node : forall from to e f,
  eval_smt_arith (SmtCast from to e) f = cast from to (eval_smt_arith e f).
Proof. reflexivity. Qed.

Lemma eval_smt_slice_node : forall lo hi e f,
  eval_smt_arith (SmtBitSlice lo hi e) f = slice_val lo hi (eval_smt_arith e f).
Proof. reflexivity. Qed.

(* The value an extract writes: the symbolic
   [SmtCast u64 of (SmtBitsToInt ...)] denotes the concrete
   [mk_int of (bits_to_Z ...)] of the same bits.  This is the equality the
   comment on [apply_extract_symbolic] asserts. *)
Lemma extract_value_commute : forall f l k cur width (of : CrIntType),
  present_bits l f = List.map (fun b => eval_smt_bool (cvv b) f) (List.firstn k l) ->
  (cur + width <= k)%nat ->
  eval_smt_arith
    (SmtCast u64 of (SmtBitsToInt
       (List.map cvv (List.firstn width (List.skipn cur l))))) f
  = mk_int of (bits_to_Z (bit_slice (present_bits l f) cur width)).
Proof.
  intros f l k cur width of Hpb Hle.
  rewrite eval_smt_cast_node, eval_smt_bits_to_int, cast_u64_mk_int.
  rewrite List.map_map, (present_slice_eq f l k cur width Hpb Hle).
  reflexivity.
Qed.

Lemma extract_in_prefix : forall f po ps k,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps + parser_op_width po <= k)%nat ->
  exists ps',
    apply_extract_symbolic po ps = Some ps' /\
    apply_extract_concrete po (eval_sym_parser_state ps f)
      = Some (eval_sym_parser_state ps' f) /\
    p_packet ps' = p_packet ps /\
    p_cursor ps' = (p_cursor ps + parser_op_width po)%nat /\
    eval_smt_bool (slice_valid (p_packet ps) (p_cursor ps) (parser_op_width po)) f
      = true.
Proof.
  intros f po ps k Hsh Hle.
  pose proof Hsh as [Hk [Hpb [Hpres Habs]]].
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  assert (Hguard : eval_smt_bool
                     (slice_valid (p_packet ps) (p_cursor ps) (parser_op_width po)) f
                   = true).
  { rewrite eval_slice_valid, List.forallb_forall.
    pose proof (slice_range_in_prefix f (p_packet ps) k (p_cursor ps)
                  (parser_op_width po) Hpres Hle) as HF.
    rewrite List.Forall_forall in HF. exact HF. }
  assert (Hsym : (p_cursor ps + parser_op_width po
                  <=? List.length (p_packet ps))%nat = true)
    by (apply Nat.leb_le; lia).
  assert (Hcon : (p_cursor ps + parser_op_width po
                  <=? List.length (present_bits (p_packet ps) f))%nat = true)
    by (apply Nat.leb_le; lia).
  destruct po as [width | h width of]; cbn [parser_op_width] in *.
  - (* SeekForward *)
    exists {| p_header_map := p_header_map ps;
              p_packet     := p_packet ps;
              p_cursor     := p_cursor ps + width |}.
    cbn [apply_extract_symbolic apply_extract_concrete eval_sym_parser_state
         p_header_map p_packet p_cursor].
    rewrite Hsym, Hcon.
    repeat split; try reflexivity; exact Hguard.
  - (* ExtractOpConstructor *)
    exists {| p_header_map :=
                PMap.set (get_key h)
                  (SmtCast u64 of (SmtBitsToInt (List.map cvv
                     (List.firstn width (List.skipn (p_cursor ps) (p_packet ps))))))
                  (p_header_map ps);
              p_packet := p_packet ps;
              p_cursor := p_cursor ps + width |}.
    cbn [apply_extract_symbolic apply_extract_concrete eval_sym_parser_state
         p_header_map p_packet p_cursor].
    rewrite Hsym, Hcon.
    repeat split; try exact Hguard.
    (* the value written differs syntactically on the two sides, so this one
       conjunct is not [reflexivity] *)
    unfold eval_sym_parser_state. cbn [p_header_map p_packet p_cursor].
    rewrite pmap_map_set,
            (extract_value_commute f (p_packet ps) k (p_cursor ps) width of Hpb Hle).
    reflexivity.
Qed.

(* An extract whose range runs past the present prefix: the concrete side
   rejects, and if the symbolic side proceeds at all its guard is false. *)
Lemma extract_out_of_prefix : forall f po ps k,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps <= k)%nat ->
  (k < p_cursor ps + parser_op_width po)%nat ->
  apply_extract_concrete po (eval_sym_parser_state ps f) = None /\
  (forall ps', apply_extract_symbolic po ps = Some ps' ->
     eval_smt_bool (slice_valid (p_packet ps) (p_cursor ps) (parser_op_width po)) f
       = false).
Proof.
  intros f po ps k Hsh Hcur Hk.
  pose proof Hsh as [Hkl [Hpb [Hpres Habs]]].
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  assert (Hcon : (p_cursor ps + parser_op_width po
                  <=? List.length (present_bits (p_packet ps) f))%nat = false)
    by (apply Nat.leb_gt; lia).
  split.
  - destruct po as [width | h width of];
      cbn [apply_extract_concrete parser_op_width eval_sym_parser_state
           p_packet p_cursor] in *;
      rewrite Hcon; reflexivity.
  - intros ps' Hsome.
    assert (Hfit : (p_cursor ps + parser_op_width po
                    <= List.length (p_packet ps))%nat).
    { destruct po as [width | h width of];
        cbn [apply_extract_symbolic parser_op_width] in *;
        destruct (p_cursor ps + width <=? List.length (p_packet ps))%nat eqn:E;
        try discriminate; apply Nat.leb_le; exact E. }
    rewrite eval_slice_valid.
    apply (slice_range_out_of_prefix f (p_packet ps) k); [ exact Habs | lia | lia | lia ].
Qed.

(* ---------------------------------------------------------------------- *)
(* Selects.                                                                *)
(* ---------------------------------------------------------------------- *)

Definition selbits_in_prefix (ps : SymbolicParserState) (k : nat) (o : SelBits) : Prop :=
  match o with
  | SelHdr _ _ _ => True
  | Peek off width => (p_cursor ps + off + width <= k)%nat
  end.

Lemma eval_select_bits_valid : forall ps cases f,
  eval_smt_bool (select_bits_valid ps cases) f
  = List.forallb
      (fun c => match sc_origin c with
                | SelHdr _ _ _ => true
                | Peek off width =>
                    List.forallb (fun b => eval_smt_bool (cvc b) f)
                      (List.firstn (off + width)
                         (List.skipn (p_cursor ps) (p_packet ps)))
                end) cases.
Proof.
  intros ps cases f. unfold select_bits_valid.
  induction cases as [| c rest IH]; [ reflexivity |].
  cbn [List.map List.fold_right List.forallb eval_smt_bool].
  rewrite IH. destruct (sc_origin c) as [h lo hi | off width];
    [ reflexivity | rewrite eval_slice_valid; reflexivity ].
Qed.

Lemma forallb_false_of : forall {A} (g : A -> bool) (l : list A) x,
  List.In x l -> g x = false -> List.forallb g l = false.
Proof.
  intros A g l x Hin Hg. induction l as [| y r IH]; [ destruct Hin |].
  cbn [List.forallb]. destruct Hin as [-> | Hin].
  - rewrite Hg. reflexivity.
  - rewrite (IH Hin), Bool.andb_false_r. reflexivity.
Qed.

Lemma forallb_false_ex : forall {A} (g : A -> bool) (l : list A),
  List.forallb g l = false -> exists x, List.In x l /\ g x = false.
Proof.
  intros A g l. induction l as [| x r IH]; cbn [List.forallb]; [ discriminate |].
  destruct (g x) eqn:Hx; cbn [andb].
  - intros H. destruct (IH H) as [y [Hy Hgy]]. exists y. split; [ right |]; assumption.
  - intros _. exists x. split; [ left; reflexivity | exact Hx ].
Qed.

Lemma select_available_concrete_in_prefix : forall f ps k cases,
  pkt_shape f (p_packet ps) k ->
  select_bits_available_concrete (eval_sym_parser_state ps f) cases = true ->
  forall c, List.In c cases -> selbits_in_prefix ps k (sc_origin c).
Proof.
  intros f ps k cases Hsh Hav c Hin.
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  unfold select_bits_available_concrete in Hav.
  rewrite List.forallb_forall in Hav. specialize (Hav c Hin).
  destruct (sc_origin c) as [h lo hi | off width]; cbn [selbits_in_prefix];
    [ exact I |].
  cbn [select_bits_concrete eval_sym_parser_state p_packet p_cursor] in Hav.
  destruct (p_cursor ps + off + width
            <=? List.length (present_bits (p_packet ps) f))%nat eqn:E;
    [| discriminate ].
  apply Nat.leb_le in E. lia.
Qed.

Lemma select_available_symbolic_of_concrete : forall f ps k cases,
  pkt_shape f (p_packet ps) k ->
  select_bits_available_concrete (eval_sym_parser_state ps f) cases = true ->
  select_bits_available_symbolic ps cases = true.
Proof.
  intros f ps k cases Hsh Hav.
  pose proof Hsh as [Hkl _].
  unfold select_bits_available_symbolic. rewrite List.forallb_forall.
  intros c Hin.
  pose proof (select_available_concrete_in_prefix f ps k cases Hsh Hav c Hin) as Hb.
  destruct (sc_origin c) as [h lo hi | off width]; cbn [select_bits_symbolic];
    [ reflexivity |].
  cbn [selbits_in_prefix] in Hb.
  replace (p_cursor ps + off + width <=? List.length (p_packet ps))%nat with true;
    [ reflexivity |].
  symmetry. apply Nat.leb_le. lia.
Qed.

Lemma select_bits_valid_true : forall f ps k cases,
  pkt_shape f (p_packet ps) k ->
  select_bits_available_concrete (eval_sym_parser_state ps f) cases = true ->
  eval_smt_bool (select_bits_valid ps cases) f = true.
Proof.
  intros f ps k cases Hsh Hav.
  pose proof Hsh as [_ [_ [Hpres _]]].
  rewrite eval_select_bits_valid, List.forallb_forall.
  intros c Hin.
  pose proof (select_available_concrete_in_prefix f ps k cases Hsh Hav c Hin) as Hb.
  destruct (sc_origin c) as [h lo hi | off width]; [ reflexivity |].
  cbn [selbits_in_prefix] in Hb.
  rewrite List.forallb_forall. intros x Hx.
  pose proof (slice_range_in_prefix f (p_packet ps) k (p_cursor ps) (off + width)
                Hpres ltac:(lia)) as HF.
  rewrite List.Forall_forall in HF. apply HF. exact Hx.
Qed.

(* The mirror image, and the reason [select_bits_valid] measures from the
   cursor: concrete unavailability has to force the symbolic guard false. *)
Lemma select_bits_valid_false : forall f ps k cases,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps <= k)%nat ->
  select_bits_available_concrete (eval_sym_parser_state ps f) cases = false ->
  select_bits_available_symbolic ps cases = true ->
  eval_smt_bool (select_bits_valid ps cases) f = false.
Proof.
  intros f ps k cases Hsh Hcur Hav Hsym.
  pose proof Hsh as [Hkl [_ [_ Habs]]].
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  unfold select_bits_available_concrete in Hav.
  destruct (forallb_false_ex _ _ Hav) as [c [Hin Hc]].
  unfold select_bits_available_symbolic in Hsym.
  rewrite List.forallb_forall in Hsym. specialize (Hsym c Hin).
  destruct (sc_origin c) as [h lo hi | off width] eqn:Ho.
  { cbn [select_bits_concrete] in Hc. discriminate. }
  (* the peeked range does not fit in the present prefix ... *)
  cbn [select_bits_concrete eval_sym_parser_state p_packet p_cursor] in Hc.
  destruct (p_cursor ps + off + width
            <=? List.length (present_bits (p_packet ps) f))%nat eqn:Ek;
    [ discriminate |].
  apply Nat.leb_gt in Ek.
  (* ... but does fit in the symbolic packet *)
  cbn [select_bits_symbolic] in Hsym.
  destruct (p_cursor ps + off + width <=? List.length (p_packet ps))%nat eqn:En;
    [| discriminate ].
  apply Nat.leb_le in En.
  rewrite eval_select_bits_valid.
  apply (forallb_false_of _ _ c Hin). rewrite Ho.
  apply (slice_range_out_of_prefix f (p_packet ps) k (p_cursor ps) (off + width)
           Habs Hcur ltac:(lia) ltac:(lia)).
Qed.

(* A case fires on the same packets on both sides. *)
Lemma select_case_cond_commute : forall f ps k c,
  pkt_shape f (p_packet ps) k ->
  selbits_in_prefix ps k (sc_origin c) ->
  eval_smt_bool (select_case_cond_symbolic ps c) f
  = select_case_matches_concrete (eval_sym_parser_state ps f) c.
Proof.
  intros f ps k c Hsh Hb.
  pose proof Hsh as [Hkl [Hpb _]].
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  unfold select_case_cond_symbolic, select_case_matches_concrete.
  destruct (sc_origin c) as [h lo hi | off width]; cbn [selbits_in_prefix] in Hb.
  - cbn [select_bits_symbolic select_bits_concrete eval_sym_parser_state
         p_header_map p_packet p_cursor eval_smt_bool].
    rewrite eval_smt_slice_node, eval_const_mask_u64, lookup_varlike_map_commute.
    destruct (CrVal.eqb _ _); reflexivity.
  - assert (Hs : (p_cursor ps + off + width <=? List.length (p_packet ps))%nat = true)
      by (apply Nat.leb_le; lia).
    assert (Hc : (p_cursor ps + off + width
                  <=? List.length (present_bits (p_packet ps) f))%nat = true)
      by (apply Nat.leb_le; lia).
    cbn [select_bits_symbolic select_bits_concrete eval_sym_parser_state
         p_header_map p_packet p_cursor].
    rewrite Hs, Hc. cbn [eval_smt_bool].
    rewrite eval_smt_bits_to_int, eval_const_mask_u64, List.map_map.
    rewrite (present_slice_eq f (p_packet ps) k (p_cursor ps + off) width Hpb
               ltac:(lia)).
    destruct (CrVal.eqb _ _); reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Merges: the merged result is the branch the valuation selects.          *)
(* ---------------------------------------------------------------------- *)

Lemma merge_header_maps_lookup : forall cond m1 m2 k,
  (merge_header_maps cond m1 m2) !! k
  = if in_dec Coqlib.peq k (pmap_keys m1 ++ pmap_keys m2)
    then SmtConditional cond (m1 !! k) (m2 !! k)
    else m1 !! k.
Proof.
  intros cond m1 m2 k. unfold merge_header_maps.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - apply (pmap_fold_set_in
             (fun k => SmtConditional cond (m1 !! k) (m2 !! k))). assumption.
  - apply (pmap_fold_set_notin
             (fun k => SmtConditional cond (m1 !! k) (m2 !! k))). assumption.
Qed.

Lemma merge_header_maps_default : forall cond m1 m2,
  fst (merge_header_maps cond m1 m2) = fst m1.
Proof. intros. unfold merge_header_maps. apply pmap_fold_set_default. Qed.

(* Per key, and the only hypothesis is that the two maps carry the same
   default -- which they do, since [PMap.set] is the only writer.  Outside
   both key sets the merge keeps [m1], and that is correct precisely because
   both sides read that shared default there. *)
Lemma merge_header_maps_commute : forall f cond m1 m2 k,
  fst m1 = fst m2 ->
  eval_smt_arith ((merge_header_maps cond m1 m2) !! k) f
  = if eval_smt_bool cond f
    then eval_smt_arith (m1 !! k) f
    else eval_smt_arith (m2 !! k) f.
Proof.
  intros f cond m1 m2 k Hd.
  rewrite merge_header_maps_lookup.
  destruct (in_dec Coqlib.peq k _) as [Hin | Hnin].
  - cbn [eval_smt_arith]. reflexivity.
  - destruct (eval_smt_bool cond f); [ reflexivity |].
    f_equal.
    rewrite (pmap_get_notin_keys m1 k), (pmap_get_notin_keys m2 k);
      [ exact Hd | | ].
    + intro; apply Hnin; apply in_or_app; right; assumption.
    + intro; apply Hnin; apply in_or_app; left; assumption.
Qed.

(* What it means for a symbolic parse result and a concrete one to agree.
   The verdict always; everything else only when the verdict is accept --
   see the header comment on this section.

   [g] is the accept condition the symbolic run was started under.  The
   concrete evaluator has no counterpart: it is simply not running on the
   paths [g] excludes.  Carrying it explicitly is what makes the induction
   go through, since [run_parser_symbolic] threads a guard and the recursive
   call sees a stronger one.  Every merge combines results that were started
   under the SAME guard, so the merge lemmas leave it alone. *)
Definition result_agree (f : SmtValuation) (g : SmtBoolExpr)
    (sr : SymParserResult) (cr : ConcParserResult) : Prop :=
  eval_smt_bool (pr_accept sr) f = (eval_smt_bool g f && pr_accept cr)%bool /\
  ((eval_smt_bool g f && pr_accept cr)%bool = true ->
     (forall k, eval_smt_arith ((pr_headers sr) !! k) f = (pr_headers cr) !! k) /\
     present_bits (pr_residual sr) f = pr_residual cr /\
     eval_smt_arith (pr_bits_read sr) f = pr_bits_read cr).

Lemma merge_results_agree : forall f g cond r1 r2 cr,
  fst (pr_headers r1) = fst (pr_headers r2) ->
  (if eval_smt_bool cond f then result_agree f g r1 cr else result_agree f g r2 cr) ->
  result_agree f g (merge_results cond r1 r2) cr.
Proof.
  intros f g cond r1 r2 cr Hd H.
  unfold result_agree, merge_results in *.
  cbn [pr_accept pr_headers pr_residual pr_bits_read].
  rewrite smt_bool_ite_eval.
  destruct (eval_smt_bool cond f) eqn:Hc;
    destruct H as [Hacc Hrest]; split; try exact Hacc; intros Hcr;
    destruct (Hrest Hcr) as [Hh [Hr Hb]]; repeat split.
  - intros k. rewrite merge_header_maps_commute by exact Hd. rewrite Hc. apply Hh.
  - rewrite merge_bitstream_present_true by exact Hc. exact Hr.
  - cbn [eval_smt_arith]. rewrite Hc. exact Hb.
  - intros k. rewrite merge_header_maps_commute by exact Hd. rewrite Hc. apply Hh.
  - rewrite merge_bitstream_present_false by exact Hc. exact Hr.
  - cbn [eval_smt_arith]. rewrite Hc. exact Hb.
Qed.

Lemma resolve_select_default : forall run_tgt ps cases default d,
  (forall tgt, fst (pr_headers (run_tgt tgt)) = d) ->
  fst (pr_headers (resolve_select_symbolic run_tgt ps cases default)) = d.
Proof.
  intros run_tgt ps cases. induction cases as [| c rest IH]; intros default d Hdf.
  - cbn [resolve_select_symbolic]. apply Hdf.
  - cbn [resolve_select_symbolic merge_results pr_headers].
    rewrite merge_header_maps_default. apply Hdf.
Qed.

(* The chain of merges denotes the target [resolve_select_concrete] picks. *)
Lemma resolve_select_agree : forall f g ps k run_tgt cases default cr d,
  pkt_shape f (p_packet ps) k ->
  (forall c, List.In c cases -> selbits_in_prefix ps k (sc_origin c)) ->
  (forall tgt, fst (pr_headers (run_tgt tgt)) = d) ->
  result_agree f g
    (run_tgt (resolve_select_concrete (eval_sym_parser_state ps f) cases default)) cr ->
  result_agree f g (resolve_select_symbolic run_tgt ps cases default) cr.
Proof.
  intros f g ps k run_tgt cases.
  induction cases as [| c rest IH]; intros default cr d Hsh Hb Hdf Hres.
  - cbn [resolve_select_symbolic resolve_select_concrete] in *. exact Hres.
  - cbn [resolve_select_symbolic] in *.
    apply (merge_results_agree f g (select_case_cond_symbolic ps c)).
    + rewrite (Hdf (sc_target c)),
              (resolve_select_default run_tgt ps rest default d Hdf).
      reflexivity.
    + rewrite (select_case_cond_commute f ps k c Hsh
                 (Hb c (or_introl eq_refl))).
      cbn [resolve_select_concrete] in Hres.
      destruct (select_case_matches_concrete (eval_sym_parser_state ps f) c);
        [ exact Hres |].
      apply (IH default cr d Hsh (fun c' Hc' => Hb c' (or_intror Hc')) Hdf).
      exact Hres.
Qed.

(* ---------------------------------------------------------------------- *)
(* Structural facts about a symbolic run.                                  *)
(* ---------------------------------------------------------------------- *)

Lemma resolve_select_accept_false : forall run_tgt ps cases default f,
  (forall tgt, eval_smt_bool (pr_accept (run_tgt tgt)) f = false) ->
  eval_smt_bool (pr_accept (resolve_select_symbolic run_tgt ps cases default)) f
    = false.
Proof.
  intros run_tgt ps cases. induction cases as [| c rest IH]; intros default f H.
  - cbn [resolve_select_symbolic]. apply H.
  - cbn [resolve_select_symbolic merge_results pr_accept].
    rewrite smt_bool_ite_eval.
    destruct (eval_smt_bool (select_case_cond_symbolic ps c) f);
      [ apply H | apply IH; exact H ].
Qed.

Lemma apply_extract_symbolic_hdr_default : forall po ps ps',
  apply_extract_symbolic po ps = Some ps' ->
  fst (p_header_map ps') = fst (p_header_map ps).
Proof.
  intros [width | h width of] ps ps' H; cbn [apply_extract_symbolic] in H;
    destruct (p_cursor ps + width <=? List.length (p_packet ps))%nat;
    try discriminate; inversion H; subst; cbn [p_header_map]; reflexivity.
Qed.

(* The header map's DEFAULT never moves: every write is a [PMap.set] and
   every merge starts from a map that already had it.  This is what
   [merge_header_maps]' correctness outside both key sets rests on. *)
Lemma run_parser_symbolic_hdr_default : forall p fuel lbl ps guard,
  fst (pr_headers (run_parser_symbolic p lbl ps guard fuel))
  = fst (p_header_map ps).
Proof.
  intros p fuel. induction fuel as [| fuel' IH]; intros lbl ps guard.
  - cbn [run_parser_symbolic pr_headers]. reflexivity.
  - cbn [run_parser_symbolic].
    destruct (lookup_def p lbl) as [d |]; [| cbn [pr_headers]; reflexivity ].
    destruct (psd_action d) as [po |].
    + destruct (apply_extract_symbolic po ps) as [ps2 |] eqn:He;
        [| cbn [pr_headers]; reflexivity ].
      pose proof (apply_extract_symbolic_hdr_default po ps ps2 He) as Hd.
      destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [run_target_symbolic pr_headers];
          [ rewrite IH | | ]; exact Hd.
      * destruct (select_bits_available_symbolic ps2 cases);
          [| cbn [pr_headers]; exact Hd ].
        rewrite (resolve_select_default _ _ _ _ (fst (p_header_map ps2)));
          [ exact Hd |].
        intros tgt. destruct tgt as [next | |]; cbn [run_target_symbolic pr_headers];
          [ apply IH | reflexivity | reflexivity ].
    + destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [run_target_symbolic pr_headers];
          [ apply IH | reflexivity | reflexivity ].
      * destruct (select_bits_available_symbolic ps cases);
          [| cbn [pr_headers]; reflexivity ].
        rewrite (resolve_select_default _ _ _ _ (fst (p_header_map ps)));
          [ reflexivity |].
        intros tgt. destruct tgt as [next | |]; cbn [run_target_symbolic pr_headers];
          [ apply IH | reflexivity | reflexivity ].
Qed.

(* A run started under a guard that is false accepts nothing: every exit is
   either [SmtFalse] or the guard itself, and the guard is only ever
   strengthened. *)
Lemma run_parser_symbolic_guard_false : forall p fuel lbl ps guard f,
  eval_smt_bool guard f = false ->
  eval_smt_bool (pr_accept (run_parser_symbolic p lbl ps guard fuel)) f = false.
Proof.
  intros p fuel. induction fuel as [| fuel' IH]; intros lbl ps guard f Hg.
  - cbn [run_parser_symbolic pr_accept]. reflexivity.
  - cbn [run_parser_symbolic].
    destruct (lookup_def p lbl) as [d |]; [| cbn [pr_accept]; reflexivity ].
    destruct (psd_action d) as [po |].
    + destruct (apply_extract_symbolic po ps) as [ps2 |];
        [| cbn [pr_accept]; reflexivity ].
      assert (Hg2 : eval_smt_bool
                      (SmtBoolAnd guard
                         (slice_valid (p_packet ps) (p_cursor ps)
                            (parser_op_width po))) f = false)
        by (cbn [eval_smt_bool]; rewrite Hg; reflexivity).
      destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [run_target_symbolic pr_accept];
          [ apply IH; exact Hg2 | exact Hg2 | reflexivity ].
      * destruct (select_bits_available_symbolic ps2 cases);
          [| cbn [pr_accept]; reflexivity ].
        apply resolve_select_accept_false. intros tgt.
        assert (Hg3 : eval_smt_bool
                        (SmtBoolAnd
                           (SmtBoolAnd guard
                              (slice_valid (p_packet ps) (p_cursor ps)
                                 (parser_op_width po)))
                           (select_bits_valid ps2 cases)) f = false)
          by (cbn [eval_smt_bool]; rewrite Hg; reflexivity).
        destruct tgt as [next | |]; cbn [run_target_symbolic pr_accept];
          [ apply IH; exact Hg3 | exact Hg3 | reflexivity ].
    + destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | |]; cbn [run_target_symbolic pr_accept];
          [ apply IH; exact Hg | exact Hg | reflexivity ].
      * destruct (select_bits_available_symbolic ps cases);
          [| cbn [pr_accept]; reflexivity ].
        apply resolve_select_accept_false. intros tgt.
        assert (Hg3 : eval_smt_bool
                        (SmtBoolAnd guard (select_bits_valid ps cases)) f = false)
          by (cbn [eval_smt_bool]; rewrite Hg; reflexivity).
        destruct tgt as [next | |]; cbn [run_target_symbolic pr_accept];
          [ apply IH; exact Hg3 | exact Hg3 | reflexivity ].
Qed.

Lemma run_target_accept_false : forall rec ps g tgt f,
  eval_smt_bool g f = false ->
  (forall next ps'' g'', eval_smt_bool g'' f = false ->
     eval_smt_bool (pr_accept (rec next ps'' g'')) f = false) ->
  eval_smt_bool (pr_accept (run_target_symbolic rec ps g tgt)) f = false.
Proof.
  intros rec ps g tgt f Hg Hrec.
  destruct tgt as [next | |]; cbn [run_target_symbolic pr_accept];
    [ apply Hrec; exact Hg | exact Hg | reflexivity ].
Qed.

Lemma present_bits_of_shape : forall f l j,
  List.Forall (fun b => eval_smt_bool (cvc b) f = true)  (List.firstn j l) ->
  List.Forall (fun b => eval_smt_bool (cvc b) f = false) (List.skipn  j l) ->
  present_bits l f = List.map (fun b => eval_smt_bool (cvv b) f) (List.firstn j l).
Proof.
  intros f l j Ht Hf.
  rewrite <- (List.firstn_skipn j l) at 1.
  rewrite present_bits_app, (present_bits_all_present _ _ Ht),
          (present_bits_absent _ _ Hf), List.app_nil_r.
  reflexivity.
Qed.

(* Handing on the unconsumed tail commutes with concretization, because
   everything the cursor has passed was present.  This is what makes an
   [Accept]'s residual line up on the two sides. *)
Lemma present_bits_skipn : forall f l k n,
  pkt_shape f l k -> (n <= k)%nat ->
  present_bits (List.skipn n l) f = List.skipn n (present_bits l f).
Proof.
  intros f l k n [Hkl [Hpb [Hpres Habs]]] Hn.
  assert (Hfs : List.firstn (k - n) (List.skipn n l)
                = List.skipn n (List.firstn k l))
    by (rewrite List.skipn_firstn_comm; reflexivity).
  rewrite (present_bits_of_shape f (List.skipn n l) (k - n)).
  - rewrite Hpb, List.skipn_map, Hfs. reflexivity.
  - rewrite Hfs. apply Forall_skipn. exact Hpres.
  - rewrite List.skipn_skipn.
    replace (k - n + n)%nat with k by lia. exact Habs.
Qed.

(* ---------------------------------------------------------------------- *)
(* The concrete step, in the same shape as the symbolic one.               *)
(* ---------------------------------------------------------------------- *)

Definition conc_target (p : Parser) (fuel : nat) (ps : ConcreteParserState)
    (tgt : ParserTarget) : option ConcParserResult :=
  match tgt with
  | Accept => Some (parser_accept_concrete ps)
  | Reject => Some (parser_reject_concrete ps)
  | TargetState next => run_parser_concrete p next ps fuel
  end.

Lemma run_parser_concrete_body : forall p fuel lbl ps def,
  lookup_def p lbl = Some def ->
  run_parser_concrete p lbl ps (S fuel)
  = match (match psd_action def with
           | None => Some ps
           | Some po => apply_extract_concrete po ps
           end) with
    | None => Some (parser_reject_concrete ps)
    | Some ps' =>
        match eval_transition_concrete ps' (psd_trans def) with
        | None => Some (parser_reject_concrete ps')
        | Some tgt => conc_target p fuel ps' tgt
        end
    end.
Proof.
  intros p fuel lbl ps def Hd. cbn [run_parser_concrete]. rewrite Hd.
  destruct (match psd_action def with
            | None => Some ps
            | Some po => apply_extract_concrete po ps
            end) as [ps' |]; [| reflexivity ].
  destruct (eval_transition_concrete ps' (psd_trans def)) as [[next | |] |];
    reflexivity.
Qed.

Lemma result_agree_guard_ext : forall f g1 g2 sr cr,
  eval_smt_bool g1 f = eval_smt_bool g2 f ->
  result_agree f g1 sr cr -> result_agree f g2 sr cr.
Proof.
  intros f g1 g2 sr cr He [H1 H2]. unfold result_agree.
  rewrite <- He. split; assumption.
Qed.

(* One transition target. *)
Lemma run_target_agree : forall p fuel f g rec ps k tgt cr,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps <= k)%nat ->
  (forall next cr',
     run_parser_concrete p next (eval_sym_parser_state ps f) fuel = Some cr' ->
     result_agree f g (rec next ps g) cr') ->
  conc_target p fuel (eval_sym_parser_state ps f) tgt = Some cr ->
  result_agree f g (run_target_symbolic rec ps g tgt) cr.
Proof.
  intros p fuel f g rec ps k tgt cr Hsh Hcur Hrec Hct.
  destruct tgt as [next | |]; cbn [run_target_symbolic conc_target] in *.
  - apply Hrec. exact Hct.
  - (* Accept *)
    inversion Hct; subst cr. clear Hct.
    unfold result_agree, parser_accept_concrete.
    cbn [pr_accept pr_headers pr_residual pr_bits_read].
    rewrite Bool.andb_true_r. split; [ reflexivity |]. intros _.
    repeat split.
    + intros k'. cbn [eval_sym_parser_state p_header_map]. symmetry. apply PMap.gmap.
    + cbn [eval_sym_parser_state p_packet p_cursor].
      apply (present_bits_skipn f (p_packet ps) k); assumption.
    + cbn [eval_sym_parser_state p_cursor]. unfold smt_bits_count.
      apply eval_const_mask_u64.
  - (* Reject *)
    inversion Hct; subst cr. clear Hct.
    unfold result_agree, parser_reject_concrete.
    cbn [pr_accept eval_smt_bool].
    rewrite Bool.andb_false_r. split; [ reflexivity |]. discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(* One transition, both flavours.  Stated as a standalone lemma taking the  *)
(* induction hypothesis as an argument, so the three ways the main          *)
(* induction can reach a transition (no action, an action inside the        *)
(* present prefix, and -- vacuously -- one past it) all discharge it the    *)
(* same way.                                                               *)
(* ---------------------------------------------------------------------- *)

Lemma trans_agree : forall p fuel f g ps k d cr,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps <= k)%nat ->
  (forall next ps'' g' cr' k',
     pkt_shape f (p_packet ps'') k' -> (p_cursor ps'' <= k')%nat ->
     run_parser_concrete p next (eval_sym_parser_state ps'' f) fuel = Some cr' ->
     result_agree f g' (run_parser_symbolic p next ps'' g' fuel) cr') ->
  match eval_transition_concrete (eval_sym_parser_state ps f) (psd_trans d) with
  | None => Some (parser_reject_concrete (eval_sym_parser_state ps f))
  | Some tgt => conc_target p fuel (eval_sym_parser_state ps f) tgt
  end = Some cr ->
  result_agree f g
    (match psd_trans d with
     | Unconditional tgt =>
         run_target_symbolic
           (fun next ps'' g'' => run_parser_symbolic p next ps'' g'' fuel) ps g tgt
     | Select cases default =>
         if select_bits_available_symbolic ps cases
         then resolve_select_symbolic
                (run_target_symbolic
                   (fun next ps'' g'' => run_parser_symbolic p next ps'' g'' fuel)
                   ps (SmtBoolAnd g (select_bits_valid ps cases)))
                ps cases default
         else mkParserResult SmtFalse (p_header_map ps) []
                (smt_bits_count (p_cursor ps))
     end) cr.
Proof.
  intros p fuel f g ps k d cr Hsh Hcur IH Hc.
  assert (Hrec : forall g' next cr',
            run_parser_concrete p next (eval_sym_parser_state ps f) fuel = Some cr' ->
            result_agree f g'
              ((fun next ps'' g'' => run_parser_symbolic p next ps'' g'' fuel)
                 next ps g') cr')
    by (intros g' next cr' H; cbn beta; eapply IH; eauto).
  destruct (psd_trans d) as [tgt | cases default].
  - cbn [eval_transition_concrete] in Hc.
    exact (run_target_agree p fuel f g _ ps k tgt cr Hsh Hcur (Hrec g) Hc).
  - cbn [eval_transition_concrete] in Hc.
    destruct (select_bits_available_concrete (eval_sym_parser_state ps f) cases)
      eqn:Eac.
    + (* both sides read the select's bits *)
      rewrite (select_available_symbolic_of_concrete f ps k cases Hsh Eac).
      (* the peeked ranges are all present, so the extra conjunct the select
         adds to the guard is true and the guard is unchanged *)
      apply (result_agree_guard_ext f
               (SmtBoolAnd g (select_bits_valid ps cases)) g).
      { cbn [eval_smt_bool].
        rewrite (select_bits_valid_true f ps k cases Hsh Eac),
                Bool.andb_true_r. reflexivity. }
      apply (resolve_select_agree f (SmtBoolAnd g (select_bits_valid ps cases))
               ps k _ cases default cr (fst (p_header_map ps)) Hsh).
      * exact (select_available_concrete_in_prefix f ps k cases Hsh Eac).
      * intros tgt. destruct tgt as [next | |];
          cbn [run_target_symbolic pr_headers];
          [ apply run_parser_symbolic_hdr_default | reflexivity | reflexivity ].
      * exact (run_target_agree p fuel f _ _ ps k _ cr Hsh Hcur (Hrec _) Hc).
    + (* the concrete run rejected: some case's peek ran off its packet *)
      inversion Hc; subst cr. clear Hc.
      unfold result_agree, parser_reject_concrete.
      cbn [pr_accept]. rewrite Bool.andb_false_r.
      split; [| discriminate ].
      destruct (select_bits_available_symbolic ps cases) eqn:Eas;
        [| cbn [pr_accept eval_smt_bool]; reflexivity ].
      (* the symbolic run took a path the concrete one does not have; its
         guard is false, so it accepts nothing *)
      assert (Hg' : eval_smt_bool (SmtBoolAnd g (select_bits_valid ps cases)) f
                    = false).
      { cbn [eval_smt_bool].
        rewrite (select_bits_valid_false f ps k cases Hsh Hcur Eac Eas),
                Bool.andb_false_r. reflexivity. }
      apply resolve_select_accept_false. intros tgt.
      apply (run_target_accept_false _ _ _ _ _ Hg').
      intros next ps'' g'' Hg''. cbn beta.
      apply run_parser_symbolic_guard_false. exact Hg''.
Qed.

Lemma eval_smt_and_node : forall a b f,
  eval_smt_bool (SmtBoolAnd a b) f = (eval_smt_bool a f && eval_smt_bool b f)%bool.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(* The parser commutes.                                                   *)
(* ====================================================================== *)

Theorem run_parser_commute : forall p fuel lbl ps guard f k cr,
  pkt_shape f (p_packet ps) k ->
  (p_cursor ps <= k)%nat ->
  run_parser_concrete p lbl (eval_sym_parser_state ps f) fuel = Some cr ->
  result_agree f guard (run_parser_symbolic p lbl ps guard fuel) cr.
Proof.
  intros p fuel. induction fuel as [| fuel' IH];
    intros lbl ps guard f k cr Hsh Hcur Hc.
  - cbn in Hc. discriminate.
  - destruct (lookup_def p lbl) as [d |] eqn:Hd;
      [| cbn [run_parser_concrete] in Hc; rewrite Hd in Hc; discriminate ].
    rewrite (run_parser_concrete_body p fuel' lbl _ d Hd) in Hc.
    cbn [run_parser_symbolic]. rewrite Hd.
    destruct (psd_action d) as [po |].
    + (* an action *)
      destruct (Nat.le_gt_cases (p_cursor ps + parser_op_width po) k)
        as [Hin | Hout].
      * (* it reads inside the present prefix: the two runs stay in step *)
        destruct (extract_in_prefix f po ps k Hsh Hin)
          as [ps2 [Hs2 [Hc2 [Hpk2 [Hcur2 Hgv]]]]].
        rewrite Hc2 in Hc. rewrite Hs2.
        apply (result_agree_guard_ext f
                 (SmtBoolAnd guard
                    (slice_valid (p_packet ps) (p_cursor ps) (parser_op_width po)))
                 guard).
        { rewrite eval_smt_and_node, Hgv, Bool.andb_true_r. reflexivity. }
        apply (trans_agree p fuel' f _ ps2 k d cr).
        -- rewrite Hpk2. exact Hsh.
        -- lia.
        -- intros next ps'' g' cr' k' H1 H2 H3. eapply IH; eassumption.
        -- exact Hc.
      * (* it reads past it: the concrete run rejects, and if the symbolic one
           carries on it does so under a guard that is false *)
        destruct (extract_out_of_prefix f po ps k Hsh Hcur Hout) as [Hcn Hgf].
        rewrite Hcn in Hc. inversion Hc; subst cr. clear Hc.
        destruct (apply_extract_symbolic po ps) as [ps2 |] eqn:Hs2.
        -- specialize (Hgf ps2 eq_refl).
           assert (Hg' : eval_smt_bool
                           (SmtBoolAnd guard
                              (slice_valid (p_packet ps) (p_cursor ps)
                                 (parser_op_width po))) f = false)
             by (rewrite eval_smt_and_node, Hgf, Bool.andb_false_r; reflexivity).
           unfold result_agree, parser_reject_concrete.
           cbn [pr_accept]. rewrite Bool.andb_false_r.
           split; [| discriminate ].
           destruct (psd_trans d) as [tgt | cases default].
           ++ apply (run_target_accept_false _ _ _ _ _ Hg').
              intros next ps'' g'' Hg''. cbn beta.
              apply run_parser_symbolic_guard_false. exact Hg''.
           ++ destruct (select_bits_available_symbolic ps2 cases);
                [| cbn [pr_accept eval_smt_bool]; reflexivity ].
              apply resolve_select_accept_false. intros tgt.
              apply run_target_accept_false;
                [ rewrite eval_smt_and_node, Hg'; reflexivity |].
              intros next ps'' g'' Hg''. cbn beta.
              apply run_parser_symbolic_guard_false. exact Hg''.
        -- unfold result_agree, parser_reject_concrete.
           cbn [pr_accept eval_smt_bool]. rewrite Bool.andb_false_r.
           split; [ reflexivity | discriminate ].
    + (* no action *)
      apply (trans_agree p fuel' f guard ps k d cr Hsh Hcur);
        [ intros next ps'' g' cr' k' H1 H2 H3; eapply IH; eassumption | exact Hc ].
Qed.

(* The entry point.  Two things are reconciled here that the induction above
   deliberately left alone.

   TOTALITY: the concrete evaluator returns an [option] and the symbolic one
   does not, so the [Some] has to come from somewhere.  It comes from
   [ParserTerminationLemmas.eval_parser_no_fuel_starvation], which is why
   [well_formed_parser] is a hypothesis -- it rules out both of
   [run_parser_concrete]'s [None] cases.  Its own [p_cursor ps = 0]
   requirement is free at every module entry, since
   [CrProgramState.set_module_packet] zeroes the cursor.

   FUEL: each evaluator sizes its fuel from the packet it was handed, and the
   concrete packet is the shorter one, so the two runs do not start with the
   same budget.  [run_parser_concrete_fuel_mono] lifts the concrete run to the
   symbolic run's fuel, which is the larger. *)
Theorem eval_parser_commute : forall p ps f,
  well_formed_parser p ->
  p_cursor ps = 0%nat ->
  pprefix f (p_packet ps) ->
  exists cr,
    eval_parser_concrete p (eval_sym_parser_state ps f) = Some cr /\
    result_agree f SmtTrue (eval_parser_symbolic p ps) cr.
Proof.
  intros p ps f Hwf Hcur0 Hpp.
  destruct (pprefix_pkt_shape f (p_packet ps) Hpp) as [k Hsh].
  pose proof (pkt_shape_present_len f (p_packet ps) k Hsh) as Hlen.
  pose proof Hsh as [Hkl _].
  (* the concrete run completes *)
  assert (Hc0 : eval_parser_concrete p (eval_sym_parser_state ps f) <> None).
  { apply eval_parser_no_fuel_starvation; [ exact Hwf |].
    cbn [eval_sym_parser_state p_cursor]. exact Hcur0. }
  destruct (eval_parser_concrete p (eval_sym_parser_state ps f)) as [cr |] eqn:Hc;
    [| exfalso; apply Hc0; reflexivity ].
  exists cr. split; [ reflexivity |].
  unfold eval_parser_concrete in Hc. unfold eval_parser_symbolic.
  cbn [eval_sym_parser_state p_packet] in Hc.
  (* lift the concrete run to the symbolic run's (larger) fuel *)
  apply (run_parser_concrete_fuel_mono _ _ _ _
           (List.length (parser_states p) * S (List.length (p_packet ps)))) in Hc;
    [| rewrite Hlen; apply Nat.mul_le_mono_l; lia ].
  apply (run_parser_commute p _ _ _ _ f k cr Hsh); [ lia | exact Hc ].
Qed.
