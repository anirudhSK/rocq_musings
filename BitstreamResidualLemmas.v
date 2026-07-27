(* 

(* ================================================================== *)
(* Gap B keystone: the residual-bitstream commutation.                  *)
(*                                                                     *)
(* The bitstream checker's symbolic side represents a parser's unconsumed *)
(* tail as a validity-annotated [SymBitstream] ([eval_parser_residual_v]), *)
(* whereas the concrete side leaves a plain [skipn cursor packet].  This   *)
(* file proves they agree: under a valuation [f] (with an all-valid input   *)
(* packet), the VALID bits of the f-concretized symbolic residual are        *)
(* exactly the concrete parser's unconsumed tail.  This is the missing        *)
(* analogue of [run_parser_commute] for the residual path — the crux of        *)
(* closing the [Admitted] bitstream lemmas.                                     *)
(* ================================================================== *)

From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrParser.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVal.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import ParserCommuteLemmas.
From MyProject Require Import Maps.

(* The concrete meaning of a symbolic residual under [f]: the list of bits at
   positions whose [valid] flag holds (padding — [valid] false — is dropped, so
   a data-dependent length is recovered as a plain concrete bit list). *)
Definition sb_concrete (sb : SymBitstream) (f : SmtValuation) : list bool :=
  List.flat_map
    (fun bv => if eval_smt_bool (snd bv) f then [eval_smt_bool (fst bv) f] else [])
    sb.

Lemma sb_concrete_nil : forall f, sb_concrete [] f = [].
Proof. reflexivity. Qed.

Lemma sb_concrete_cons : forall f b v xs,
  sb_concrete ((b, v) :: xs) f
    = (if eval_smt_bool v f then [eval_smt_bool b f] else []) ++ sb_concrete xs f.
Proof. reflexivity. Qed.

(* A [merge_bitstream] concretizes to whichever side the condition selects: the
   padded (invalid) positions on the losing side contribute nothing. *)
Lemma sb_concrete_merge : forall f cond l1 l2,
  sb_concrete (merge_bitstream cond l1 l2) f =
  if eval_smt_bool cond f then sb_concrete l1 f else sb_concrete l2 f.
Proof.
  intros f cond l1. induction l1 as [|[b1 v1] r1 IH]; intros l2.
  - cbn [merge_bitstream].
    induction l2 as [|[b2 v2] r2 IH2].
    + destruct (eval_smt_bool cond f); reflexivity.
    + cbn [map].
      rewrite (sb_concrete_cons f (smt_bool_ite cond SmtFalse b2)
                 (smt_bool_ite cond SmtFalse v2)).
      rewrite ! eval_smt_bool_ite. rewrite IH2.
      destruct (eval_smt_bool cond f) eqn:Hc; cbn [eval_smt_bool]; reflexivity.
  - cbn [merge_bitstream]. destruct l2 as [|[b2 v2] r2].
    + rewrite (sb_concrete_cons f (smt_bool_ite cond b1 SmtFalse)
                 (smt_bool_ite cond v1 SmtFalse)).
      rewrite ! eval_smt_bool_ite. rewrite (IH []).
      destruct (eval_smt_bool cond f) eqn:Hc; cbn [eval_smt_bool]; reflexivity.
    + rewrite (sb_concrete_cons f (smt_bool_ite cond b1 b2)
                 (smt_bool_ite cond v1 v2)).
      rewrite ! eval_smt_bool_ite. rewrite (IH r2).
      destruct (eval_smt_bool cond f) eqn:Hc; reflexivity.
Qed.

(* An all-valid [combine] concretizes to the plain concretized bits. *)
Lemma sb_concrete_combine_allvalid : forall f bits validity,
  length validity = length bits ->
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  sb_concrete (List.combine bits validity) f
    = List.map (fun b => eval_smt_bool b f) bits.
Proof.
  intros f. induction bits as [|b bits IH]; intros validity Hlen Hv.
  - destruct validity; [ reflexivity | discriminate ].
  - destruct validity as [|v validity]; [ discriminate |].
    cbn [combine]. cbn [sb_concrete flat_map snd fst].
    rewrite (Hv v (or_introl eq_refl)). cbn [eval_smt_bool].
    unfold sb_concrete in IH. rewrite IH.
    + reflexivity.
    + cbn [length] in Hlen. injection Hlen as ->. reflexivity.
    + intros v' Hin. apply Hv. right. exact Hin.
Qed.

(* A [skipn] tail is a sublist, so validity of the whole implies validity of it. *)
Lemma in_skipn : forall {A} n (l : list A) x, In x (List.skipn n l) -> In x l.
Proof.
  intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. right. exact H.
Qed.

(* THE KEYSTONE.  Under an all-valid input packet, the valid bits of the
   f-concretized symbolic residual are exactly the concrete parser's unconsumed
   tail.  (On a concrete reject there is nothing to relate — the accept condition
   is false, so the residual is not compared by the checker.) *)
Lemma run_parser_residual_v_commute : forall f validity fuel p lbl ps cps,
  length validity = length (p_packet ps) ->
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  run_parser_concrete p lbl (eval_sym_parser_state ps f) fuel = Some cps ->
  sb_concrete (run_parser_residual_v p lbl ps validity fuel) f
    = List.skipn (p_cursor cps) (p_packet cps).
Proof.
  intros f validity. induction fuel as [|fuel' IH]; intros p lbl ps cps Hlen Hvalid Hrun.
  - discriminate Hrun.
  - cbn [run_parser_concrete] in Hrun. cbn [run_parser_residual_v].
    destruct (lookup_state p lbl) as [d|] eqn:Hlk; [| discriminate Hrun].
    (* transition handler, shared by both extraction cases (parameterized by the
       post-extraction state [ps'] whose validity length still matches). *)
    assert (Htrans : forall ps',
      length validity = length (p_packet ps') ->
      match eval_transition_concrete (eval_sym_parser_state ps' f) (psd_trans d) with
      | Accept => Some (eval_sym_parser_state ps' f)
      | Reject => None
      | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel' end
        = Some cps ->
      sb_concrete
        (match psd_trans d with
         | Unconditional tgt =>
             match tgt with
             | TargetState next => run_parser_residual_v p next ps' validity fuel'
             | Accept => List.combine (List.skipn (p_cursor ps') (p_packet ps'))
                                      (List.skipn (p_cursor ps') validity)
             | Reject => [] end
         | Select cases default =>
             resolve_select_residual
               (fun tgt => match tgt with
                | TargetState next => run_parser_residual_v p next ps' validity fuel'
                | Accept => List.combine (List.skipn (p_cursor ps') (p_packet ps'))
                                         (List.skipn (p_cursor ps') validity)
                | Reject => [] end) ps' cases default end) f
        = List.skipn (p_cursor cps) (p_packet cps)).
    { intros ps' Hlen' Hrun'. clear Hrun.
      assert (Ptgt : forall tgt,
        match tgt with
        | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
        | Accept => Some (eval_sym_parser_state ps' f) | Reject => None end = Some cps ->
        sb_concrete (match tgt with
          | TargetState next => run_parser_residual_v p next ps' validity fuel'
          | Accept => List.combine (List.skipn (p_cursor ps') (p_packet ps'))
                                   (List.skipn (p_cursor ps') validity)
          | Reject => [] end) f = List.skipn (p_cursor cps) (p_packet cps)).
      { intros tgt Htgt. destruct tgt as [next| |].
        - apply (IH p next ps' cps Hlen' Hvalid Htgt).
        - injection Htgt as <-. cbn [p_cursor p_packet eval_sym_parser_state].
          rewrite (sb_concrete_combine_allvalid f
                     (List.skipn (p_cursor ps') (p_packet ps'))
                     (List.skipn (p_cursor ps') validity)).
          + rewrite skipn_map. reflexivity.
          + rewrite ! length_skipn. rewrite Hlen'. reflexivity.
          + intros v Hin. apply Hvalid. apply (in_skipn (p_cursor ps') validity). exact Hin.
        - discriminate Htgt. }
      revert Hrun'. destruct (psd_trans d) as [tgt | cases default]; intro Hrun'.
      - cbn [eval_transition_concrete] in Hrun'. exact (Ptgt tgt Hrun').
      - cbn [eval_transition_concrete] in Hrun'. revert Hrun'.
        induction cases as [|c rest IHcases]; intro Hrun'.
        + cbn [resolve_select_concrete] in Hrun'. cbn [resolve_select_residual].
          exact (Ptgt default Hrun').
        + cbn [resolve_select_concrete] in Hrun'. cbn [resolve_select_residual].
          rewrite sb_concrete_merge, (select_case_cond_commute ps' f c).
          destruct (select_case_matches_concrete (eval_sym_parser_state ps' f) c) eqn:Hm.
          * exact (Ptgt (sc_target c) Hrun').
          * exact (IHcases Hrun'). }
    (* discharge the extraction, reducing each case to [Htrans] *)
    revert Hrun. destruct (psd_action d) as [[h w]|] eqn:Hex; intro Hrun.
    + rewrite (apply_extract_commute (ExtractOpConstructor h w) ps f) in Hrun. revert Hrun.
      destruct (apply_extract_symbolic (ExtractOpConstructor h w) ps) as [ps'|] eqn:Hae; intro Hrun.
      2:{ cbv [option_map] in Hrun. discriminate Hrun. }
      cbv [option_map] in Hrun. apply (Htrans ps'); [| exact Hrun].
      unfold apply_extract_symbolic in Hae.
      destruct (Nat.leb (p_cursor ps + w) (length (p_packet ps))); [|discriminate].
      injection Hae as <-. exact Hlen.
    + apply (Htrans ps Hlen). exact Hrun.
Qed.

(* Specialization to the whole parser (fuels match: [eval_sym_parser_state]
   preserves packet length). *)
Lemma eval_parser_residual_v_commute : forall f validity p ps cps,
  length validity = length (p_packet ps) ->
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  eval_parser_concrete p (eval_sym_parser_state ps f) = Some cps ->
  sb_concrete (eval_parser_residual_v p ps validity) f
    = List.skipn (p_cursor cps) (p_packet cps).
Proof.
  intros f validity p ps cps Hlen Hvalid Hrun.
  unfold eval_parser_residual_v, eval_parser_concrete in *.
  replace (length (p_packet (eval_sym_parser_state ps f))) with (length (p_packet ps)) in Hrun
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  apply (run_parser_residual_v_commute f validity _ p (parser_start p) ps cps Hlen Hvalid Hrun).
Qed.

(* ------------------------------------------------------------------ *)
(* Concretization distributes over bitstream concatenation, and an
   all-valid ([SmtTrue]) run of freshly-emitted bits concretizes to just the
   concretized bits.  Together with the keystone these give the deparser output
   commutation used to close the bitstream checker. *)
Lemma sb_concrete_app : forall f l1 l2,
  sb_concrete (l1 ++ l2) f = sb_concrete l1 f ++ sb_concrete l2 f.
Proof. intros f l1 l2. unfold sb_concrete. apply flat_map_app. Qed.

Lemma sb_concrete_allvalid_map : forall f (L : list SmtBoolExpr),
  sb_concrete (List.map (fun b => (b, SmtTrue)) L) f
    = List.map (fun b => eval_smt_bool b f) L.
Proof.
  intros f. induction L as [|b L IH]; [reflexivity|].
  cbn [map]. rewrite (sb_concrete_cons f b SmtTrue). cbn [eval_smt_bool].
  rewrite IH. reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Accept commutation for the validity-aware parser.  With an all-valid input
   packet the validity guard [run_parser_symbolic_v] conjoins into the accept
   condition is vacuously true, so a concrete accept forces the symbolic accept
   to evaluate to the incoming [guard] (i.e. [true] at the top level).  This is
   the accept-side analogue of [run_parser_commute]. *)

Lemma in_firstn : forall {A} n (l : list A) x, In x (List.firstn n l) -> In x l.
Proof.
  intros A n l x H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H.
Qed.

Lemma fold_and_true : forall f L,
  (forall v, In v L -> eval_smt_bool v f = true) ->
  eval_smt_bool (List.fold_right SmtBoolAnd SmtTrue L) f = true.
Proof.
  intros f. induction L as [|x xs IH]; intros H; [reflexivity|].
  cbn [fold_right eval_smt_bool]. rewrite (H x (or_introl eq_refl)). cbn [andb].
  apply IH. intros v Hin. apply H. right. exact Hin.
Qed.

Lemma slice_valid_true : forall f validity c w,
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  eval_smt_bool (slice_valid validity c w) f = true.
Proof.
  intros f validity c w Hv. unfold slice_valid. apply fold_and_true.
  intros v Hin. apply Hv. apply (in_skipn c). apply (in_firstn w). exact Hin.
Qed.

Lemma run_parser_symbolic_v_accept : forall f validity fuel p lbl ps cps guard,
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  run_parser_concrete p lbl (eval_sym_parser_state ps f) fuel = Some cps ->
  eval_smt_bool (spr_accept (run_parser_symbolic_v p lbl ps validity guard fuel)) f
    = eval_smt_bool guard f.
Proof.
  intros f validity. induction fuel as [|fuel' IH];
    intros p lbl ps cps guard Hvalid Hrun.
  - discriminate Hrun.
  - cbn [run_parser_concrete] in Hrun. cbn [run_parser_symbolic_v].
    destruct (lookup_state p lbl) as [d|] eqn:Hlk; [| discriminate Hrun].
    assert (Htrans : forall ps' guard',
      eval_smt_bool guard' f = eval_smt_bool guard f ->
      match eval_transition_concrete (eval_sym_parser_state ps' f) (psd_trans d) with
      | Accept => Some (eval_sym_parser_state ps' f)
      | Reject => None
      | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel' end
        = Some cps ->
      eval_smt_bool (spr_accept
        (match psd_trans d with
         | Unconditional tgt =>
             match tgt with
             | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
             | Accept => mkSymParserResult guard' (p_header_map ps')
             | Reject => mkSymParserResult SmtFalse (p_header_map ps') end
         | Select cases default =>
             resolve_select_symbolic
               (fun tgt => match tgt with
                | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
                | Accept => mkSymParserResult guard' (p_header_map ps')
                | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) ps' cases default
         end)) f = eval_smt_bool guard f).
    { intros ps' guard' Hg Hrun'. clear Hrun.
      assert (Ptgt : forall tgt,
        match tgt with
        | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
        | Accept => Some (eval_sym_parser_state ps' f) | Reject => None end = Some cps ->
        eval_smt_bool (spr_accept (match tgt with
          | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
          | Accept => mkSymParserResult guard' (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end)) f
          = eval_smt_bool guard f).
      { intros tgt Htgt. destruct tgt as [next| |].
        - rewrite (IH p next ps' cps guard' Hvalid Htgt). exact Hg.
        - cbn [spr_accept]. exact Hg.
        - discriminate Htgt. }
      revert Hrun'. destruct (psd_trans d) as [tgt | cases default]; intro Hrun'.
      - cbn [eval_transition_concrete] in Hrun'. exact (Ptgt tgt Hrun').
      - cbn [eval_transition_concrete] in Hrun'. revert Hrun'.
        induction cases as [|c rest IHcases]; intro Hrun'.
        + cbn [resolve_select_concrete] in Hrun'. cbn [resolve_select_symbolic].
          exact (Ptgt default Hrun').
        + cbn [resolve_select_concrete] in Hrun'.
          cbn [resolve_select_symbolic]. unfold merge_results. cbn [spr_accept].
          rewrite eval_smt_bool_ite, (select_case_cond_commute ps' f c).
          destruct (select_case_matches_concrete (eval_sym_parser_state ps' f) c) eqn:Hm.
          * exact (Ptgt (sc_target c) Hrun').
          * exact (IHcases Hrun'). }
    revert Hrun. destruct (psd_action d) as [[h w]|] eqn:Hex; intro Hrun.
    + rewrite (apply_extract_commute (ExtractOpConstructor h w) ps f) in Hrun. revert Hrun.
      destruct (apply_extract_symbolic (ExtractOpConstructor h w) ps) as [ps'|] eqn:Hae; intro Hrun.
      2:{ cbv [option_map] in Hrun. discriminate Hrun. }
      cbv [option_map] in Hrun.
      apply (Htrans ps' (SmtBoolAnd guard (slice_valid validity (p_cursor ps) w))); [| exact Hrun].
      cbn [eval_smt_bool]. rewrite (slice_valid_true f validity (p_cursor ps) w Hvalid).
      apply Bool.andb_true_r.
    + apply (Htrans ps guard); [ reflexivity | exact Hrun ].
Qed.

Lemma eval_parser_symbolic_v_accept : forall f validity p ps cps,
  (forall v, In v validity -> eval_smt_bool v f = true) ->
  eval_parser_concrete p (eval_sym_parser_state ps f) = Some cps ->
  eval_smt_bool (spr_accept (eval_parser_symbolic_v p ps validity)) f = true.
Proof.
  intros f validity p ps cps Hvalid Hrun.
  unfold eval_parser_symbolic_v, eval_parser_concrete in *.
  replace (length (p_packet (eval_sym_parser_state ps f))) with (length (p_packet ps)) in Hrun
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  rewrite (run_parser_symbolic_v_accept f validity _ p (parser_start p) ps cps SmtTrue Hvalid Hrun).
  reflexivity.
Qed.

(* Reject-direction accept commutation: when the concrete parser rejects, the
   symbolic validity-guarded accept evaluates to false (mirror of the accept
   lemma; the guard is irrelevant — a rejected parse never accepts). *)
Lemma run_parser_symbolic_v_reject : forall f validity fuel p lbl ps guard,
  run_parser_concrete p lbl (eval_sym_parser_state ps f) fuel = None ->
  eval_smt_bool (spr_accept (run_parser_symbolic_v p lbl ps validity guard fuel)) f = false.
Proof.
  intros f validity. induction fuel as [|fuel' IH]; intros p lbl ps guard Hrun.
  - reflexivity.
  - cbn [run_parser_concrete] in Hrun. cbn [run_parser_symbolic_v].
    destruct (lookup_state p lbl) as [d|] eqn:Hlk; [| reflexivity].
    assert (Htrans : forall ps' guard',
      match eval_transition_concrete (eval_sym_parser_state ps' f) (psd_trans d) with
      | Accept => Some (eval_sym_parser_state ps' f)
      | Reject => None
      | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel' end
        = None ->
      eval_smt_bool (spr_accept
        (match psd_trans d with
         | Unconditional tgt =>
             match tgt with
             | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
             | Accept => mkSymParserResult guard' (p_header_map ps')
             | Reject => mkSymParserResult SmtFalse (p_header_map ps') end
         | Select cases default =>
             resolve_select_symbolic
               (fun tgt => match tgt with
                | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
                | Accept => mkSymParserResult guard' (p_header_map ps')
                | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) ps' cases default
         end)) f = false).
    { intros ps' guard' Hrun'. clear Hrun.
      assert (Ptgt : forall tgt,
        match tgt with
        | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
        | Accept => Some (eval_sym_parser_state ps' f) | Reject => None end = None ->
        eval_smt_bool (spr_accept (match tgt with
          | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
          | Accept => mkSymParserResult guard' (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end)) f = false).
      { intros tgt Htgt. destruct tgt as [next| |].
        - exact (IH p next ps' guard' Htgt).
        - discriminate Htgt.
        - reflexivity. }
      revert Hrun'. destruct (psd_trans d) as [tgt | cases default]; intro Hrun'.
      - cbn [eval_transition_concrete] in Hrun'. exact (Ptgt tgt Hrun').
      - cbn [eval_transition_concrete] in Hrun'. revert Hrun'.
        induction cases as [|c rest IHcases]; intro Hrun'.
        + cbn [resolve_select_concrete] in Hrun'. cbn [resolve_select_symbolic].
          exact (Ptgt default Hrun').
        + cbn [resolve_select_concrete] in Hrun'.
          cbn [resolve_select_symbolic]. unfold merge_results. cbn [spr_accept].
          rewrite eval_smt_bool_ite, (select_case_cond_commute ps' f c).
          destruct (select_case_matches_concrete (eval_sym_parser_state ps' f) c) eqn:Hm.
          * exact (Ptgt (sc_target c) Hrun').
          * exact (IHcases Hrun'). }
    revert Hrun. destruct (psd_action d) as [[h w]|] eqn:Hex; intro Hrun.
    + rewrite (apply_extract_commute (ExtractOpConstructor h w) ps f) in Hrun. revert Hrun.
      destruct (apply_extract_symbolic (ExtractOpConstructor h w) ps) as [ps'|] eqn:Hae; intro Hrun.
      2:{ reflexivity. }
      cbv [option_map] in Hrun.
      apply (Htrans ps' (SmtBoolAnd guard (slice_valid validity (p_cursor ps) w))). exact Hrun.
    + apply (Htrans ps guard). exact Hrun.
Qed.

Lemma eval_parser_symbolic_v_reject : forall f validity p ps,
  eval_parser_concrete p (eval_sym_parser_state ps f) = None ->
  eval_smt_bool (spr_accept (eval_parser_symbolic_v p ps validity)) f = false.
Proof.
  intros f validity p ps Hrun.
  unfold eval_parser_symbolic_v, eval_parser_concrete in *.
  replace (length (p_packet (eval_sym_parser_state ps f))) with (length (p_packet ps)) in Hrun
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  exact (run_parser_symbolic_v_reject f validity _ p (parser_start p) ps SmtTrue Hrun).
Qed.

(* The validity-aware parser computes the SAME header map as the plain accept-
   aware parser (the validity guard only affects [spr_accept], never the merged
   headers), so header-agreement results proved for [eval_parser_symbolic] carry
   over to [eval_parser_symbolic_v]. *)
Lemma run_parser_symbolic_v_headers : forall fuel p lbl ps validity guard,
  spr_headers (run_parser_symbolic_v p lbl ps validity guard fuel)
    = spr_headers (run_parser_symbolic p lbl ps fuel).
Proof.
  induction fuel as [|fuel' IH]; intros p lbl ps validity guard.
  - reflexivity.
  - cbn [run_parser_symbolic_v run_parser_symbolic].
    destruct (lookup_state p lbl) as [d|]; [| reflexivity].
    assert (Htgt : forall ps' guard' tgt,
      spr_headers (match tgt with
        | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
        | Accept => mkSymParserResult guard' (p_header_map ps')
        | Reject => mkSymParserResult SmtFalse (p_header_map ps') end)
      = spr_headers (match tgt with
        | TargetState next => run_parser_symbolic p next ps' fuel'
        | Accept => mkSymParserResult SmtTrue (p_header_map ps')
        | Reject => mkSymParserResult SmtFalse (p_header_map ps') end)).
    { intros ps' guard' tgt. destruct tgt as [next| |]; [ apply IH | reflexivity | reflexivity ]. }
    assert (Hres : forall ps' guard' cases default,
      spr_headers (resolve_select_symbolic
        (fun tgt => match tgt with
          | TargetState next => run_parser_symbolic_v p next ps' validity guard' fuel'
          | Accept => mkSymParserResult guard' (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) ps' cases default)
      = spr_headers (resolve_select_symbolic
        (fun tgt => match tgt with
          | TargetState next => run_parser_symbolic p next ps' fuel'
          | Accept => mkSymParserResult SmtTrue (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps') end) ps' cases default)).
    { intros ps' guard' cases. induction cases as [|c rest IHc]; intro default.
      - cbn [resolve_select_symbolic]. apply Htgt.
      - cbn [resolve_select_symbolic]. unfold merge_results. cbn [spr_headers].
        rewrite (Htgt ps' guard' (sc_target c)), IHc. reflexivity. }
    destruct (psd_action d) as [[h w]|] eqn:Hex.
    + destruct (apply_extract_symbolic (ExtractOpConstructor h w) ps) as [ps'|] eqn:Hae;
        [| reflexivity].
      destruct (psd_trans d) as [tgt | cases default]; [ apply Htgt | apply Hres ].
    + destruct (psd_trans d) as [tgt | cases default]; [ apply Htgt | apply Hres ].
Qed.

Lemma eval_parser_symbolic_v_headers : forall p ps validity,
  spr_headers (eval_parser_symbolic_v p ps validity) = spr_headers (eval_parser_symbolic p ps).
Proof. intros. apply run_parser_symbolic_v_headers. Qed. *)
