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

(* ====================================================================== *)
(* Value-level sublemmas for the commutation proof.                        *)
(* ====================================================================== *)

Transparent lookup_varlike_map.

(* --- The bit-fold denotes [bits_to_Z].  [SmtBitsToInt]'s eval uses an anonymous
   fix (a named mutual sibling is rejected by the guard checker), so we bridge it
   to a standalone accumulator fold. --- *)
Fixpoint bits_foldZ (bs : list bool) (acc : Z) : Z :=
  match bs with
  | nil => acc
  | b :: rest => bits_foldZ rest (Z.add (Z.mul 2 acc) (if b then 1%Z else 0%Z))
  end.

Lemma bits_foldZ_fold_left : forall bs acc,
  bits_foldZ bs acc =
  fold_left (fun (a : Z) (b : bool) => Z.add (Z.mul 2 a) (if b then 1%Z else 0%Z)) bs acc.
Proof. induction bs; intro acc; simpl; [ reflexivity | apply IHbs ]. Qed.

Lemma bits_foldZ_bits_to_Z : forall bs, bits_foldZ bs 0%Z = bits_to_Z bs.
Proof. intro bs. unfold bits_to_Z. apply bits_foldZ_fold_left. Qed.

Lemma eval_bits_go : forall bits f acc,
  (fix go (bs : list SmtBoolExpr) (a : Z) {struct bs} : Z :=
     match bs with
     | nil => a
     | b :: rest =>
         go rest (Z.add (Z.mul 2 a) (if eval_smt_bool b f then 1%Z else 0%Z))
     end) bits acc
  = bits_foldZ (List.map (fun b => eval_smt_bool b f) bits) acc.
Proof. induction bits; intros f acc; simpl; [ reflexivity | apply IHbits ]. Qed.

Lemma eval_bits_to_int : forall bits f,
  eval_smt_arith (SmtBitsToInt bits) f =
  mk_int u64 (bits_to_Z (List.map (fun b => eval_smt_bool b f) bits)).
Proof.
  intros bits f. cbn [eval_smt_arith].
  rewrite eval_bits_go, bits_foldZ_bits_to_Z. reflexivity.
Qed.

(* --- A header lookup on a valuation-concretized state is the [f]-evaluation of
   the symbolic lookup. --- *)
Lemma eval_sym_lookup_header : forall s f (h : Header),
  lookup_varlike_map (p_header_map (eval_sym_parser_state s f)) h =
  eval_smt_arith (lookup_varlike_map (p_header_map s) h) f.
Proof.
  intros s f h. unfold eval_sym_parser_state, lookup_varlike_map. simpl.
  rewrite PMap.gmap. reflexivity.
Qed.

(* --- A [select] case's symbolic firing condition, evaluated at [f], is the
   concrete match test on the concretized state. --- *)
Lemma select_case_cond_commute : forall s f c,
  eval_smt_bool (select_case_cond_symbolic s c) f =
  select_case_matches_concrete (eval_sym_parser_state s f) c.
Proof.
  intros s f c. unfold select_case_cond_symbolic, select_case_matches_concrete.
  cbv zeta.
  unfold mk_int at 1. cbn [eval_smt_bool].
  change (it_width u64) with W64.
  rewrite <- (eval_sym_lookup_header s f (sc_header c)).
  rewrite eval_const_mask_u64.
  destruct (CrVal.eqb
              (lookup_varlike_map (p_header_map (eval_sym_parser_state s f)) (sc_header c))
              (mk_int u64 (bits_to_Z (sc_pattern c)))); reflexivity.
Qed.

(* --- A single extraction commutes: running it concretely on the concretized
   state equals concretizing the symbolic extraction (option-wise). --- *)
Lemma apply_extract_commute : forall eo s f,
  apply_extract_concrete eo (eval_sym_parser_state s f) =
  option_map (fun s' => eval_sym_parser_state s' f) (apply_extract_symbolic eo s).
Proof.
  intros [h width] s f.
  unfold apply_extract_concrete, apply_extract_symbolic, eval_sym_parser_state.
  cbn [p_cursor p_packet p_header_map].
  rewrite length_map.
  destruct (Nat.leb (p_cursor s + width) (length (p_packet s)));
    cbn [option_map]; [ | reflexivity ].
  f_equal. cbn [p_cursor p_packet p_header_map].
  rewrite pmap_map_set. cbn beta. rewrite eval_bits_to_int.
  unfold bit_slice. rewrite skipn_map, firstn_map. reflexivity.
Qed.

(* ====================================================================== *)
(* Header-map domain monotonicity.                                         *)
(*                                                                         *)
(* [merge_header_maps] only builds a real conditional for keys in the      *)
(* [m_then] tree; for interface headers this is fine because the parser    *)
(* run only ever grows the tree domain (extraction adds keys, a merge      *)
(* keeps [m_then]'s domain), and the interface keys are all seeded by       *)
(* [init_symbolic_parser_state_n].  This section proves that monotonicity. *)
(* ====================================================================== *)

Definition in_dom (m : PMap.t SmtArithExpr) (k : positive) : Prop :=
  PTree.get k (snd m) <> None.

Definition dom_sub (m1 m2 : PMap.t SmtArithExpr) : Prop :=
  forall k, in_dom m1 k -> in_dom m2 k.

Lemma dom_sub_refl : forall m, dom_sub m m.
Proof. unfold dom_sub; auto. Qed.

(* [PMap.set] only adds a key. *)
Lemma pmap_set_dom_sub : forall k v m, dom_sub m (PMap.set k v m).
Proof.
  unfold dom_sub, in_dom, PMap.set. intros k v m i Hi. simpl.
  rewrite PTree.gsspec. destruct (Coqlib.peq i k); congruence.
Qed.

(* A merge keeps [m_then]'s domain. *)
Lemma merge_in_dom : forall cond mt me k,
  in_dom (merge_header_maps cond mt me) k <-> in_dom mt k.
Proof.
  intros cond mt me k. unfold in_dom, merge_header_maps. simpl.
  rewrite PTree.gmap. destruct (PTree.get k (snd mt)); simpl; split; congruence.
Qed.

(* Resolving a [select] keeps the domain of [ps'], given the continuation does. *)
Lemma resolve_dom : forall cases default run_tgt ps' k,
  (forall tgt, in_dom (p_header_map ps') k -> in_dom (spr_headers (run_tgt tgt)) k) ->
  in_dom (p_header_map ps') k ->
  in_dom (spr_headers (resolve_select_symbolic_acc run_tgt ps' cases default)) k.
Proof.
  destruct cases as [| c rest]; intros default run_tgt ps' k Htgt Hin; simpl.
  - apply Htgt, Hin.
  - unfold merge_results; simpl. apply merge_in_dom. apply Htgt, Hin.
Qed.

(* The parser run only grows the header-map domain. *)
Lemma run_dom_mono : forall fuel p lbl s k,
  in_dom (p_header_map s) k ->
  in_dom (spr_headers (run_parser_symbolic_acc p lbl s fuel)) k.
Proof.
  induction fuel as [| fuel' IH]; intros p lbl s k Hk.
  - simpl. cbn [spr_headers]. exact Hk.
  - simpl. destruct (lookup_state p lbl) as [d|]; [| cbn [spr_headers]; exact Hk ].
    destruct (psd_extract d) as [eo|] eqn:Hex.
    + destruct eo as [h width]. unfold apply_extract_symbolic.
      destruct (Nat.leb (p_cursor s + width) (length (p_packet s)));
        [ | cbn [spr_headers]; exact Hk ].
      destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | | ]; cbn [spr_headers p_header_map];
          [ apply IH; cbn [p_header_map]; apply pmap_set_dom_sub; exact Hk
          | apply pmap_set_dom_sub; exact Hk
          | apply pmap_set_dom_sub; exact Hk ].
      * apply resolve_dom.
        -- intros tgt Htin. destruct tgt as [next | | ]; cbn [spr_headers];
             [ apply IH; exact Htin | exact Htin | exact Htin ].
        -- cbn [p_header_map]. apply pmap_set_dom_sub. exact Hk.
    + destruct (psd_trans d) as [tgt | cases default].
      * destruct tgt as [next | | ]; cbn [spr_headers];
          [ apply IH; exact Hk | exact Hk | exact Hk ].
      * apply resolve_dom.
        -- intros tgt Htin. destruct tgt as [next | | ]; cbn [spr_headers];
             [ apply IH; exact Htin | exact Htin | exact Htin ].
        -- exact Hk.
Qed.

(* Every interface header is seeded into the initial tree domain. *)
Lemma init_dom : forall headers n h,
  In h headers ->
  in_dom (p_header_map (init_symbolic_parser_state_n headers n)) (get_key h).
Proof.
  intros headers n h Hin. unfold in_dom, init_symbolic_parser_state_n.
  cbn [snd p_header_map].
  match goal with
  | |- PTree.get (get_key h) (PTree_Properties.of_list ?l) <> None =>
      assert (Hin' : In (get_key h) (map fst l)) by
        (rewrite map_map; apply in_map_iff; exists h; split; [ reflexivity | exact Hin ]);
      apply PTree_Properties.of_list_dom in Hin';
      destruct Hin' as [v Hv]; rewrite Hv; discriminate
  end.
Qed.

(* --- Evaluating a merged map at an in-domain key collapses to the branch the
   condition selects. --- *)
Lemma merge_get : forall f cond mt me k,
  in_dom mt k ->
  eval_smt_arith (PMap.get k (merge_header_maps cond mt me)) f =
  (if eval_smt_bool cond f
   then eval_smt_arith (PMap.get k mt) f
   else eval_smt_arith (PMap.get k me) f).
Proof.
  intros f cond mt me k Hin. unfold in_dom in Hin.
  unfold merge_header_maps, PMap.get. cbn [snd fst].
  rewrite PTree.gmap.
  destruct (PTree.get k (snd mt)) as [v_then|] eqn:Ht; [ | congruence ].
  cbn [option_map eval_smt_arith]. reflexivity.
Qed.

(* --- The extraction step (over both the [None] and [Some eo] cases) links the
   concrete-on-concretized state to the concretized symbolic extraction. --- *)
Lemma extracted_commute : forall f d s,
  match psd_extract d with
  | None => Some (eval_sym_parser_state s f)
  | Some eo => apply_extract_concrete eo (eval_sym_parser_state s f)
  end =
  option_map (fun s' => eval_sym_parser_state s' f)
    (match psd_extract d with
     | None => Some s
     | Some eo => apply_extract_symbolic eo s
     end).
Proof.
  intros f d s. destruct (psd_extract d) as [eo|]; [ apply apply_extract_commute | reflexivity ].
Qed.

Lemma extracted_dom : forall d s ps' k,
  (match psd_extract d with
   | None => Some s
   | Some eo => apply_extract_symbolic eo s
   end) = Some ps' ->
  in_dom (p_header_map s) k -> in_dom (p_header_map ps') k.
Proof.
  intros d s ps' k Hext Hk. destruct (psd_extract d) as [eo|].
  - destruct eo as [h width]. unfold apply_extract_symbolic in Hext.
    destruct (Nat.leb (p_cursor s + width) (length (p_packet s)));
      [ injection Hext as <- | discriminate Hext ].
    cbn [p_header_map]. apply pmap_set_dom_sub. exact Hk.
  - injection Hext as <-. exact Hk.
Qed.

Lemma eval_smt_bool_ite : forall c a b f,
  eval_smt_bool (smt_bool_ite c a b) f =
  if eval_smt_bool c f then eval_smt_bool a f else eval_smt_bool b f.
Proof.
  intros c a b f. unfold smt_bool_ite. cbn [eval_smt_bool].
  destruct (eval_smt_bool c f), (eval_smt_bool a f), (eval_smt_bool b f); reflexivity.
Qed.

(* --- The transition step of the fuel case, factored out ([Hrec] is the fuel IH).
   Given a post-extraction state [ps'] whose tree domain covers the interface
   headers, the concrete transition on the concretization of [ps'] matches the
   symbolic one: [Ptgt] handles a single target, [Hmt] keeps interface keys in
   each target's domain, and the [select] case is an induction on the cases using
   [merge_get] and [select_case_cond_commute]. --- *)
Lemma transition_commute :
  forall f (headers : list Header) p fuel' ps' tr,
    (forall lbl s,
       (forall h, In h headers -> in_dom (p_header_map s) (get_key h)) ->
       match run_parser_concrete p lbl (eval_sym_parser_state s f) fuel' with
       | Some cps =>
           eval_smt_bool (spr_accept (run_parser_symbolic_acc p lbl s fuel')) f = true /\
           (forall h, In h headers ->
              lookup_varlike_map (p_header_map cps) h =
              eval_smt_arith (lookup_varlike_map (spr_headers (run_parser_symbolic_acc p lbl s fuel')) h) f)
       | None => eval_smt_bool (spr_accept (run_parser_symbolic_acc p lbl s fuel')) f = false
       end) ->
    (forall h, In h headers -> in_dom (p_header_map ps') (get_key h)) ->
    match match eval_transition_concrete (eval_sym_parser_state ps' f) tr with
          | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
          | Accept => Some (eval_sym_parser_state ps' f)
          | Reject => None
          end with
    | Some cps =>
        eval_smt_bool (spr_accept
          match tr with
          | Unconditional tgt =>
              match tgt with
              | TargetState next => run_parser_symbolic_acc p next ps' fuel'
              | Accept => mkSymParserResult SmtTrue (p_header_map ps')
              | Reject => mkSymParserResult SmtFalse (p_header_map ps')
              end
          | Select cases default =>
              resolve_select_symbolic_acc
                (fun t => match t with
                  | TargetState next => run_parser_symbolic_acc p next ps' fuel'
                  | Accept => mkSymParserResult SmtTrue (p_header_map ps')
                  | Reject => mkSymParserResult SmtFalse (p_header_map ps')
                  end) ps' cases default
          end) f = true /\
        (forall h, In h headers ->
           lookup_varlike_map (p_header_map cps) h =
           eval_smt_arith (lookup_varlike_map (spr_headers
             match tr with
             | Unconditional tgt =>
                 match tgt with
                 | TargetState next => run_parser_symbolic_acc p next ps' fuel'
                 | Accept => mkSymParserResult SmtTrue (p_header_map ps')
                 | Reject => mkSymParserResult SmtFalse (p_header_map ps')
                 end
             | Select cases default =>
                 resolve_select_symbolic_acc
                   (fun t => match t with
                     | TargetState next => run_parser_symbolic_acc p next ps' fuel'
                     | Accept => mkSymParserResult SmtTrue (p_header_map ps')
                     | Reject => mkSymParserResult SmtFalse (p_header_map ps')
                     end) ps' cases default
             end) h) f)
    | None =>
        eval_smt_bool (spr_accept
          match tr with
          | Unconditional tgt =>
              match tgt with
              | TargetState next => run_parser_symbolic_acc p next ps' fuel'
              | Accept => mkSymParserResult SmtTrue (p_header_map ps')
              | Reject => mkSymParserResult SmtFalse (p_header_map ps')
              end
          | Select cases default =>
              resolve_select_symbolic_acc
                (fun t => match t with
                  | TargetState next => run_parser_symbolic_acc p next ps' fuel'
                  | Accept => mkSymParserResult SmtTrue (p_header_map ps')
                  | Reject => mkSymParserResult SmtFalse (p_header_map ps')
                  end) ps' cases default
          end) f = false
    end.
Proof.
  intros f headers p fuel' ps' tr Hrec Hdom0.
  assert (Ptgt : forall tgt,
    match match tgt with
          | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
          | Accept => Some (eval_sym_parser_state ps' f)
          | Reject => None
          end with
    | Some cps =>
        eval_smt_bool (spr_accept
          match tgt with
          | TargetState next => run_parser_symbolic_acc p next ps' fuel'
          | Accept => mkSymParserResult SmtTrue (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps')
          end) f = true /\
        (forall h, In h headers ->
           lookup_varlike_map (p_header_map cps) h =
           eval_smt_arith (lookup_varlike_map (spr_headers
             match tgt with
             | TargetState next => run_parser_symbolic_acc p next ps' fuel'
             | Accept => mkSymParserResult SmtTrue (p_header_map ps')
             | Reject => mkSymParserResult SmtFalse (p_header_map ps')
             end) h) f)
    | None =>
        eval_smt_bool (spr_accept
          match tgt with
          | TargetState next => run_parser_symbolic_acc p next ps' fuel'
          | Accept => mkSymParserResult SmtTrue (p_header_map ps')
          | Reject => mkSymParserResult SmtFalse (p_header_map ps')
          end) f = false
    end).
  { intro tgt. destruct tgt as [next | | ].
    - apply Hrec; exact Hdom0.
    - cbn [spr_accept spr_headers]. split; [ reflexivity | ].
      intros h Hh. apply eval_sym_lookup_header.
    - cbn [spr_accept]. reflexivity. }
  assert (Hmt : forall tgt h, In h headers ->
    in_dom (spr_headers
      match tgt with
      | TargetState next => run_parser_symbolic_acc p next ps' fuel'
      | Accept => mkSymParserResult SmtTrue (p_header_map ps')
      | Reject => mkSymParserResult SmtFalse (p_header_map ps')
      end) (get_key h)).
  { intros tgt h Hh. destruct tgt as [next | | ].
    - apply run_dom_mono. apply Hdom0; exact Hh.
    - cbn [spr_headers]. apply Hdom0; exact Hh.
    - cbn [spr_headers]. apply Hdom0; exact Hh. }
  destruct tr as [tgt | cases default].
  - cbn [eval_transition_concrete]. exact (Ptgt tgt).
  - cbn [eval_transition_concrete]. induction cases as [| c rest IHcases].
    + cbn [resolve_select_symbolic_acc resolve_select_concrete]. exact (Ptgt default).
    + cbn [resolve_select_symbolic_acc resolve_select_concrete].
      unfold merge_results. cbn [spr_accept spr_headers].
      rewrite eval_smt_bool_ite.
      pose proof (select_case_cond_commute ps' f c) as Hcond.
      destruct (select_case_matches_concrete (eval_sym_parser_state ps' f) c) eqn:Hbm;
        rewrite Hcond; cbn beta iota.
      -- pose proof (Ptgt (sc_target c)) as Pc.
         destruct (match sc_target c with
                   | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
                   | Accept => Some (eval_sym_parser_state ps' f)
                   | Reject => None
                   end) as [cps|].
         ++ destruct Pc as [Pa Ph]. split; [ exact Pa | ].
            intros h Hh. rewrite (Ph h Hh).
            unfold lookup_varlike_map; rewrite merge_get by (apply Hmt; exact Hh);
              rewrite Hcond; reflexivity.
         ++ exact Pc.
      -- destruct (match resolve_select_concrete (eval_sym_parser_state ps' f) rest default with
                   | TargetState next => run_parser_concrete p next (eval_sym_parser_state ps' f) fuel'
                   | Accept => Some (eval_sym_parser_state ps' f)
                   | Reject => None
                   end) as [cps|].
         ++ destruct IHcases as [Ia Ih]. split; [ exact Ia | ].
            intros h Hh. rewrite (Ih h Hh).
            unfold lookup_varlike_map; rewrite merge_get by (apply Hmt; exact Hh);
              rewrite Hcond; reflexivity.
         ++ exact IHcases.
Qed.

(* --- The generalized commutation, by induction on fuel.  Given that the
   interface headers are in the start state's domain, running [p] concretely from
   [lbl] on the [f]-concretization of [s] matches the accept-aware symbolic run:
   same accept/reject, and equal interface-header values when accepting. --- *)
Lemma run_parser_commute : forall f (headers : list Header) fuel p lbl s,
  (forall h, In h headers -> in_dom (p_header_map s) (get_key h)) ->
  match run_parser_concrete p lbl (eval_sym_parser_state s f) fuel with
  | Some cps =>
      eval_smt_bool (spr_accept (run_parser_symbolic_acc p lbl s fuel)) f = true /\
      (forall h, In h headers ->
         lookup_varlike_map (p_header_map cps) h =
         eval_smt_arith (lookup_varlike_map (spr_headers (run_parser_symbolic_acc p lbl s fuel)) h) f)
  | None =>
      eval_smt_bool (spr_accept (run_parser_symbolic_acc p lbl s fuel)) f = false
  end.
Proof.
  intros f headers. induction fuel as [| fuel' IH]; intros p lbl s Hdom.
  - reflexivity.
  - simpl. destruct (lookup_state p lbl) as [d|]; [| reflexivity ].
    destruct (psd_extract d) as [eo|] eqn:Hex.
    + (* extraction: link concrete/symbolic via [apply_extract_commute] *)
      cbn [option_map]. rewrite (apply_extract_commute eo s f).
      destruct (apply_extract_symbolic eo s) as [ps'|] eqn:Hext; cbn [option_map].
      * cbn [option_map]. apply transition_commute; [ exact (IH p) | ].
        intros h Hh. eapply extracted_dom; [ rewrite Hex; exact Hext | apply Hdom; exact Hh ].
      * cbn [spr_accept]. reflexivity.
    + (* no extraction: [ps' = s] *)
      cbn [option_map]. apply transition_commute; [ exact (IH p) | exact Hdom ].
Qed.

(* --- The concrete<->symbolic parser commutation lemma: soundness/completeness
   follow from this.  It specializes [run_parser_commute] to the shared start
   state (fuels match because [eval_sym_parser_state] preserves packet length). *)
Lemma eval_parser_commute :
  forall headers packet_len p f,
    match eval_parser_concrete p
            (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f) with
    | Some cps =>
        eval_smt_bool
          (spr_accept (eval_parser_symbolic_acc p
                         (init_symbolic_parser_state_n headers packet_len))) f = true /\
        (forall h, In h headers ->
           lookup_varlike_map (p_header_map cps) h =
           eval_smt_arith
             (lookup_varlike_map
                (spr_headers (eval_parser_symbolic_acc p
                                (init_symbolic_parser_state_n headers packet_len))) h) f)
    | None =>
        eval_smt_bool
          (spr_accept (eval_parser_symbolic_acc p
                         (init_symbolic_parser_state_n headers packet_len))) f = false
    end.
Proof.
  intros headers packet_len p f.
  unfold eval_parser_concrete, eval_parser_symbolic_acc.
  replace (length (p_packet (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f)))
    with (length (p_packet (init_symbolic_parser_state_n headers packet_len)))
    by (unfold eval_sym_parser_state; cbn [p_packet]; rewrite length_map; reflexivity).
  apply (run_parser_commute f headers _ p (parser_start p)
           (init_symbolic_parser_state_n headers packet_len)).
  intros h Hh. apply init_dom. exact Hh.
Qed.
