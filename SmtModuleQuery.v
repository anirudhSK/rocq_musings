From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import SmtTypes.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtQuery.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import SmtHelperLemmas.

Definition keys_from_map {T A : Type} (fn : positive -> A) (m : PMap.t T) : list A :=
  List.map fn (List.map fst (PTree.elements (snd m))).

(* iff / implication, built from the primitive boolean connectives. *)
Definition smt_iff (a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd a b) (SmtBoolAnd (SmtBoolNot a) (SmtBoolNot b)).
Definition smt_implies (a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolNot a) b.

Fixpoint sym_out_equal (out1 out2 : list (ConditionalVal SmtBoolExpr)) : SmtBoolExpr :=
  match out1, out2 with
  | [], [] => SmtTrue
  | b1 :: _, [] => SmtBoolNot (cvc b1)   (* out1 must already be past its end *)
  | [], b2 :: _ => SmtBoolNot (cvc b2)
  | b1 :: r1, b2 :: r2 =>
      let v1 := cvc b1 in
      let v2 := cvc b2 in
      SmtBoolAnd
        (smt_iff v1 v2)                              (* same length so far *)
        (smt_implies
          (SmtBoolAnd v1 v2)                        (* only if both live... *)
          (SmtBoolAnd
            (smt_iff (cvv b1) (cvv b2))       (* ...bits agree *)
            (sym_out_equal r1 r2)))                 (* ...and recurse *)
  end.

(* Two accepting runs agree only if they consumed the same amount of the input
   packet.  This is the bitstream analogue of the memory IR's access-extent
   equivalence: a network that reads further into its input needs more of it to
   be there, so two networks that emit identical output packets but read
   different numbers of bits are not interchangeable.  Compared only where both
   sides accept -- a rejecting run has no meaningful read extent. *)
Definition check_sym_bits_read (s1 s2 : GeneralSymbolicState) : SmtBoolExpr :=
  SmtBoolEq (sh_bits_read s1) (sh_bits_read s2).

(* Two accepting runs must also leave every declared memory region holding the
   same thing.  Unlike a header, a region is an observable side effect -- it is
   how a program talks to a map or to its caller's buffer -- so it is compared,
   not treated as internal scratch.

   ONE array equality, not a cell-by-cell conjunction.  It used to be the
   latter -- [mr_len] separate [SmtArrSel] comparisons -- on the grounds that a
   memory-sorted equality in [SmtBoolExpr] would need a decidable equality on
   [Array CrVal].  It does not: [SmtArrEq] carries the bound to fold over, so
   the Coq side still says "agree cell by cell over the declared length" while
   the Z3 side emits a single extensional array equality.

   This is the difference between a checker that can look at a program which
   writes a header and one that cannot.  The old encoding was quadratic in the
   number of cells compared AND quadratic in the number of stores -- 32 cells
   against one store cost 10s, four stores cost two minutes -- because every
   [select] had to be resolved against the whole store chain independently.  See
   [memo-memo.txt] for the measurements. *)
Definition check_sym_region_equal (d : MemRegionDecl) (s1 s2 : GeneralSymbolicState)
  : SmtBoolExpr :=
  let k := unwrap (mr_id d) in
  SmtArrEq (mr_len d) ((sh_mem s1) !! k) ((sh_mem s2) !! k).

Definition check_sym_mem_equal (rs : list MemRegionDecl) (s1 s2 : GeneralSymbolicState)
  : SmtBoolExpr :=
  List.fold_right (fun d acc => SmtBoolAnd acc (check_sym_region_equal d s1 s2))
    SmtTrue rs.

(* The memory analogue of [check_sym_bits_read], and the reason loads and
   stores are total rather than rejecting: a program that reaches further into
   a region needs more of it to be there, so it can fault where the other does
   not, even when the two emit identical packets and leave identical contents
   behind.  This is the access-extent equivalence the memory IR checked with
   [CrMem.query_bounds]. *)
Definition check_sym_mem_extent (rs : list MemRegionDecl) (s1 s2 : GeneralSymbolicState)
  : SmtBoolExpr :=
  List.fold_right (fun d acc =>
    let k := unwrap (mr_id d) in
    SmtBoolAnd acc (SmtBoolEq ((sh_mem_extent s1) !! k) ((sh_mem_extent s2) !! k)))
    SmtTrue rs.

Definition check_sym_pkt_out (rs : list MemRegionDecl) (s1 s2 : GeneralSymbolicState)
  : SmtBoolExpr :=
  let v1 := cvv (gps_valid s1) in
  let v2 := cvv (gps_valid s2) in
  let eq_expr := SmtBoolOr
    (SmtBoolAnd (SmtBoolNot v1) (SmtBoolNot v2))
    (SmtBoolAnd (SmtBoolAnd v1 v2)
                (SmtBoolAnd
                  (SmtBoolAnd
                    (sym_out_equal (sh_write_tape s1) (sh_write_tape s2))
                    (check_sym_bits_read s1 s2))
                  (SmtBoolAnd
                    (check_sym_mem_equal rs s1 s2)
                    (check_sym_mem_extent rs s1 s2)))) in
  SmtBoolNot eq_expr.

Definition modnet_equivalence_checker
  (p1 : GeneralCaracaraProgram) (p2 : GeneralCaracaraProgram)
  : EquivalenceResult :=
  let len_1 := get_inp_len_from_general p1 in
  let len_2 := get_inp_len_from_general p2 in
  let mem_1 := get_mem_regions_from_general p1 in
  let mem_2 := get_mem_regions_from_general p2 in
  (* packet shape must be the same, and so must the declared memory: the two
     runs share one set of region input variables (see [init_symbolic_mem]), so
     comparing programs that disagree about which regions exist, or how long
     they are, is not meaningful. *)
  if andb (Nat.eqb len_1 len_2) (mem_region_decls_eqb mem_1 mem_2) then
    let sym1_opt := eval_general_program_symbolic p1 (init_general_symbolic_state "p1" p1) in
    let sym2_opt := eval_general_program_symbolic p2 (init_general_symbolic_state "p2" p2) in
    match sym1_opt, sym2_opt with
    | Some fs1, Some fs2 =>
      match smt_query (check_sym_pkt_out mem_1 fs1 fs2) with
      | SmtUnsat => Equivalent
      | SmtSat f => NotEquivalent f
      | SmtUnknown => NotEquivalentUnknown
      end
    | _, _ => NotEquivalentVariablesDiffer
    end
  else
    NotEquivalentVariablesDiffer.

Definition is_linear_chain (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  is_dag net /\
  single_sink net /\
  no_fan_out net /\
  no_fan_in net.

(* ================================================================== *)
(* Soundness of [modnet_equivalence_checker].                          *)
(*                                                                     *)
(* The statement is about [concretize_sym_modnet_state] applied to the  *)
(* symbolic final states -- not about running the concrete semantics -- *)
(* so this proof does not need the concrete/symbolic commutation.  What *)
(* it needs is that each conjunct of [check_sym_pkt_out], once known to *)
(* be true under every valuation, forces the corresponding equality on  *)
(* the concretized states.  The work is in three places: the write tape *)
(* (whose symbolic length is compared through presence conditions), the *)
(* per-region content conjunct (which has to know both concretized      *)
(* regions have the same declared length before an equality of loaded   *)
(* values becomes an equality of loads), and threading both invariants  *)
(* through the network recursion.                                       *)
(* ================================================================== *)

(* ---------- boolean plumbing ---------- *)

Lemma smt_iff_true : forall a b f,
  eval_smt_bool (smt_iff a b) f = true ->
  eval_smt_bool a f = eval_smt_bool b f.
Proof.
  intros a b f H. unfold smt_iff in H. cbn [eval_smt_bool] in H.
  destruct (eval_smt_bool a f), (eval_smt_bool b f); cbn in H;
    try reflexivity; discriminate.
Qed.

Lemma smt_implies_true : forall a b f,
  eval_smt_bool (smt_implies a b) f = true ->
  eval_smt_bool a f = true ->
  eval_smt_bool b f = true.
Proof.
  intros a b f H Ha. unfold smt_implies in H. cbn [eval_smt_bool] in H.
  rewrite Ha in H. cbn in H. exact H.
Qed.

(* Both memory conjuncts and [check_sym_region_equal] are right folds of
   [SmtBoolAnd acc (P x)] over a list.  Peel one element off. *)
Lemma fold_and_true : forall {A : Type} (P : A -> SmtBoolExpr) (l : list A) f,
  eval_smt_bool (List.fold_right (fun x acc => SmtBoolAnd acc (P x)) SmtTrue l) f = true ->
  List.Forall (fun x => eval_smt_bool (P x) f = true) l.
Proof.
  intros A P l f. induction l as [| x l IH]; intros H.
  - constructor.
  - cbn [List.fold_right] in H. cbn [eval_smt_bool] in H.
    apply Bool.andb_true_iff in H as [Hacc Hx].
    constructor; [exact Hx | apply IH; exact Hacc].
Qed.

(* ---------- the write tape ---------- *)

(* Every bit a deparser emits is unconditionally present ([cvc := SmtTrue] in
   [eval_deparser_symbolic]), and nothing else ever appends to the write tape.
   The property matters because [sym_out_equal] compares tapes of DIFFERENT
   lengths by asserting the surplus entries are absent, while
   [concretize_sym_modnet_state] maps over the raw list and so does not shrink
   it.  Without this invariant the length conjunct of the conclusion would be
   false, not merely unproven. *)
Definition wt_unconditional (o : list (ConditionalVal SmtBoolExpr)) : Prop :=
  List.Forall (fun b => cvc b = SmtTrue) o.

Lemma sym_out_equal_sound : forall o1 o2 f,
  wt_unconditional o1 -> wt_unconditional o2 ->
  eval_smt_bool (sym_out_equal o1 o2) f = true ->
  List.length o1 = List.length o2 /\
  List.Forall (fun '(b1, b2) => b1 = b2)
    (List.combine (List.map (fun b => eval_smt_bool (cvv b) f) o1)
                  (List.map (fun b => eval_smt_bool (cvv b) f) o2)).
Proof.
  induction o1 as [| b1 r1 IH]; intros o2 f H1 H2 H.
  - destruct o2 as [| b2 r2].
    + split; [reflexivity | constructor].
    + inversion H2 as [| ? ? Hc2 ?]; subst.
      cbn [sym_out_equal] in H. rewrite Hc2 in H. cbn in H. discriminate.
  - inversion H1 as [| ? ? Hc1 Hr1]; subst.
    destruct o2 as [| b2 r2].
    + cbn [sym_out_equal] in H. rewrite Hc1 in H. cbn in H. discriminate.
    + inversion H2 as [| ? ? Hc2 Hr2]; subst.
      cbn [sym_out_equal] in H.
      rewrite Hc1, Hc2 in H.
      cbn [eval_smt_bool smt_iff smt_implies] in H.
      apply Bool.andb_true_iff in H as [_ H].
      cbn in H.
      apply Bool.andb_true_iff in H as [Hbits Hrest].
      apply smt_iff_true in Hbits.
      specialize (IH r2 f Hr1 Hr2 Hrest) as [Hlen Hall].
      split.
      * cbn. rewrite Hlen. reflexivity.
      * cbn [List.map List.combine]. constructor; assumption.
Qed.

(* The invariant is preserved by one module step: only the deparser arm touches
   the write tape, and it appends bits it builds with [cvc := SmtTrue]. *)
Lemma module_update_gs_symbolic_wt : forall m ls gs,
  wt_unconditional (sh_write_tape gs) ->
  wt_unconditional (sh_write_tape (module_update_gs_symbolic m ls gs)).
Proof.
  intros m ls gs H.
  destruct m as [m_id p | m_id d | m_id st ct t]; destruct ls as [ts | ps | ds];
    cbn [module_update_gs_symbolic]; try exact H;
    unfold set_gps_valid, set_gps_mod_states, set_gps_shared_write_tape,
           set_gps_shared_headers, set_gps_shared_read_tape, set_gps_bits_read,
           set_gps_mem, set_gps_mem_extent;
    cbn [sh_write_tape]; try exact H.
  (* deparser: the appended bits are built with [cvc := SmtTrue] *)
  unfold wt_unconditional in *. apply List.Forall_app. split; [exact H |].
  cbn [eval_deparser_symbolic p_packet].
  apply List.Forall_map. apply List.Forall_forall. intros x _. reflexivity.
Qed.

(* The network recursion folds over downstream modules with an option
   accumulator; this is the shape of that fold, once, generically. *)
Lemma fold_left_opt_inv :
  forall (Inv : GeneralSymbolicState -> Prop)
         (step : GeneralSymbolicState -> ModuleName -> option GeneralSymbolicState)
         (dsts : list ModuleName) (acc : option GeneralSymbolicState) res,
  (forall gs d gs', Inv gs -> step gs d = Some gs' -> Inv gs') ->
  (match acc with Some g => Inv g | None => True end) ->
  List.fold_left
    (fun a d => match a with None => None | Some g => step g d end) dsts acc
    = Some res ->
  Inv res.
Proof.
  intros Inv step dsts. induction dsts as [| d dsts IH]; intros acc res Hstep Hacc H.
  - cbn in H. destruct acc as [g |]; [inversion H; subst; exact Hacc | discriminate].
  - cbn in H. destruct acc as [g |].
    + destruct (step g d) as [g' |] eqn:Hs.
      * apply (IH (Some g') res Hstep); [eapply Hstep; eauto | exact H].
      * apply (IH None res Hstep); [exact I | exact H].
    + apply (IH None res Hstep); [exact I | exact H].
Qed.

Lemma eval_network_from_symbolic_wt :
  forall fuel net start f_hdrs f_bits gs gs',
  wt_unconditional (sh_write_tape gs) ->
  eval_network_from_symbolic net start f_hdrs f_bits gs fuel = Some gs' ->
  wt_unconditional (sh_write_tape gs').
Proof.
  induction fuel as [| fuel IH]; intros net start f_hdrs f_bits gs gs' Hgs H.
  - cbn in H. discriminate.
  - cbn [eval_network_from_symbolic] in H.
    destruct (lookup_module net start) as [m |] eqn:Hm; [| discriminate].
    destruct ((mod_states gs) ?? (unwrap start)) as [ls |] eqn:Hls; [| discriminate].
    apply (fold_left_opt_inv
             (fun g => wt_unconditional (sh_write_tape g))
             (fun g d => eval_network_from_symbolic net d
                           (sh_hdr_map (module_update_gs_symbolic m
                              (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
                           (sh_read_tape (module_update_gs_symbolic m
                              (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
                           g fuel)
             (downstream_modules net start)
             (Some (module_update_gs_symbolic m
                      (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
             gs').
    + intros g d g' Hg Hstep. eapply IH; eauto.
    + cbn. apply module_update_gs_symbolic_wt. exact Hgs.
    + exact H.
Qed.

Lemma eval_general_program_symbolic_wt : forall p pre s,
  eval_general_program_symbolic p (init_general_symbolic_state pre p) = Some s ->
  wt_unconditional (sh_write_tape s).
Proof.
  intros p pre s H.
  unfold eval_general_program_symbolic in H.
  destruct ((mod_states (init_general_symbolic_state pre p))
              ?? (unwrap (start_module (get_network_from_general p)))) eqn:Hst;
    [| discriminate].
  eapply eval_network_from_symbolic_wt; [| exact H].
  cbn [init_general_symbolic_state sh_write_tape]. constructor.
Qed.

(* ---------- memory: every region stays rooted at its initial expression ----- *)

(* The content conjunct compares LOADED VALUES, and turning that into an
   equality of LOADS needs to know the two concretized regions are both
   allocated with the same length (or both unallocated) -- otherwise one side
   could be [Legal ErrorVal] against the other's [Illegal], which agree on the
   value and differ as [Check_T]s.

   Rather than track lengths, track provenance: every leaf of a region's
   expression is still the expression the state started with at that key.  A
   store wraps in [SmtArrSt] and a merge in [SmtArrIte]; neither invents a
   leaf, and neither changes the length ([st_arr] preserves [arr_len] and
   returns the region untouched when it refuses).  Because the checker has
   already established the two programs declare the same regions, their
   initial maps are equal, so a shared root gives both sides the same shape. *)
Fixpoint arr_rooted (root : SmtArrExpr) (a : SmtArrExpr) : Prop :=
  match a with
  | SmtArrSt a' _ _ => arr_rooted root a'
  | SmtArrIte _ a1 a2 => arr_rooted root a1 /\ arr_rooted root a2
  | _ => a = root
  end.

Definition arr_leaf (a : SmtArrExpr) : Prop :=
  match a with
  | SmtArrSt _ _ _ | SmtArrIte _ _ _ => False
  | _ => True
  end.

Lemma arr_rooted_refl : forall a, arr_leaf a -> arr_rooted a a.
Proof. intros a H; destruct a; cbn in *; try contradiction; reflexivity. Qed.

(* The payoff: a rooted expression denotes an array of the root's shape. *)
Lemma eval_smt_mem_rooted : forall root a f,
  arr_rooted root a ->
  match eval_smt_mem root f with
  | Unallocated => eval_smt_mem a f = Unallocated
  | Allocated b0 => exists blk, eval_smt_mem a f = Allocated blk /\ arr_len blk = arr_len b0
  end.
Proof.
  intros root a f. revert a.
  induction a as [| nm len | a' IHa idx val | c a1 IH1 a2 IH2]; intros Hr.
  - (* SmtArrInit *) cbn in Hr; subst root. cbn. reflexivity.
  - (* SmtArrVar *) cbn in Hr; subst root.
    cbn [eval_smt_mem]. unfold region_with_len.
    exists {| arr_len := len; arr_bytes := region_bytes (sv_arrs f nm) |}.
    split; reflexivity.
  - (* SmtArrSt *) cbn in Hr. specialize (IHa Hr).
    destruct (eval_smt_mem root f) as [b0 |] eqn:Hroot.
    + destruct IHa as [blk [Hev Hlen]].
      cbn [eval_smt_mem]. rewrite Hev.
      unfold st_arr.
      destruct (eval_smt_arith idx f) as [i ti | |] eqn:Hi;
        try (exists blk; split; [reflexivity | exact Hlen]).
      destruct (Integers.ltu i (arr_len blk)) eqn:Hlt.
      * eexists. split; [reflexivity | cbn; exact Hlen].
      * exists blk; split; [reflexivity | exact Hlen].
    + cbn [eval_smt_mem]. rewrite IHa. cbn. reflexivity.
  - (* SmtArrIte *) cbn in Hr. destruct Hr as [Hr1 Hr2].
    specialize (IH1 Hr1). specialize (IH2 Hr2).
    destruct (eval_smt_mem root f) as [b0 |] eqn:Hroot;
      cbn [eval_smt_mem]; destruct (eval_smt_bool c f); assumption.
Qed.

(* Only the sets at key [k] can change what is stored at [k], and they all
   store [g k]. *)
Lemma fold_set_preserves_at :
  forall {T : Type} (P : T -> Prop) (g : positive -> T) ks (m : PMap.t T) k,
  P (m !! k) -> P (g k) ->
  P ((List.fold_left (fun acc k' => PMap.set k' (g k') acc) ks m) !! k).
Proof.
  intros T P g ks. induction ks as [| k' ks IH]; intros m k Hm Hg.
  - cbn. exact Hm.
  - cbn. apply IH; [| exact Hg].
    rewrite PMap.gsspec. destruct (Coqlib.peq k k'); [subst; exact Hg | exact Hm].
Qed.

(* The per-key invariant, lifted to a whole memory map. *)
Definition mem_rooted (m0 m : PMap.t SmtArrExpr) : Prop :=
  forall k, arr_rooted (m0 !! k) (m !! k).

Lemma switch_case_arr_rooted : forall root conds l dflt,
  List.Forall (fun a => arr_rooted root a) l ->
  arr_rooted root dflt ->
  arr_rooted root (switch_case_arr (List.combine conds l) dflt).
Proof.
  intros root conds. revert conds.
  induction conds as [| c conds IH]; intros l dflt Hl Hd.
  - cbn. exact Hd.
  - destruct l as [| a l]; cbn; [exact Hd |].
    inversion Hl as [| ? ? Ha Hl']; subst.
    split; [exact Ha | apply IH; assumption].
Qed.

Lemma eval_hdr_op_assign_smt_mem_rooted : forall m0 op mc ps,
  mem_rooted m0 (mc_mem mc) ->
  mem_rooted m0 (mc_mem (fst (eval_hdr_op_assign_smt_mem op mc ps))).
Proof.
  intros m0 op mc ps H.
  destruct op; cbn [eval_hdr_op_assign_smt_mem fst];
    unfold bump_extent_smt, set_mc_extent, set_mc_mem; cbn [mc_mem]; try exact H.
  (* StoreOp: the region is wrapped in SmtArrSt, which keeps its leaves *)
  intro k. rewrite PMap.gsspec.
  destruct (Coqlib.peq k (unwrap region)); [subst; cbn; apply H | apply H].
Qed.

Lemma eval_hdr_op_list_smt_mem_rooted : forall m0 hol mc ps,
  mem_rooted m0 (mc_mem mc) ->
  mem_rooted m0 (mc_mem (fst (eval_hdr_op_list_smt_mem hol mc ps))).
Proof.
  intros m0 hol. induction hol as [| op hol IH]; intros mc ps H.
  - cbn. exact H.
  - unfold eval_hdr_op_list_smt_mem. cbn [List.fold_left].
    destruct (eval_hdr_op_assign_smt_mem op mc ps) as [mc' ps'] eqn:Hstep.
    apply IH.
    replace mc' with (fst (eval_hdr_op_assign_smt_mem op mc ps)) by (rewrite Hstep; reflexivity).
    apply eval_hdr_op_assign_smt_mem_rooted. exact H.
Qed.

Lemma merge_mem_ctx_smt_rooted : forall m0 c mc1 mc2,
  mem_rooted m0 (mc_mem mc1) -> mem_rooted m0 (mc_mem mc2) ->
  mem_rooted m0 (mc_mem (merge_mem_ctx_smt c mc1 mc2)).
Proof.
  intros m0 c mc1 mc2 H1 H2 k.
  unfold merge_mem_ctx_smt. cbn [mc_mem].
  apply fold_set_preserves_at; [apply H2 | cbn; split; [apply H1 | apply H2]].
Qed.

Lemma eval_match_action_rule_smt_mem_rooted : forall m0 rule mc ps,
  mem_rooted m0 (mc_mem mc) ->
  mem_rooted m0 (mc_mem (fst (eval_match_action_rule_smt_mem rule mc ps))).
Proof.
  intros m0 rule mc ps H.
  destruct rule as [[mp act] | [mp act]]; cbn [eval_match_action_rule_smt_mem
    eval_seq_rule_smt_mem eval_par_rule_smt_mem fst];
    apply merge_mem_ctx_smt_rooted; try exact H;
    apply eval_hdr_op_list_smt_mem_rooted; exact H.
Qed.

Lemma eval_transformer_smt_mem_rooted : forall m0 t mc ps,
  mem_rooted m0 (mc_mem mc) ->
  mem_rooted m0 (mc_mem (fst (eval_transformer_smt_mem t mc ps))).
Proof.
  intros m0 t mc ps H k.
  unfold eval_transformer_smt_mem. cbn [fst mc_mem].
  apply fold_set_preserves_at; [apply H |].
  apply switch_case_arr_rooted; [| apply H].
  rewrite List.map_map, List.map_map.
  apply List.Forall_map. apply List.Forall_forall. intros rule _.
  apply (eval_match_action_rule_smt_mem_rooted m0 rule mc ps H).
Qed.

Lemma module_update_gs_symbolic_mem_rooted : forall m0 m ls gs,
  mem_rooted m0 (sh_mem gs) ->
  mem_rooted m0 (sh_mem (module_update_gs_symbolic m ls gs)).
Proof.
  intros m0 m ls gs H.
  destruct m as [m_id p | m_id d | m_id st ct t]; destruct ls as [ts | ps | ds];
    cbn [module_update_gs_symbolic];
    unfold set_gps_valid, set_gps_mod_states, set_gps_shared_write_tape,
           set_gps_shared_headers, set_gps_shared_read_tape, set_gps_bits_read,
           set_gps_mem, set_gps_mem_extent;
    cbn [sh_mem]; try exact H.
  (* transformer: the memory context is threaded through and copied back *)
  apply (eval_transformer_smt_mem_rooted m0 t
           {| mc_mem := sh_mem gs; mc_extent := sh_mem_extent gs |} ts).
  cbn [mc_mem]. exact H.
Qed.

Lemma eval_network_from_symbolic_mem_rooted :
  forall m0 fuel net start f_hdrs f_bits gs gs',
  mem_rooted m0 (sh_mem gs) ->
  eval_network_from_symbolic net start f_hdrs f_bits gs fuel = Some gs' ->
  mem_rooted m0 (sh_mem gs').
Proof.
  intros m0 fuel. induction fuel as [| fuel IH];
    intros net start f_hdrs f_bits gs gs' Hgs H.
  - cbn in H. discriminate.
  - cbn [eval_network_from_symbolic] in H.
    destruct (lookup_module net start) as [m |] eqn:Hm; [| discriminate].
    destruct ((mod_states gs) ?? (unwrap start)) as [ls |] eqn:Hls; [| discriminate].
    apply (fold_left_opt_inv
             (fun g => mem_rooted m0 (sh_mem g))
             (fun g d => eval_network_from_symbolic net d
                           (sh_hdr_map (module_update_gs_symbolic m
                              (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
                           (sh_read_tape (module_update_gs_symbolic m
                              (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
                           g fuel)
             (downstream_modules net start)
             (Some (module_update_gs_symbolic m
                      (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs))
             gs').
    + intros g d g' Hg Hstep. eapply IH; eauto.
    + cbn. apply module_update_gs_symbolic_mem_rooted. exact Hgs.
    + exact H.
Qed.

(* The initial map's entries are all leaves ([SmtArrVar] for a declared region,
   [SmtArrInit] for the default), which is what makes rooting reflexive. *)
Lemma init_symbolic_mem_leaf : forall rs k, arr_leaf ((init_symbolic_mem rs) !! k).
Proof.
  intros rs k. unfold init_symbolic_mem.
  assert (Hgen : forall rs' m, (forall k', arr_leaf (m !! k')) ->
            arr_leaf ((List.fold_left
              (fun acc d => PMap.set (unwrap (mr_id d))
                 (SmtArrVar ("mem_" ++ pos_to_string (unwrap (mr_id d)))
                            (repr (Z.of_nat (mr_len d)))) acc) rs' m) !! k)).
  { intros rs'. induction rs' as [| d rs' IH]; intros m Hm.
    - cbn. apply Hm.
    - cbn. apply IH. intros k'.
      destruct (Coqlib.peq k' (unwrap (mr_id d))) as [He | Hne].
      + subst k'. rewrite PMap.gss. exact I.
      + rewrite PMap.gso by exact Hne. apply Hm. }
  apply Hgen. intros k'. rewrite PMap.gi. exact I.
Qed.

Lemma init_symbolic_mem_rooted : forall rs,
  mem_rooted (init_symbolic_mem rs) (init_symbolic_mem rs).
Proof.
  intros rs k. apply arr_rooted_refl. apply init_symbolic_mem_leaf.
Qed.

(* [check_sym_region_equal] builds its indices with [repr]; the conclusion
   states them with [mk_int u64].  Both mask to the same 64-bit value. *)
Lemma mask_width_W64_unsigned_repr : forall z : Z,
  mask_width W64 (@unsigned 64%positive (@repr 64%positive z)) = mask_width W64 z.
Proof.
  intro z. unfold mask_width, width_bits.
  assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
  rewrite !Z.land_ones by lia.
  cbn [unsigned repr intval]. rewrite Z_mod_modulus_eq, Hmod.
  rewrite Zmod_mod. reflexivity.
Qed.

Lemma mk_int_u64_unsigned_repr : forall z : Z,
  mk_int u64 (@unsigned 64%positive (@repr 64%positive z)) = mk_int u64 z.
Proof.
  intro z. unfold mk_int, u64, it_width. f_equal.
  apply mask_width_W64_unsigned_repr.
Qed.

Lemma eval_general_program_symbolic_mem_rooted : forall p pre s,
  eval_general_program_symbolic p (init_general_symbolic_state pre p) = Some s ->
  mem_rooted (init_symbolic_mem (get_mem_regions_from_general p)) (sh_mem s).
Proof.
  intros p pre s H.
  unfold eval_general_program_symbolic in H.
  destruct ((mod_states (init_general_symbolic_state pre p))
              ?? (unwrap (start_module (get_network_from_general p)))) eqn:Hst;
    [| discriminate].
  eapply eval_network_from_symbolic_mem_rooted; [| exact H].
  cbn [init_general_symbolic_state sh_mem]. apply init_symbolic_mem_rooted.
Qed.

(* The checker's region guard is an equality test, so the two programs really
   do declare the same list -- which is what lets both symbolic runs be rooted
   at ONE initial memory map. *)
Lemma mem_region_decl_eqb_eq : forall a b, mem_region_decl_eqb a b = true -> a = b.
Proof.
  intros [ia la] [ib lb] H. unfold mem_region_decl_eqb in H. cbn in H.
  apply Bool.andb_true_iff in H as [Hi Hl].
  apply PeanoNat.Nat.eqb_eq in Hl.
  assert (Hi' : ia = ib).
  { apply (@posesque_eqb_iff MemRegion Posesque_MemRegion). exact Hi. }
  subst. reflexivity.
Qed.

Lemma mem_region_decls_eqb_eq : forall a b, mem_region_decls_eqb a b = true -> a = b.
Proof.
  intros a. induction a as [| x a IH]; intros b H;
    unfold mem_region_decls_eqb in H; apply Bool.andb_true_iff in H as [Hlen Hall].
  - destruct b; [reflexivity | cbn in Hlen; discriminate].
  - destruct b as [| y b]; [cbn in Hlen; discriminate |].
    cbn in Hlen, Hall. apply Bool.andb_true_iff in Hall as [Hxy Hrest].
    apply mem_region_decl_eqb_eq in Hxy. subst y. f_equal.
    apply IH. unfold mem_region_decls_eqb. apply Bool.andb_true_iff.
    split; [exact Hlen | exact Hrest].
Qed.

(* Equal loaded VALUES become an equal LOAD once both regions are known to have
   the same shape -- otherwise [Legal ErrorVal] on one side and [Illegal] on
   the other would agree on the value and differ here. *)
Lemma ld_arr_eq_of_val_eq : forall (A1 A2 : @Array CrVal) idx,
  (match A1, A2 with
   | Unallocated, Unallocated => True
   | Allocated b1, Allocated b2 => arr_len b1 = arr_len b2
   | _, _ => False
   end) ->
  (match ld_arr A1 idx with Legal v => v | Illegal => ErrorVal end)
    = (match ld_arr A2 idx with Legal v => v | Illegal => ErrorVal end) ->
  ld_arr A1 idx = ld_arr A2 idx.
Proof.
  intros A1 A2 idx Hshape Hval.
  destruct A1 as [b1 |]; destruct A2 as [b2 |]; try contradiction.
  - cbn [ld_arr]. destruct idx as [i ti | |]; try reflexivity.
    rewrite Hshape. destruct (Integers.ltu i (arr_len b2)) eqn:Hlt; [| reflexivity].
    cbn [ld_arr] in Hval. rewrite Hshape, Hlt in Hval.
    destruct ((arr_bytes b1) !! (offset_to_key i)) eqn:H1;
      destruct ((arr_bytes b2) !! (offset_to_key i)) eqn:H2;
      cbn in Hval |- *; congruence.
  - cbn. reflexivity.
Qed.

(* ---------- the two memory conjuncts, concretized ---------- *)

Lemma check_sym_mem_extent_sound : forall rs s1 s2 f,
  eval_smt_bool (check_sym_mem_extent rs s1 s2) f = true ->
  List.Forall (fun d =>
    (sh_mem_extent (concretize_sym_modnet_state s1 f)) !! (unwrap (mr_id d)) =
    (sh_mem_extent (concretize_sym_modnet_state s2 f)) !! (unwrap (mr_id d))) rs.
Proof.
  intros rs s1 s2 f H.
  unfold check_sym_mem_extent in H.
  apply fold_and_true in H.
  eapply List.Forall_impl; [| exact H]. cbn beta.
  intros d Hd.
  cbn [concretize_sym_modnet_state sh_mem_extent].
  rewrite !PMap.gmap.
  apply smt_bool_eq_true. exact Hd.
Qed.

Lemma check_crval_eqb_eq : forall x y, check_crval_eqb x y = true -> x = y.
Proof.
  intros [a |] [b |] H; cbn in H; try discriminate; try reflexivity.
  f_equal. apply crval_concrete_if_else. rewrite H. reflexivity.
Qed.

(* With [SmtArrEq] the checker constrains the LOADS directly, so this no longer
   needs to know anything about the shape of the two regions -- the rooting
   invariant above is not used here.  It has not become pointless: it is the
   Coq-side evidence that lowering [SmtArrEq] to one extensional array equality
   is faithful, since a rooted region agrees with its root outside the declared
   length.  See [SOUNDNESS.md]. *)
Lemma check_sym_mem_equal_sound : forall rs s1 s2 f,
  eval_smt_bool (check_sym_mem_equal rs s1 s2) f = true ->
  List.Forall (fun d => forall i, (i < mr_len d)%nat ->
    ld_arr ((sh_mem (concretize_sym_modnet_state s1 f)) !! (unwrap (mr_id d)))
           (mk_int u64 (Z.of_nat i)) =
    ld_arr ((sh_mem (concretize_sym_modnet_state s2 f)) !! (unwrap (mr_id d)))
           (mk_int u64 (Z.of_nat i))) rs.
Proof.
  intros rs s1 s2 f H.
  unfold check_sym_mem_equal in H.
  apply fold_and_true in H.
  eapply List.Forall_impl; [| exact H]. cbn beta.
  intros d Hd i Hi.
  unfold check_sym_region_equal in Hd. cbn [eval_smt_bool] in Hd.
  unfold arr_agree_upto in Hd. rewrite List.forallb_forall in Hd.
  assert (Hin : List.In i (List.seq 0 (mr_len d))) by (apply List.in_seq; lia).
  specialize (Hd i Hin).
  cbn [concretize_sym_modnet_state sh_mem]. rewrite !PMap.gmap.
  apply check_crval_eqb_eq. exact Hd.
Qed.

(* ---------- the same conjuncts, in the failing direction ---------- *)

Lemma smt_iff_false : forall a b f,
  eval_smt_bool (smt_iff a b) f = false ->
  eval_smt_bool a f <> eval_smt_bool b f.
Proof.
  intros a b f H. unfold smt_iff in H. cbn [eval_smt_bool] in H.
  destruct (eval_smt_bool a f), (eval_smt_bool b f); cbn in H;
    try discriminate; congruence.
Qed.

(* One step of [sym_out_equal], with both presence conditions known present.
   Stated as an iff so both directions of the checker can use it. *)
Lemma sym_out_equal_cons : forall b1 r1 b2 r2 f,
  cvc b1 = SmtTrue -> cvc b2 = SmtTrue ->
  (eval_smt_bool (sym_out_equal (b1 :: r1) (b2 :: r2)) f = true
   <-> (eval_smt_bool (cvv b1) f = eval_smt_bool (cvv b2) f
        /\ eval_smt_bool (sym_out_equal r1 r2) f = true)).
Proof.
  intros b1 r1 b2 r2 f Hc1 Hc2.
  cbn [sym_out_equal]. rewrite Hc1, Hc2.
  unfold smt_iff, smt_implies. cbn [eval_smt_bool].
  destruct (eval_smt_bool (cvv b1) f), (eval_smt_bool (cvv b2) f),
           (eval_smt_bool (sym_out_equal r1 r2) f); cbn;
    intuition congruence.
Qed.

Lemma sym_out_equal_complete : forall o1 o2 f,
  wt_unconditional o1 -> wt_unconditional o2 ->
  eval_smt_bool (sym_out_equal o1 o2) f = false ->
  List.length o1 <> List.length o2 \/
  ~ List.Forall (fun '(b1, b2) => b1 = b2)
      (List.combine (List.map (fun b => eval_smt_bool (cvv b) f) o1)
                    (List.map (fun b => eval_smt_bool (cvv b) f) o2)).
Proof.
  induction o1 as [| b1 r1 IH]; intros o2 f H1 H2 H.
  - destruct o2 as [| b2 r2].
    + cbn in H. discriminate.
    + left. cbn. discriminate.
  - destruct o2 as [| b2 r2].
    + left. cbn. discriminate.
    + inversion H1 as [| ? ? Hc1 Hr1]; subst.
      inversion H2 as [| ? ? Hc2 Hr2]; subst.
      destruct (Bool.eqb (eval_smt_bool (cvv b1) f) (eval_smt_bool (cvv b2) f)) eqn:Hbits.
      * (* head bits agree, so the tail is what failed *)
        assert (Hb : eval_smt_bool (cvv b1) f = eval_smt_bool (cvv b2) f)
          by (apply Bool.eqb_prop; exact Hbits).
        destruct (eval_smt_bool (sym_out_equal r1 r2) f) eqn:Htail.
        -- exfalso.
           rewrite (proj2 (sym_out_equal_cons b1 r1 b2 r2 f Hc1 Hc2)
                      (conj Hb Htail)) in H. discriminate.
        -- destruct (IH r2 f Hr1 Hr2 Htail) as [Hlen | Hall].
           ++ left. cbn. intro Hc. apply Hlen. injection Hc. auto.
           ++ right. cbn [List.map List.combine]. intro Hc.
              apply Hall. exact (List.Forall_inv_tail Hc).
      * (* the head bits themselves differ *)
        right. cbn [List.map List.combine]. intro Hc.
        pose proof (List.Forall_inv Hc) as Hhead. cbn in Hhead.
        rewrite Hhead in Hbits. rewrite Bool.eqb_reflx in Hbits. discriminate.
Qed.

(* Dual of [fold_and_true]: a false conjunction has a false conjunct. *)
Lemma fold_and_false : forall {A : Type} (P : A -> SmtBoolExpr) (l : list A) f,
  eval_smt_bool (List.fold_right (fun x acc => SmtBoolAnd acc (P x)) SmtTrue l) f = false ->
  exists x, List.In x l /\ eval_smt_bool (P x) f = false.
Proof.
  intros A P l f. induction l as [| x l IH]; intros H.
  - cbn in H. discriminate.
  - cbn [List.fold_right] in H. cbn [eval_smt_bool] in H.
    apply Bool.andb_false_iff in H as [Hacc | Hx].
    + destruct (IH Hacc) as [y [Hin Hy]]. exists y. split; [right; exact Hin | exact Hy].
    + exists x. split; [left; reflexivity | exact Hx].
Qed.

Lemma check_sym_mem_extent_complete : forall rs s1 s2 f,
  eval_smt_bool (check_sym_mem_extent rs s1 s2) f = false ->
  ~ List.Forall (fun d =>
      (sh_mem_extent (concretize_sym_modnet_state s1 f)) !! (unwrap (mr_id d)) =
      (sh_mem_extent (concretize_sym_modnet_state s2 f)) !! (unwrap (mr_id d))) rs.
Proof.
  intros rs s1 s2 f H.
  unfold check_sym_mem_extent in H.
  apply fold_and_false in H. destruct H as [d [Hin Hd]].
  apply smt_bool_eq_false in Hd.
  intro Hall. rewrite List.Forall_forall in Hall.
  specialize (Hall d Hin).
  cbn [concretize_sym_modnet_state sh_mem_extent] in Hall.
  rewrite !PMap.gmap in Hall. contradiction.
Qed.

(* Note what this direction does NOT need: [_sound] had to know both regions
   have the same shape before an equality of loaded values became an equality of
   loads.  Here the implication runs the easy way -- differing values force
   differing loads outright -- so no rooting invariant is involved. *)
Lemma check_crval_eqb_neq : forall x y, check_crval_eqb x y = false -> x <> y.
Proof.
  intros [a |] [b |] H; cbn in H; try discriminate; try congruence.
  intro Hc. injection Hc as Hc. subst b.
  rewrite CrVal.eqb_refl in H. discriminate.
Qed.

Lemma forallb_false_exists : forall {A : Type} (g : A -> bool) (l : list A),
  List.forallb g l = false -> exists x, List.In x l /\ g x = false.
Proof.
  intros A g l. induction l as [| x l IH]; intros H; cbn in H.
  - discriminate.
  - apply Bool.andb_false_iff in H as [Hx | Hl].
    + exists x. split; [left; reflexivity | exact Hx].
    + destruct (IH Hl) as [y [Hin Hy]]. exists y. split; [right; exact Hin | exact Hy].
Qed.

(* As before, this direction runs the easy way round and needs no invariant. *)
Lemma check_sym_mem_equal_complete : forall rs s1 s2 f,
  eval_smt_bool (check_sym_mem_equal rs s1 s2) f = false ->
  ~ List.Forall (fun d => forall i, (i < mr_len d)%nat ->
      ld_arr ((sh_mem (concretize_sym_modnet_state s1 f)) !! (unwrap (mr_id d)))
             (mk_int u64 (Z.of_nat i)) =
      ld_arr ((sh_mem (concretize_sym_modnet_state s2 f)) !! (unwrap (mr_id d)))
             (mk_int u64 (Z.of_nat i))) rs.
Proof.
  intros rs s1 s2 f H.
  unfold check_sym_mem_equal in H.
  apply fold_and_false in H. destruct H as [d [Hin Hd]].
  unfold check_sym_region_equal in Hd. cbn [eval_smt_bool] in Hd.
  unfold arr_agree_upto in Hd.
  apply forallb_false_exists in Hd. destruct Hd as [i [Hini Hi]].
  apply List.in_seq in Hini. destruct Hini as [_ Hlt]. cbn in Hlt.
  apply check_crval_eqb_neq in Hi.
  intro Hall. rewrite List.Forall_forall in Hall.
  specialize (Hall d Hin i Hlt).
  cbn [concretize_sym_modnet_state sh_mem] in Hall.
  rewrite !PMap.gmap in Hall. contradiction.
Qed.

Lemma modnet_equivalence_checker_sound :
  forall p1 p2,
  (* if two well-formed programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and they're considered equivalent *)
  modnet_equivalence_checker p1 p2 = Equivalent ->
  (* if we run them from their initial symbolic states *)
  forall s_i1 s_i2 s_f1 s_f2,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  eval_general_program_symbolic p1 s_i1 = Some s_f1 ->
  eval_general_program_symbolic p2 s_i2 = Some s_f2 ->
  (* then for every valuation of the symbolic variables *)
  forall c_f1 c_f2 (f : SmtValuation),
  (* the concretized outputs *)
  concretize_sym_modnet_state s_f1 f = c_f1 ->
  concretize_sym_modnet_state s_f2 f = c_f2 ->
  (* both are invalid *)
  (gps_valid c_f1 = false /\ gps_valid c_f2 = false)
  (* or both are valid and have identical output packets *)
  \/
  ( gps_valid c_f1 = true /\ gps_valid c_f2 = true /\
    List.length (sh_write_tape c_f1) = List.length (sh_write_tape c_f2) /\
    (* ...consumed the same amount of the input packet ([check_sym_bits_read]).
       Stated over [sh_bits_read] rather than the residual's list length: the
       symbolic residual is padded by [merge_bitstream], so its raw length is
       not the read extent and concretization does not shrink it. *)
    sh_bits_read c_f1 = sh_bits_read c_f2 /\
    List.Forall (fun '(b1, b2) => b1 = b2)
      (List.combine (sh_write_tape c_f1) (sh_write_tape c_f2)) /\
    (* ...left every declared region holding the same contents
       ([check_sym_mem_equal]), cell by cell over the declared length -- the
       checker never constrains cells past it, so neither does this... *)
    List.Forall (fun d =>
      forall i, (i < mr_len d)%nat ->
        ld_arr ((sh_mem c_f1) !! (unwrap (mr_id d))) (mk_int u64 (Z.of_nat i)) =
        ld_arr ((sh_mem c_f2) !! (unwrap (mr_id d))) (mk_int u64 (Z.of_nat i)))
      (get_mem_regions_from_general p1) /\
    (* ...and reached the same distance into each region
       ([check_sym_mem_extent]), the memory analogue of [sh_bits_read]. *)
    List.Forall (fun d =>
      (sh_mem_extent c_f1) !! (unwrap (mr_id d)) =
      (sh_mem_extent c_f2) !! (unwrap (mr_id d)))
      (get_mem_regions_from_general p1)).
Proof.
  intros p1 p2 Hwf1 Hwf2 Hlc1 Hlc2 Hcheck s_i1 s_i2 s_f1 s_f2 Hi1 Hi2 He1 He2
         c_f1 c_f2 f Hc1 Hc2.
  subst s_i1 s_i2 c_f1 c_f2.
  (* The one invariant this needs is that the write tape is unconditionally
     present; see [wt_unconditional].  (The memory rooting above is not needed
     by either direction any more -- it is the encoding argument for
     [SmtArrEq], not a proof obligation here.) *)
  pose proof (eval_general_program_symbolic_wt _ _ _ He1) as Hwt1.
  pose proof (eval_general_program_symbolic_wt _ _ _ He2) as Hwt2.
  unfold modnet_equivalence_checker in Hcheck.
  destruct (andb (Nat.eqb (get_inp_len_from_general p1) (get_inp_len_from_general p2))
                 (mem_region_decls_eqb (get_mem_regions_from_general p1)
                                       (get_mem_regions_from_general p2))) eqn:Hguard;
    [| discriminate].
  (* The checker ran exactly the evaluations the hypotheses name. *)
  rewrite He1, He2 in Hcheck.
  destruct (smt_query (check_sym_pkt_out (get_mem_regions_from_general p1) s_f1 s_f2))
    eqn:Hq; try discriminate. clear Hcheck.
  (* Unsat means the negated agreement formula is false under EVERY valuation,
     so agreement itself holds under [f]. *)
  pose proof (smt_query_sound_none _ Hq f) as Hff.
  unfold check_sym_pkt_out in Hff.
  cbn [eval_smt_bool] in Hff.
  apply Bool.negb_false_iff in Hff.
  apply Bool.orb_true_iff in Hff. destruct Hff as [Hreject | Haccept].
  - (* both runs rejected *)
    left.
    apply Bool.andb_true_iff in Hreject as [H1 H2].
    apply Bool.negb_true_iff in H1. apply Bool.negb_true_iff in H2.
    cbn [concretize_sym_modnet_state gps_valid]. split; assumption.
  - (* both accepted, and every observable agrees *)
    right.
    apply Bool.andb_true_iff in Haccept as [Hvalid Hrest].
    apply Bool.andb_true_iff in Hvalid as [Hv1 Hv2].
    apply Bool.andb_true_iff in Hrest as [Hpkt Hmem].
    apply Bool.andb_true_iff in Hpkt as [Hout Hbits].
    apply Bool.andb_true_iff in Hmem as [Hmemeq Hmemext].
    pose proof (sym_out_equal_sound _ _ f Hwt1 Hwt2 Hout) as [Hlen Hbitsall].
    unfold check_sym_bits_read in Hbits.
    cbn [concretize_sym_modnet_state gps_valid sh_write_tape sh_bits_read].
    split; [exact Hv1 |].
    split; [exact Hv2 |].
    split; [rewrite !List.length_map; exact Hlen |].
    split; [apply smt_bool_eq_true; exact Hbits |].
    split; [exact Hbitsall |].
    split.
    + apply check_sym_mem_equal_sound. exact Hmemeq.
    + apply check_sym_mem_extent_sound. exact Hmemext.
Qed.

Lemma modnet_equivalence_checker_complete :
  forall p1 p2 f,
  (* if two well-formed programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and they're considered not equivalent with witness f *)
  modnet_equivalence_checker p1 p2 = NotEquivalent f ->
  (* if we run them from their initial symbolic states *)
  forall s_i1 s_i2 s_f1 s_f2,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  eval_general_program_symbolic p1 s_i1 = Some s_f1 ->
  eval_general_program_symbolic p2 s_i2 = Some s_f2 ->
  (* for the concretized outputs under f *)
  forall c_f1 c_f2,
  concretize_sym_modnet_state s_f1 f = c_f1 ->
  concretize_sym_modnet_state s_f2 f = c_f2 ->
  (* either the accept flags are not equal *)
  (gps_valid c_f1 <> gps_valid c_f2)
  (* or the emitted output packets are not equal *)
  \/
  ( gps_valid c_f1 = true /\ gps_valid c_f2 = true /\
    ( List.length (sh_write_tape c_f1) <> List.length (sh_write_tape c_f2) \/
      sh_bits_read c_f1 <> sh_bits_read c_f2 \/
    ~ List.Forall (fun '(b1, b2) => b1 = b2)
      (List.combine (sh_write_tape c_f1) (sh_write_tape c_f2)) \/
    (* ...or a declared region's contents differ somewhere in bounds... *)
    ~ List.Forall (fun d =>
        forall i, (i < mr_len d)%nat ->
          ld_arr ((sh_mem c_f1) !! (unwrap (mr_id d))) (mk_int u64 (Z.of_nat i)) =
          ld_arr ((sh_mem c_f2) !! (unwrap (mr_id d))) (mk_int u64 (Z.of_nat i)))
        (get_mem_regions_from_general p1) \/
    (* ...or one run reached further into some region than the other. *)
    ~ List.Forall (fun d =>
        (sh_mem_extent c_f1) !! (unwrap (mr_id d)) =
        (sh_mem_extent c_f2) !! (unwrap (mr_id d)))
        (get_mem_regions_from_general p1))).
Proof.
  intros p1 p2 f Hwf1 Hwf2 Hlc1 Hlc2 Hcheck s_i1 s_i2 s_f1 s_f2 Hi1 Hi2 He1 He2
         c_f1 c_f2 Hc1 Hc2.
  subst s_i1 s_i2 c_f1 c_f2.
  (* Only the write-tape invariant is needed here.  The memory rooting that
     [_sound] required is not: there the implication ran from equal loaded
     values to equal loads (which needs both regions to have the same shape),
     here it runs the easy way round. *)
  pose proof (eval_general_program_symbolic_wt _ _ _ He1) as Hwt1.
  pose proof (eval_general_program_symbolic_wt _ _ _ He2) as Hwt2.
  unfold modnet_equivalence_checker in Hcheck.
  destruct (andb (Nat.eqb (get_inp_len_from_general p1) (get_inp_len_from_general p2))
                 (mem_region_decls_eqb (get_mem_regions_from_general p1)
                                       (get_mem_regions_from_general p2))) eqn:Hguard;
    [| discriminate].
  rewrite He1, He2 in Hcheck.
  destruct (smt_query (check_sym_pkt_out (get_mem_regions_from_general p1) s_f1 s_f2))
    as [v | |] eqn:Hq; try discriminate.
  injection Hcheck as Hvf. subst v.
  (* Sat means the negated agreement formula holds under the witness, i.e.
     agreement itself fails there. *)
  pose proof (smt_query_sound_some _ _ Hq) as Htrue.
  unfold check_sym_pkt_out in Htrue. cbn [eval_smt_bool] in Htrue.
  apply Bool.negb_true_iff in Htrue.
  apply Bool.orb_false_iff in Htrue as [HA HB].
  cbn [concretize_sym_modnet_state gps_valid sh_write_tape sh_bits_read].
  destruct (eval_smt_bool (cvv (gps_valid s_f1)) f) eqn:Ha;
    destruct (eval_smt_bool (cvv (gps_valid s_f2)) f) eqn:Hb.
  - (* both accepted: some observable must be the one that differs *)
    right. split; [reflexivity |]. split; [reflexivity |].
    cbn in HB.
    apply Bool.andb_false_iff in HB as [Hpkt | Hmem].
    + apply Bool.andb_false_iff in Hpkt as [Hout | Hbits].
      * destruct (sym_out_equal_complete _ _ f Hwt1 Hwt2 Hout) as [Hlen | Hall].
        -- left. rewrite !List.length_map. exact Hlen.
        -- right. right. left. exact Hall.
      * right. left. unfold check_sym_bits_read in Hbits.
        apply smt_bool_eq_false. exact Hbits.
    + apply Bool.andb_false_iff in Hmem as [Hmemeq | Hmemext].
      * right. right. right. left.
        apply check_sym_mem_equal_complete. exact Hmemeq.
      * right. right. right. right.
        apply check_sym_mem_extent_complete. exact Hmemext.
  - (* accept flags disagree *) left. discriminate.
  - (* accept flags disagree *) left. discriminate.
  - (* both rejected is an accepting case, so this cannot be a Sat witness *)
    cbn in HA. discriminate.
Qed.
