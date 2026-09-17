(* The network level of the symbolic-to-concrete bridge.

   The levels below are proved elsewhere: [MemCommuteLemmas] for a transformer
   with memory threaded, [ParserCommuteLemmas.eval_parser_commute] for a
   parser, [DeparserCommuteLemmas.eval_deparser_commute] for a deparser.  This
   file is the induction over [eval_network_from_*] that assembles them, the
   node-level correspondences the two [eval_general_program_*] wrappers need
   around it, and the entry conditions that induction turns out to require --
   ending at [program_commute_init], which is what
   [SmtModuleQuery.eval_general_program_commute] is proved from.

   The relation being transported is NOT an equality of states.  It cannot be:
   see [SmtModuleQuery.gps_agree] and the note on it.  After one module the
   concrete memory is no longer literally [PMap.map] of the symbolic memory,
   only equal to it at every key, which is why [MemCommuteLemmas] §6 proves the
   concrete evaluator is a congruence for that. *)

From MyProject Require Import CrIdentifiers CrDsl CrTransformer CrParser CrModule CrProgramState
     CrGeneralProgramState CrVarLike CrVal Maps MyInts Integers Coqlib
     SmtExpr SmtTypes ListUtils ParserWellFormed ParserTerminationLemmas
     CrConcreteSemanticsTransformer CrConcreteSemanticsParser
     CrConcreteSemanticsDeparser CrConcreteSemanticsModule
     CrSymbolicSemanticsTransformer CrSymbolicSemanticsParser
     CrSymbolicSemanticsDeparser CrSymbolicSemanticsModule
     MemCommuteLemmas ParserCommuteLemmas DeparserCommuteLemmas CrDslProperties.
From Stdlib Require Import List ZArith micromega.Lia.
Import ListNotations.

Local Open Scope Z_scope.

(* ==================================================================== *)
(* 1. THE KEY SET OF A CONCRETIZED MAP.                                  *)
(*                                                                       *)
(* [concretize_sym_modnet_state] is [PMap.map] on every map it carries,  *)
(* and [PMap.map] is [PTree.map1], which preserves bindings.  So the two *)
(* sides enumerate the same keys -- which is what lets the memory-safety *)
(* check, the one thing in either semantics that looks at a key SET,     *)
(* correspond at all.                                                    *)
(* ==================================================================== *)

Lemma pmap_keys_map : forall (A B : Type) (g : A -> B) (m : PMap.t A),
  pmap_keys (PMap.map g m) = pmap_keys m.
Proof.
  intros A B g m. unfold pmap_keys, PMap.map. cbn [snd].
  assert (H := @PTree.elements_canonical_order' A B (fun (a : A) (b : B) => b = g a)
                 (snd m) (PTree.map1 g (snd m))).
  lapply H; [clear H; intro H | intros i; rewrite PTree.gmap1;
             destruct (PTree.get i (snd m)); cbn [option_map]; constructor; reflexivity ].
  symmetry.
  induction H as [| x y l1 l2 Hxy Hrest IH]; cbn [List.map]; [reflexivity |].
  destruct Hxy as [Hf _]. rewrite Hf, IH. reflexivity.
Qed.

(* ==================================================================== *)
(* 2. THE MEMORY-SAFETY CHECK CORRESPONDS.                               *)
(*                                                                       *)
(* [mem_extents_in_bounds_smt] was written as a node-for-node mirror of  *)
(* [mem_extents_in_bounds_concrete]; this is the statement that says so. *)
(* The one wrinkle is associativity: the concrete side is a [forallb],   *)
(* which conjoins head-first, and the symbolic side a [fold_right] that  *)
(* puts the accumulator on the LEFT of each [SmtBoolAnd], so the two     *)
(* bracket the same conjuncts in opposite orders.                        *)
(* ==================================================================== *)

(* [SmtArithConst (mask_width W64 n) u64] denotes [mk_int u64 n]: the constant
   is stored already masked, and evaluating it masks again. *)
Lemma mk_int_u64_mask_idem : forall z,
  mk_int u64 (unsigned (mask_width W64 z)) = mk_int u64 z.
Proof.
  intro z. unfold mk_int, u64. cbn [it_width]. f_equal.
  apply mask_width_W64_unsigned_idem.
Qed.

Lemma extent_conjunct_commute : forall lens k ext f,
  negb (CrVal.ltb (mk_int u64 (Z.of_nat (lens !! k)))
                  ((PMap.map (fun e => eval_smt_arith e f) ext) !! k))
  = eval_smt_bool
      (SmtBoolNot (SmtBoolLt (SmtArithConst (mask_width W64 (Z.of_nat (lens !! k))) u64)
                             (ext !! k))) f.
Proof.
  intros lens k ext f. cbn [eval_smt_bool eval_smt_arith].
  rewrite PMap.gmap, mk_int_u64_mask_idem. reflexivity.
Qed.

Lemma extents_fold_commute : forall lens l ext f,
  List.forallb
    (fun k => negb (CrVal.ltb (mk_int u64 (Z.of_nat (lens !! k)))
                              ((PMap.map (fun e => eval_smt_arith e f) ext) !! k))) l
  = eval_smt_bool
      (List.fold_right
        (fun k acc =>
          SmtBoolAnd acc
            (SmtBoolNot
              (SmtBoolLt (SmtArithConst (mask_width W64 (Z.of_nat (lens !! k))) u64)
                         (ext !! k))))
        SmtTrue l) f.
Proof.
  intros lens l ext f. induction l as [| k r IH]; cbn [List.forallb List.fold_right].
  - reflexivity.
  - cbn [eval_smt_bool]. rewrite <- IH, extent_conjunct_commute.
    apply andb_comm.
Qed.

Theorem mem_extents_in_bounds_commute : forall rs ext f,
  mem_extents_in_bounds_concrete rs (PMap.map (fun e => eval_smt_arith e f) ext)
  = eval_smt_bool (mem_extents_in_bounds_smt rs ext) f.
Proof.
  intros rs ext f.
  unfold mem_extents_in_bounds_concrete, mem_extents_in_bounds_smt. cbv zeta.
  rewrite pmap_keys_map. apply extents_fold_commute.
Qed.

(* ==================================================================== *)
(* 3. THE NETWORK FOLD, UNDER [no_fan_out].                              *)
(*                                                                       *)
(* [eval_network_from_*] folds over [downstream_modules], which under    *)
(* [is_linear_chain] holds at most one name.  So the fold is not really  *)
(* a fold: it is "stop here" or "one more module".  Proving that once,   *)
(* on both evaluators, is what lets the induction below be an ordinary   *)
(* one on fuel rather than a relational analogue of [fold_left].         *)
(* ==================================================================== *)

Lemma downstream_cases : forall net start,
  no_fan_out net ->
  downstream_modules net start = []
  \/ exists dst, downstream_modules net start = [dst].
Proof.
  intros net start Hnf. specialize (Hnf start).
  destruct (downstream_modules net start) as [| a [| b l]].
  - left. reflexivity.
  - right. exists a. reflexivity.
  - cbn [List.length] in Hnf. lia.
Qed.

Lemma network_concrete_step : forall net start f_hdrs f_bits gs fuel',
  eval_network_from_concrete net start f_hdrs f_bits gs (S fuel') =
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
      let gs' := module_update_gs_concrete m
                   (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs in
      List.fold_left
        (fun acc dst =>
          match acc with
          | None => None
          | Some gs_acc =>
              eval_network_from_concrete net dst (sh_hdr_map gs') (sh_read_tape gs') gs_acc fuel'
          end)
        (downstream_modules net start) (Some gs')
  | _, _ => None
  end.
Proof. reflexivity. Qed.

Lemma network_symbolic_step : forall net start f_hdrs f_bits gs fuel',
  eval_network_from_symbolic net start f_hdrs f_bits gs (S fuel') =
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
      let gs' := module_update_gs_symbolic m
                   (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs in
      List.fold_left
        (fun acc dst =>
          match acc with
          | None => None
          | Some gs_acc =>
              eval_network_from_symbolic net dst (sh_hdr_map gs') (sh_read_tape gs') gs_acc fuel'
          end)
        (downstream_modules net start) (Some gs')
  | _, _ => None
  end.
Proof. reflexivity. Qed.

(* ==================================================================== *)
(* 4. REJECTION IS ABSORBING, ON BOTH SIDES.                             *)
(*                                                                       *)
(* This is what makes the bridge's first conjunct -- the verdicts agree  *)
(* -- survive the modules that run AFTER a rejection, where the two      *)
(* states have genuinely diverged and no commutation lemma applies.      *)
(* Neither semantics can clear the flag: every writer conjoins.  So once *)
(* both runs are invalid they stay invalid, and the flags agree for the  *)
(* rest of the network without anything being known about the states.    *)
(* ==================================================================== *)

Lemma module_update_concrete_invalid : forall m ls gs,
  gps_valid gs = false ->
  gps_valid (module_update_gs_concrete m ls gs) = false.
Proof.
  intros m ls gs H. unfold module_update_gs_concrete.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    cbv zeta; cbn [gps_valid set_gps_valid set_gps_mod_states set_gps_mem
                   set_gps_mem_extent set_gps_shared_headers set_gps_bits_read
                   set_gps_shared_read_tape set_gps_shared_write_tape];
    try reflexivity; try exact H.
  destruct (eval_parser_concrete pp ps) as [r |];
    cbn [gps_valid set_gps_valid set_gps_mod_states set_gps_bits_read
         set_gps_shared_read_tape set_gps_shared_headers];
    [ rewrite H; reflexivity | reflexivity ].
Qed.

Lemma module_update_symbolic_invalid : forall m ls gs f,
  eval_smt_bool (cvv (gps_valid gs)) f = false ->
  eval_smt_bool (cvv (gps_valid (module_update_gs_symbolic m ls gs))) f = false.
Proof.
  intros m ls gs f H. unfold module_update_gs_symbolic.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    cbv zeta; cbn [gps_valid cvv set_gps_valid set_gps_mod_states set_gps_mem
                   set_gps_mem_extent set_gps_shared_headers set_gps_bits_read
                   set_gps_shared_read_tape set_gps_shared_write_tape];
    try reflexivity; try exact H.
  cbn [eval_smt_bool]. rewrite H. reflexivity.
Qed.

(* ==================================================================== *)
(* 5. THE DEPARSER MODULE.                                               *)
(*                                                                       *)
(* The easy kind, and it is worth saying why it is easy: a deparser reads *)
(* only its header map.  It overwrites [p_packet] with what it emitted    *)
(* and [p_cursor] with 0, so the packet it was handed is irrelevant.      *)
(*                                                                       *)
(* That is not a convenience, it is load-bearing at the network level.    *)
(* The packet a deparser is handed is the READ tape, which concretizes    *)
(* through [present_bits] -- a filter -- while                            *)
(* [concretize_sym_module_state]'s [DeparserMod] branch maps positionally. *)
(* The two genuinely disagree about the incoming packet, and the only     *)
(* reason that does not matter is that nothing reads it.                  *)
(* ==================================================================== *)

Lemma eval_deparser_concrete_cong : forall d ps1 ps2,
  p_header_map ps1 = p_header_map ps2 ->
  eval_deparser_concrete d ps1 = eval_deparser_concrete d ps2.
Proof.
  intros d ps1 ps2 H. unfold eval_deparser_concrete. rewrite H. reflexivity.
Qed.

Theorem deparser_mod_commute : forall d ps f cpkt,
  DeparserMod (eval_deparser_concrete d
    {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
       p_packet     := cpkt;
       p_cursor     := 0 |})
  = concretize_sym_module_state (DeparserMod (eval_deparser_symbolic d ps)) f.
Proof.
  intros d ps f cpkt.
  rewrite (eval_deparser_concrete_cong d _
    {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
       p_packet     := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet ps);
       p_cursor     := p_cursor ps |}) by reflexivity.
  cbn [concretize_sym_module_state]. f_equal. apply eval_deparser_commute.
Qed.

(* ==================================================================== *)
(* 6. THREADING THE HEADER MAP IN.                                       *)
(*                                                                       *)
(* Both network recursions hand the next module the shared header map     *)
(* through [set_module_header_map], and for a transformer that is         *)
(* [inject_headers].  Concretization commutes with it, so a module can be *)
(* given the concretized map or the concretization of the map it is given *)
(* and cannot tell -- which is what lets [MemCommuteLemmas]' transformer   *)
(* results, stated about [eval_sym_state ps f], apply at the network      *)
(* level, where the state arrives already injected.                       *)
(* ==================================================================== *)

(* [program_state_mapper] is [Global Opaque], so its defining equation has to
   be named rather than unfolded. *)
Lemma program_state_mapper_eq_local : forall (T1 T2 : Type) (fc fh fs : T1 -> T2) s,
  program_state_mapper fc fh fs s =
  {| t_ctrl_map := PMap.map fc (t_ctrl_map s);
     t_header_map := PMap.map fh (t_header_map s);
     t_state_map := PMap.map fs (t_state_map s) |}.
Proof. reflexivity. Qed.

Lemma inject_headers_commute : forall hm ts f,
  inject_headers (PMap.map (fun e => eval_smt_arith e f) hm) (eval_sym_state ts f)
  = eval_sym_state (inject_headers hm ts) f.
Proof.
  intros hm ts f. unfold eval_sym_state. cbv zeta.
  rewrite !program_state_mapper_eq_local. unfold inject_headers.
  cbn [t_ctrl_map t_header_map t_state_map]. reflexivity.
Qed.

(* ==================================================================== *)
(* 7. WHEN POINTWISE AGREEMENT IS ENOUGH FOR A [PMap] EQUALITY.          *)
(*                                                                       *)
(* [gps_agree] keeps STRUCTURAL equality on [sh_hdr_map] and             *)
(* [mod_states], and the induction has to deliver it from results that   *)
(* are per-key ([MemCommuteLemmas]' transformer lemmas are stated one    *)
(* key at a time, and only for keys in the state's domain).  Pointwise   *)
(* [!!] agreement is NOT enough on its own -- that is the whole reason   *)
(* the memory maps had to be weakened -- because [!!] collapses an       *)
(* absent key onto the default and so cannot see the key set.            *)
(*                                                                       *)
(* Add the key set and the default and it IS enough.  Both are available *)
(* here, so the header and module-state maps do NOT have to be weakened  *)
(* the way the memory maps were -- which is why [gps_agree] keeps        *)
(* structural equality on them, and why                                   *)
(* [modnet_equivalence_checker_sound] did not have to be restated.       *)
(* (TODO 1.1 item 5 records this as settled, and why the alternative --  *)
(* an extensional [ts_agree] -- would have cost more.)                   *)
(* ==================================================================== *)

Lemma pmap_ext : forall (T : Type) (m1 m2 : PMap.t T),
  fst m1 = fst m2 ->
  (forall k, m1 ?? k = None <-> m2 ?? k = None) ->
  (forall k, m1 !! k = m2 !! k) ->
  m1 = m2.
Proof.
  intros T [d1 t1] [d2 t2] Hd Hdom Hval. cbn [fst] in Hd. subst d2. f_equal.
  apply PTree.extensionality. intros i.
  specialize (Hdom i). specialize (Hval i).
  unfold PMap.get in Hval. cbn [snd] in *.
  destruct (t1 ! i) as [a |] eqn:E1; destruct (t2 ! i) as [b |] eqn:E2.
  - congruence.
  - exfalso. destruct Hdom as [_ H2]. specialize (H2 eq_refl). congruence.
  - exfalso. destruct Hdom as [H1 _]. specialize (H1 eq_refl). congruence.
  - reflexivity.
Qed.

(* The symbolic writer cannot introduce a key and cannot move the default:
   [update_all_varlike] is [new_pmap_from_old] in all three [CrVarLike]
   instances, which keeps [fst] and rebuilds the tree with [PTree.map].  So a
   merge's domain is the domain it started with.  Not derivable from the
   [CrVarLike] class -- [update_all_varlike] is an abstract field with no body
   -- but all three instances are [new_pmap_from_old], so one lemma about that
   covers them. *)
(* [new_pmap_from_old] is [Global Opaque] too. *)
Lemma new_pmap_from_old_eq : forall (T : Type) (m : PMap.t T) g,
  new_pmap_from_old m g = (fst m, PTree.map (fun x _ => g x) (snd m)).
Proof. reflexivity. Qed.

Lemma new_pmap_from_old_default : forall (T : Type) (m : PMap.t T) g,
  fst (new_pmap_from_old m g) = fst m.
Proof. intros T m g. rewrite new_pmap_from_old_eq. reflexivity. Qed.

Lemma new_pmap_from_old_dom : forall (T : Type) (m : PMap.t T) g k,
  (new_pmap_from_old m g) ?? k = None <-> m ?? k = None.
Proof.
  intros T m g k. rewrite new_pmap_from_old_eq. cbn [snd].
  rewrite PTree.gmap. destruct (PTree.get k (snd m)); cbn [option_map]; split;
    intro H; congruence.
Qed.

(* The concrete writer does not move the default either, and it introduces a
   key only when it writes one that was absent -- which the domain invariant
   ([every key a module writes is already in its maps]) rules out. *)
Lemma pmap_set_default : forall (T : Type) (m : PMap.t T) k v,
  fst (PMap.set k v m) = fst m.
Proof. reflexivity. Qed.

Lemma pmap_set_dom_present : forall (T : Type) (m : PMap.t T) k v j,
  m ?? k <> None ->
  ((PMap.set k v m) ?? j = None <-> m ?? j = None).
Proof.
  intros T m k v j Hk. unfold PMap.set. cbn [snd].
  rewrite PTree.gsspec. destruct (Coqlib.peq j k) as [-> |].
  - split; intro H; [discriminate | congruence].
  - split; intro H; exact H.
Qed.

(* And [PMap.map], the shape every field of a concretized state has. *)
Lemma pmap_map_dom : forall (A B : Type) (g : A -> B) (m : PMap.t A) k,
  (PMap.map g m) ?? k = None <-> m ?? k = None.
Proof.
  intros A B g m k. unfold PMap.map. cbn [snd].
  rewrite PTree.gmap1. destruct (PTree.get k (snd m)); cbn [option_map]; split;
    intro H; congruence.
Qed.

Lemma pmap_map_default : forall (A B : Type) (g : A -> B) (m : PMap.t A),
  fst (PMap.map g m) = g (fst m).
Proof. reflexivity. Qed.

(* ==================================================================== *)
(* 8. THE MEMORY-SAFETY CHECK SURVIVES POINTWISE EXTENT AGREEMENT.       *)
(*                                                                       *)
(* [MemCommuteLemmas] §6 observes that the concrete side is blind to the *)
(* difference between "equal maps" and "maps equal at every key",        *)
(* because memory is only ever touched through [!!] and [PMap.set].      *)
(* [mem_extents_in_bounds_concrete] is the one exception: it folds over  *)
(* [pmap_keys], the one thing pointwise agreement does not fix.          *)
(*                                                                       *)
(* It survives anyway, and the argument is specific rather than          *)
(* structural: a key present in one map and absent from the other reads  *)
(* the absent map's DEFAULT, the default is [mk_int u64 0], and          *)
(* [negb (ltb bound 0)] is [true] -- an untouched region cannot overrun. *)
(* So the surplus keys contribute [true] and cannot change the verdict.  *)
(* ==================================================================== *)

(* Local copies of two [Integers] facts, so this file does not depend on
   [SmtCompile] for them. *)
Lemma ltu64_spec_local : forall (a b : uint64), Integers.ltu a b = (unsigned a <? unsigned b).
Proof.
  intros a b. unfold Integers.ltu.
  destruct (Rocqlib.zlt (unsigned a) (unsigned b)) as [H | H].
  - symmetry. apply Z.ltb_lt. exact H.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma unsigned_range_local : forall (a : uint64), 0 <= unsigned a < 2 ^ 64.
Proof.
  intros a. pose proof (unsigned_range a) as H.
  assert (Hm : @modulus 64%positive = 2 ^ 64) by (vm_compute; reflexivity).
  rewrite Hm in H. exact H.
Qed.

Lemma unsigned_mask_W64_local : forall z, 0 <= z < 2 ^ 64 -> unsigned (mask_width W64 z) = z.
Proof.
  intros z Hz. rewrite mask_width_W64_small by exact Hz.
  apply unsigned_repr. unfold max_unsigned.
  assert (Hm : @modulus 64%positive = 2 ^ 64) by (vm_compute; reflexivity).
  rewrite Hm. lia.
Qed.

Lemma pmap_not_in_keys_default : forall (T : Type) (m : PMap.t T) k,
  ~ In k (pmap_keys m) -> m !! k = fst m.
Proof.
  intros T m k Hnin. unfold PMap.get.
  destruct (PTree.get k (snd m)) as [v |] eqn:E; [| reflexivity].
  exfalso. apply Hnin. unfold pmap_keys.
  apply (List.in_map fst (PTree.elements (snd m)) (k, v)).
  apply PTree.elements_correct. exact E.
Qed.

Lemma forallb_all_iff : forall (P : positive -> bool) l,
  (forall k, ~ In k l -> P k = true) ->
  (List.forallb P l = true <-> forall k, P k = true).
Proof.
  intros P l H. split.
  - intros Hf k. destruct (in_dec Coqlib.peq k l) as [Hin | Hnin].
    + rewrite List.forallb_forall in Hf. apply Hf, Hin.
    + apply H, Hnin.
  - intros Hall. apply List.forallb_forall. intros x _. apply Hall.
Qed.

Lemma forallb_ext_default : forall (P : positive -> bool) l1 l2,
  (forall k, ~ In k l1 -> P k = true) ->
  (forall k, ~ In k l2 -> P k = true) ->
  List.forallb P l1 = List.forallb P l2.
Proof.
  intros P l1 l2 H1 H2.
  destruct (List.forallb P l1) eqn:E1; destruct (List.forallb P l2) eqn:E2;
    try reflexivity.
  - assert (Hall : forall k, P k = true)
      by (apply (proj1 (forallb_all_iff P l1 H1)); exact E1).
    assert (H : List.forallb P l2 = true)
      by (apply (proj2 (forallb_all_iff P l2 H2)); exact Hall).
    rewrite H in E2. discriminate.
  - assert (Hall : forall k, P k = true)
      by (apply (proj1 (forallb_all_iff P l2 H2)); exact E2).
    assert (H : List.forallb P l1 = true)
      by (apply (proj2 (forallb_all_iff P l1 H1)); exact Hall).
    rewrite H in E1. discriminate.
Qed.

(* An untouched region -- extent [mk_int u64 0] -- is in bounds whatever its
   declared length is, because nothing is [CrVal.ltb] below zero. *)
Lemma ltb_zero_false : forall x, CrVal.ltb x (mk_int u64 0) = false.
Proof.
  intros [a ty | | ]; unfold CrVal.ltb, mk_int, u64; cbn [it_width];
    try reflexivity.
  destruct (crinttype_eqb ty (mkCrIntType W64)); cbn [andb]; [| reflexivity].
  rewrite ltu64_spec_local.
  rewrite (unsigned_mask_W64_local 0) by (split; [lia | vm_compute; reflexivity]).
  pose proof (unsigned_range_local a). apply Z.ltb_ge. lia.
Qed.

Lemma extent_zero_in_bounds : forall n,
  negb (CrVal.ltb (mk_int u64 (Z.of_nat n)) (mk_int u64 0)) = true.
Proof. intro n. rewrite ltb_zero_false. reflexivity. Qed.

Lemma forallb_ext_fn : forall (P Q : positive -> bool) l,
  (forall k, P k = Q k) -> List.forallb P l = List.forallb Q l.
Proof.
  intros P Q l H. induction l as [| a r IH]; cbn [List.forallb];
    [reflexivity | rewrite H, IH; reflexivity].
Qed.

Theorem mem_extents_in_bounds_concrete_cong : forall rs e1 e2,
  fst e1 = mk_int u64 0 ->
  fst e2 = mk_int u64 0 ->
  (forall k, e1 !! k = e2 !! k) ->
  mem_extents_in_bounds_concrete rs e1 = mem_extents_in_bounds_concrete rs e2.
Proof.
  intros rs e1 e2 Hd1 Hd2 Hk.
  unfold mem_extents_in_bounds_concrete. cbv zeta.
  set (P1 := fun k => negb (CrVal.ltb (mk_int u64 (Z.of_nat ((region_len_map rs) !! k))) (e1 !! k))).
  set (P2 := fun k => negb (CrVal.ltb (mk_int u64 (Z.of_nat ((region_len_map rs) !! k))) (e2 !! k))).
  assert (HP : forall k, P1 k = P2 k) by (intro k; unfold P1, P2; rewrite Hk; reflexivity).
  transitivity (List.forallb P1 (pmap_keys e2)).
  - apply forallb_ext_default; intros k Hnin; unfold P1.
    + rewrite (pmap_not_in_keys_default _ e1 k Hnin), Hd1. apply extent_zero_in_bounds.
    + rewrite Hk, (pmap_not_in_keys_default _ e2 k Hnin), Hd2.
      apply extent_zero_in_bounds.
  - apply forallb_ext_fn. exact HP.
Qed.

(* ==================================================================== *)
(* 9. THE PROGRAM WRAPPER.                                               *)
(*                                                                       *)
(* Both [eval_general_program_*] do the same three things around the     *)
(* network recursion: look up the start module's state, run the network, *)
(* and conjoin the memory-safety check into the final flag.  This is     *)
(* that glue.                                                            *)
(*                                                                       *)
(* It takes the network-level outcome as HYPOTHESES rather than naming   *)
(* the induction, which keeps the two separable: §21 supplies them, and  *)
(* the wrapper's own reasoning -- the start-module lookups agreeing, and *)
(* the memory-safety check surviving the pointwise weakening -- can be   *)
(* read without the induction.                                           *)
(* ==================================================================== *)

(* Agreement between two concrete network states.

   Structural equality on every field EXCEPT the two memory maps, which are
   compared pointwise.  That exception is not a convenience: an equality of
   [GeneralConcreteState] records is FALSE here, for a [PMap] representation
   reason rather than a semantic one.

   [sh_mem_extent] starts life as [PMap.init] -- an empty tree -- and every
   access adds a key.  A transformer whose first rule touches region A and
   whose second touches region B leaves the CONCRETE extent map with a binding
   for whichever rule ran, and the SYMBOLIC one with bindings for both, since
   [eval_transformer_smt_mem] folds over the keys of every branch's context.
   [PMap.map] preserves trees, so the two records differ even though [!!]
   agrees at every key: the surplus bindings all hold the map's own default.

   Nothing downstream notices, which is why this is the right weakening rather
   than a lost conclusion.  [modnet_equivalence_checker_sound] never compares
   maps -- it compares [ld_arr ((sh_mem ...) !! ...)], [(sh_mem_extent ...) !! ...],
   the two tapes and the flag, every one of them extensional.

   [sh_mem] is weakened alongside it for uniformity.  Only the extent map
   demonstrably needs it: a store to an UNDECLARED region would add a key on
   the merged path alone, but touching an undeclared region overruns it (its
   [region_len_map] bound is 0), so such a run is rejected and the second half
   of the bridge does not apply to it.  Relying on that would smuggle the
   declared-regions argument into the bridge; comparing pointwise does not.

   The remaining fields are structurally equal, and for [sh_hdr_map] and
   [mod_states] that is not an accident either -- it is the seeding.  A parser's
   merged header map is a union over branches, so a header written on only one
   branch would be a key on the symbolic side alone; [init_general_symbolic_state]
   seeds the map with [collect_write_headers], which already holds every one of
   them, so both sides carry the same key set. *)
Definition gps_agree (c1 c2 : GeneralConcreteState) : Prop :=
  sh_hdr_map    c1 = sh_hdr_map    c2 /\
  sh_read_tape  c1 = sh_read_tape  c2 /\
  sh_bits_read  c1 = sh_bits_read  c2 /\
  sh_write_tape c1 = sh_write_tape c2 /\
  (forall k, (sh_mem        c1) !! k = (sh_mem        c2) !! k) /\
  (forall k, (sh_mem_extent c1) !! k = (sh_mem_extent c2) !! k) /\
  mod_states    c1 = mod_states    c2 /\
  gps_valid     c1 = gps_valid     c2.


Lemma gps_agree_set_valid : forall c1 c2 b1 b2,
  gps_agree c1 c2 -> b1 = b2 ->
  gps_agree (set_gps_valid c1 b1) (set_gps_valid c2 b2).
Proof.
  intros c1 c2 b1 b2 [H1 [H2 [H3 [H4 [H5 [H6 [H7 _]]]]]]] Hb.
  unfold gps_agree, set_gps_valid.
  cbn [sh_hdr_map sh_read_tape sh_bits_read sh_write_tape sh_mem sh_mem_extent
       mod_states gps_valid].
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 Hb))))))).
Qed.

Lemma concretize_set_valid : forall sgs v f,
  concretize_sym_modnet_state (set_gps_valid sgs v) f
  = set_gps_valid (concretize_sym_modnet_state sgs f) (eval_smt_bool (cvv v) f).
Proof. reflexivity. Qed.

(* The reduction.  Note which hypotheses are about the DEFAULT of each extent
   map: the memory-safety check folds over [pmap_keys], so it is the one place
   the pointwise weakening in [gps_agree] does not carry, and §8 is what
   bridges it -- given that an untouched region reads extent zero on both
   sides. *)
Theorem program_commute_from_network : forall p s f s_f sgs_f cgs_f,
  eval_network_from_symbolic (get_network_from_general p)
    (start_module (get_network_from_general p))
    (sh_hdr_map s) (sh_read_tape s) s
    (List.length (net_modules (get_network_from_general p))) = Some sgs_f ->
  eval_network_from_concrete (get_network_from_general p)
    (start_module (get_network_from_general p))
    (sh_hdr_map (concretize_sym_modnet_state s f))
    (sh_read_tape (concretize_sym_modnet_state s f))
    (concretize_sym_modnet_state s f)
    (List.length (net_modules (get_network_from_general p))) = Some cgs_f ->
  gps_valid cgs_f = eval_smt_bool (cvv (gps_valid sgs_f)) f ->
  fst (sh_mem_extent cgs_f) = mk_int u64 0 ->
  eval_smt_arith (fst (sh_mem_extent sgs_f)) f = mk_int u64 0 ->
  (gps_valid cgs_f = true -> gps_agree cgs_f (concretize_sym_modnet_state sgs_f f)) ->
  eval_general_program_symbolic p s = Some s_f ->
  exists c_f,
    eval_general_program_concrete p (concretize_sym_modnet_state s f) = Some c_f /\
    gps_valid c_f = gps_valid (concretize_sym_modnet_state s_f f) /\
    (gps_valid c_f = true -> gps_agree c_f (concretize_sym_modnet_state s_f f)).
Proof.
  intros p s f s_f sgs_f cgs_f Hsym Hconc Hflag Hcd Hsd Hagree Hprog.
  unfold eval_general_program_symbolic in Hprog. cbv zeta in Hprog.
  destruct ((mod_states s) ?? (unwrap (start_module (get_network_from_general p))))
    as [st |] eqn:Hms; [| discriminate].
  rewrite Hsym in Hprog. injection Hprog as Hprog. subst s_f.
  (* the concrete start lookup succeeds because [PMap.map] preserves bindings *)
  unfold eval_general_program_concrete. cbv zeta.
  destruct ((mod_states (concretize_sym_modnet_state s f))
              ?? (unwrap (start_module (get_network_from_general p)))) as [st' |] eqn:Hms2.
  2: { exfalso. cbn [mod_states concretize_sym_modnet_state] in Hms2.
       rewrite (proj1 (pmap_map_dom _ _ _ (mod_states s) _) Hms2) in Hms.
       discriminate. }
  rewrite Hconc.
  eexists. split; [reflexivity | ].
  (* the two final flags *)
  assert (Hchk : gps_valid cgs_f = true ->
                 mem_extents_in_bounds_concrete (get_mem_regions_from_general p)
                   (sh_mem_extent cgs_f)
                 = eval_smt_bool (mem_extents_in_bounds_smt
                     (get_mem_regions_from_general p) (sh_mem_extent sgs_f)) f).
  { intro Hv. rewrite <- mem_extents_in_bounds_commute.
    apply mem_extents_in_bounds_concrete_cong;
      [ exact Hcd
      | rewrite pmap_map_default; exact Hsd
      | intro k; rewrite PMap.gmap;
        destruct (Hagree Hv) as [_ [_ [_ [_ [_ [He _]]]]]]; rewrite He;
        cbn [sh_mem_extent concretize_sym_modnet_state]; rewrite PMap.gmap;
        reflexivity ]. }
  assert (Hflag' : gps_valid (set_gps_valid cgs_f
                     (gps_valid cgs_f && mem_extents_in_bounds_concrete
                        (get_mem_regions_from_general p) (sh_mem_extent cgs_f)))
                   = gps_valid (concretize_sym_modnet_state
                       (set_gps_valid sgs_f
                          {| cvc := cvc (gps_valid sgs_f);
                             cvv := SmtBoolAnd (cvv (gps_valid sgs_f))
                                      (mem_extents_in_bounds_smt
                                         (get_mem_regions_from_general p)
                                         (sh_mem_extent sgs_f)) |}) f)).
  { rewrite concretize_set_valid.
    cbn [gps_valid set_gps_valid cvv eval_smt_bool].
    rewrite Hflag.
    destruct (eval_smt_bool (cvv (gps_valid sgs_f)) f) eqn:Hv; cbn [andb].
    - apply Hchk. rewrite Hflag. first [ reflexivity | exact Hv ].
    - reflexivity. }
  split; [exact Hflag' |].
  intro Hvf.
  assert (Hv : gps_valid cgs_f = true).
  { cbn [gps_valid set_gps_valid] in Hvf.
    destruct (gps_valid cgs_f); [reflexivity | cbn [andb] in Hvf; discriminate]. }
  rewrite concretize_set_valid.
  apply gps_agree_set_valid; [ exact (Hagree Hv) |].
  rewrite concretize_set_valid in Hflag'.
  cbn [gps_valid set_gps_valid] in Hflag'. exact Hflag'.
Qed.

(* ==================================================================== *)
(* 10. THE CONCRETE TRANSFORMER DOES NOT CHANGE A MAP'S SHAPE.           *)
(*                                                                       *)
(* §7 reduces a transformer's module-state equality to three things:     *)
(* defaults, domains, and per-key agreement.  Per-key is                 *)
(* [MemCommuteLemmas.transformer_commute_hdr]/[_sv].  This section is    *)
(* the other two.                                                        *)
(*                                                                       *)
(* Defaults are free: the concrete side writes only with [PMap.set],     *)
(* which never moves [fst].  Domains are not: [PMap.set] ADDS a key,     *)
(* while the symbolic [update_all_varlike] rebuilds from the keys        *)
(* already present and so cannot.  They stay equal exactly when every    *)
(* target a transformer writes is already in its maps -- which is what   *)
(* the header-map seeding and [force_keys] are for, and which has to be  *)
(* threaded in as a hypothesis because nothing in the evaluator knows    *)
(* it.                                                                   *)
(* ==================================================================== *)

Definition pmap_shape {T : Type} (m1 m2 : PMap.t T) : Prop :=
  fst m1 = fst m2 /\ (forall k, m1 ?? k = None <-> m2 ?? k = None).

Definition ts_shape {T : Type} (a b : TransformerState T) : Prop :=
  pmap_shape (t_ctrl_map a) (t_ctrl_map b)
  /\ pmap_shape (t_header_map a) (t_header_map b)
  /\ pmap_shape (t_state_map a) (t_state_map b).

Lemma pmap_shape_of_eq : forall (T : Type) (m1 m2 : PMap.t T),
  m1 = m2 -> pmap_shape m1 m2.
Proof.
  intros T m1 m2 ->. split; [reflexivity | intro k; split; intro H; exact H].
Qed.

Lemma pmap_shape_refl : forall (T : Type) (m : PMap.t T), pmap_shape m m.
Proof. intros T m. split; [reflexivity | intro k; split; intro H; exact H]. Qed.

Lemma pmap_shape_trans : forall (T : Type) (a b c : PMap.t T),
  pmap_shape a b -> pmap_shape b c -> pmap_shape a c.
Proof.
  intros T a b c [Hd1 Hk1] [Hd2 Hk2]. split; [congruence |].
  intro k. split; intro H; [apply Hk2, Hk1, H | apply Hk1, Hk2, H].
Qed.

Lemma ts_shape_refl : forall (T : Type) (a : TransformerState T), ts_shape a a.
Proof. intros T a. split; [| split]; apply pmap_shape_refl. Qed.

Lemma ts_shape_trans : forall (T : Type) (a b c : TransformerState T),
  ts_shape a b -> ts_shape b c -> ts_shape a c.
Proof.
  intros T a b c [H1 [H2 H3]] [H4 [H5 H6]].
  split; [| split]; eapply pmap_shape_trans; eassumption.
Qed.

Lemma pmap_shape_set : forall (T : Type) (m : PMap.t T) k v,
  m ?? k <> None -> pmap_shape (PMap.set k v m) m.
Proof.
  intros T m k v Hk. split; [apply pmap_set_default |].
  intro j. apply pmap_set_dom_present. exact Hk.
Qed.

(* The one place a target is written, per varlike kind. *)
Lemma update_varlike_header_shape : forall (T : Type) (ps : TransformerState T) (h : Header) (v : T),
  (t_header_map ps) ?? (unwrap h) <> None ->
  ts_shape (update_varlike ps h v) ps.
Proof.
  intros T ps h v Hh.
  cbn [update_varlike CrVarLike_Header t_ctrl_map t_header_map t_state_map].
  split; [| split].
  - apply pmap_shape_refl.
  - apply pmap_shape_set. exact Hh.
  - apply pmap_shape_refl.
Qed.

Lemma update_varlike_state_shape : forall (T : Type) (ps : TransformerState T) (s : State) (v : T),
  (t_state_map ps) ?? (unwrap s) <> None ->
  ts_shape (update_varlike ps s v) ps.
Proof.
  intros T ps s v Hs.
  cbn [update_varlike CrVarLike_State t_ctrl_map t_header_map t_state_map].
  split; [| split].
  - apply pmap_shape_refl.
  - apply pmap_shape_refl.
  - apply pmap_shape_set. exact Hs.
Qed.

(* Every target an op writes, as a condition on the state it writes into.
   [StoreOp] writes memory, not a varlike, so it has nothing to ask for. *)
Definition op_dom_ok {T : Type} (op : HdrOp) (ps : TransformerState T) : Prop :=
  match op with
  | StatefulOp _ _ _ _ tgt     => (t_state_map ps)  ?? (unwrap tgt) <> None
  | StatelessOp _ _ _ _ tgt    => (t_header_map ps) ?? (unwrap tgt) <> None
  | CastStateOp _ _ _ tgt      => (t_state_map ps)  ?? (unwrap tgt) <> None
  | CastHeaderOp _ _ _ tgt     => (t_header_map ps) ?? (unwrap tgt) <> None
  | LoadOp _ _ _ tgt           => (t_header_map ps) ?? (unwrap tgt) <> None
  | StatefulLoadOp _ _ _ tgt   => (t_state_map ps)  ?? (unwrap tgt) <> None
  | StoreOp _ _ _ _            => True
  end.

(* The condition depends on the state only through its shape, so it survives
   the ops that ran before -- which is what makes the list induction go
   through with a hypothesis stated against the INITIAL state. *)
Lemma op_dom_ok_shape : forall (T : Type) op (ps1 ps2 : TransformerState T),
  ts_shape ps1 ps2 -> op_dom_ok op ps2 -> op_dom_ok op ps1.
Proof.
  intros T op ps1 ps2 [_ [[_ Hh] [_ Hs]]] H.
  destruct op; cbn [op_dom_ok] in *; try exact I;
    intro Hc; apply H; solve [ apply Hh; exact Hc | apply Hs; exact Hc ].
Qed.

Lemma op_shape : forall op mc ps,
  op_dom_ok op ps ->
  ts_shape (snd (eval_hdr_op_assign_concrete_mem op mc ps)) ps.
Proof.
  intros op mc ps H.
  destruct op; cbn [eval_hdr_op_assign_concrete_mem op_dom_ok snd] in *;
    solve [ apply ts_shape_refl
          | apply update_varlike_state_shape; exact H
          | apply update_varlike_header_shape; exact H ].
Qed.

Lemma op_list_shape : forall hol mc ps,
  List.Forall (fun op => op_dom_ok op ps) hol ->
  ts_shape (snd (eval_hdr_op_list_concrete_mem hol mc ps)) ps.
Proof.
  induction hol as [| op rest IH]; intros mc ps H; [apply ts_shape_refl |].
  rewrite eval_hdr_op_list_concrete_mem_cons.
  inversion H as [| o r Hop Hrest Heq]; subst.
  assert (Hs1 : ts_shape (snd (eval_hdr_op_assign_concrete_mem op mc ps)) ps)
    by (apply op_shape; exact Hop).
  eapply ts_shape_trans; [ apply IH | exact Hs1 ].
  eapply List.Forall_impl; [| exact Hrest]. intros o Ho.
  eapply op_dom_ok_shape; [ exact Hs1 | exact Ho ].
Qed.

Definition rule_ops (rule : MatchActionRule) : list HdrOp :=
  match rule with
  | Seq (SeqCtr _ action) => action
  | Par (ParCtr _ action) => proj1_sig action
  end.

Definition rule_dom_ok {T : Type} (rule : MatchActionRule) (ps : TransformerState T) : Prop :=
  List.Forall (fun op => op_dom_ok op ps) (rule_ops rule).

Definition transformer_dom_ok {T : Type} (t : Transformer) (ps : TransformerState T) : Prop :=
  List.Forall (fun rule => rule_dom_ok rule ps) t.

Lemma rule_shape : forall rule mc ps,
  rule_dom_ok rule ps ->
  ts_shape (snd (eval_match_action_rule_concrete_mem rule mc ps)) ps.
Proof.
  intros [[mp action] | [mp action]] mc ps H;
    cbn [eval_match_action_rule_concrete_mem eval_seq_rule_concrete_mem
         eval_par_rule_concrete_mem rule_dom_ok rule_ops] in *;
    destruct (eval_match_concrete mp ps);
    solve [ apply op_list_shape; exact H | cbn [snd]; apply ts_shape_refl ].
Qed.

Theorem transformer_shape : forall t mc ps,
  transformer_dom_ok t ps ->
  ts_shape (snd (eval_transformer_concrete_mem t mc ps)) ps.
Proof.
  intros t mc ps H.
  unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (find_first_match (List.combine (get_match_results t ps) t)) as [rule |] eqn:Hf.
  - apply rule_shape.
    unfold transformer_dom_ok in H. rewrite List.Forall_forall in H. apply H.
    apply (find_first_match_in_transformer t ps rule). symmetry. exact Hf.
  - cbn [snd]. apply ts_shape_refl.
Qed.

(* ==================================================================== *)
(* 11. A TRANSFORMER'S MODULE STATE COMMUTES.                            *)
(*                                                                       *)
(* The payoff.  [pmap_ext] wants defaults, domains and per-key: §10 gives *)
(* the first two on the concrete side, [new_pmap_from_old] gives them on  *)
(* the symbolic side, and [MemCommuteLemmas]' per-key results give the    *)
(* third -- for keys IN the domain, which is exactly where [pmap_ext]     *)
(* needs them, since outside it both sides read a default and the         *)
(* defaults agree.                                                       *)
(* ==================================================================== *)

Lemma ts_eq : forall (T : Type) (a b : TransformerState T),
  t_ctrl_map a = t_ctrl_map b ->
  t_header_map a = t_header_map b ->
  t_state_map a = t_state_map b ->
  a = b.
Proof. intros T [c1 h1 s1] [c2 h2 s2]; cbn; intros; subst; reflexivity. Qed.

Lemma pmap_get_default : forall (T : Type) (m : PMap.t T) k,
  m ?? k = None -> m !! k = fst m.
Proof. intros T m k H. unfold PMap.get. rewrite H. reflexivity. Qed.

Lemma new_pmap_from_old_shape : forall (T : Type) (m : PMap.t T) g,
  pmap_shape (new_pmap_from_old m g) m.
Proof.
  intros T m g. split;
    [ apply new_pmap_from_old_default | intro k; apply new_pmap_from_old_dom ].
Qed.

(* The symbolic transformer rebuilds both maps with [update_all_varlike], so
   neither its defaults nor its domains move. *)
Lemma smt_transformer_hdr_shape : forall t mc ps,
  pmap_shape (t_header_map (snd (eval_transformer_smt_mem t mc ps))) (t_header_map ps).
Proof.
  intros t mc ps. unfold eval_transformer_smt_mem. cbv zeta. cbn [snd].
  cbn [update_all_varlike CrVarLike_Header CrVarLike_State
       t_ctrl_map t_header_map t_state_map].
  apply new_pmap_from_old_shape.
Qed.

Lemma smt_transformer_sv_shape : forall t mc ps,
  pmap_shape (t_state_map (snd (eval_transformer_smt_mem t mc ps))) (t_state_map ps).
Proof.
  intros t mc ps. unfold eval_transformer_smt_mem. cbv zeta. cbn [snd].
  cbn [update_all_varlike CrVarLike_Header CrVarLike_State
       t_ctrl_map t_header_map t_state_map].
  apply new_pmap_from_old_shape.
Qed.

Lemma eval_sym_state_hdr : forall ps f,
  t_header_map (eval_sym_state ps f)
  = PMap.map (fun e => eval_smt_arith e f) (t_header_map ps).
Proof.
  intros ps f. unfold eval_sym_state. cbv zeta.
  rewrite program_state_mapper_eq_local. reflexivity.
Qed.

Lemma eval_sym_state_sv : forall ps f,
  t_state_map (eval_sym_state ps f)
  = PMap.map (fun e => eval_smt_arith e f) (t_state_map ps).
Proof.
  intros ps f. unfold eval_sym_state. cbv zeta.
  rewrite program_state_mapper_eq_local. reflexivity.
Qed.

Lemma pmap_map_shape_iff : forall (A B : Type) (g : A -> B) (m1 m2 : PMap.t A),
  (forall k, m1 ?? k = None <-> m2 ?? k = None) ->
  (forall k, (PMap.map g m1) ?? k = None <-> (PMap.map g m2) ?? k = None).
Proof.
  intros A B g m1 m2 H k.
  eapply iff_trans; [ apply pmap_map_dom |].
  eapply iff_trans; [ apply H |].
  symmetry. apply pmap_map_dom.
Qed.

Theorem transformer_state_commute : forall t mc ps f,
  transformer_dom_ok t (eval_sym_state ps f) ->
  snd (eval_transformer_concrete_mem t (concretize_mem_ctx mc f) (eval_sym_state ps f))
  = eval_sym_state (snd (eval_transformer_smt_mem t mc ps)) f.
Proof.
  intros t mc ps f Hdom.
  pose proof (transformer_shape t (concretize_mem_ctx mc f) (eval_sym_state ps f) Hdom)
    as [_ [[Hhd Hhk] [Hsd Hsk]]].
  pose proof (smt_transformer_hdr_shape t mc ps) as [Hshd Hshk].
  pose proof (smt_transformer_sv_shape t mc ps) as [Hssd Hssk].
  assert (Hhk' : forall k,
    (t_header_map (snd (eval_transformer_concrete_mem t (concretize_mem_ctx mc f)
                          (eval_sym_state ps f)))) ?? k = None
    <-> (PMap.map (fun e => eval_smt_arith e f) (t_header_map ps)) ?? k = None)
    by (intro k; rewrite <- eval_sym_state_hdr; apply Hhk).
  assert (Hsk' : forall k,
    (t_state_map (snd (eval_transformer_concrete_mem t (concretize_mem_ctx mc f)
                         (eval_sym_state ps f)))) ?? k = None
    <-> (PMap.map (fun e => eval_smt_arith e f) (t_state_map ps)) ?? k = None)
    by (intro k; rewrite <- eval_sym_state_sv; apply Hsk).
  apply ts_eq.
  - apply transformer_commute_ctrl.
  - (* ---- headers ---- *)
    rewrite eval_sym_state_hdr.
    assert (Hdef : fst (t_header_map (snd (eval_transformer_concrete_mem t
                          (concretize_mem_ctx mc f) (eval_sym_state ps f))))
                   = fst (PMap.map (fun e => eval_smt_arith e f)
                            (t_header_map (snd (eval_transformer_smt_mem t mc ps))))).
    { rewrite Hhd, eval_sym_state_hdr, !pmap_map_default;
      f_equal; symmetry; exact Hshd. }
    apply pmap_ext; [ exact Hdef | | ].
    + intro k. eapply iff_trans; [ apply Hhk' |].
      apply pmap_map_shape_iff. intro j. symmetry. apply Hshk.
    + intro k. destruct ((t_header_map ps) ?? k) eqn:Ek.
      * (* in the domain: the per-key commutation applies *)
        rewrite <- eval_sym_state_hdr.
        apply (transformer_commute_hdr t mc ps f (HeaderCtr k)).
        change (is_varlike_in_ps ps (HeaderCtr k)) with ((t_header_map ps) ?? k).
        rewrite Ek. discriminate.
      * (* outside it: both read a default, and the defaults agree *)
        rewrite (pmap_get_default _ _ k), (pmap_get_default _ _ k);
          [ exact Hdef
          | apply (proj2 (pmap_map_dom _ _ _ _ k)); apply Hshk; exact Ek
          | apply (proj2 (Hhk' k)); apply (proj2 (pmap_map_dom _ _ _ _ k)); exact Ek ].
  - (* ---- state variables ---- *)
    rewrite eval_sym_state_sv.
    assert (Hdef : fst (t_state_map (snd (eval_transformer_concrete_mem t
                          (concretize_mem_ctx mc f) (eval_sym_state ps f))))
                   = fst (PMap.map (fun e => eval_smt_arith e f)
                            (t_state_map (snd (eval_transformer_smt_mem t mc ps))))).
    { rewrite Hsd, eval_sym_state_sv, !pmap_map_default;
      f_equal; symmetry; exact Hssd. }
    apply pmap_ext; [ exact Hdef | | ].
    + intro k. eapply iff_trans; [ apply Hsk' |].
      apply pmap_map_shape_iff. intro j. symmetry. apply Hssk.
    + intro k. destruct ((t_state_map ps) ?? k) eqn:Ek.
      * rewrite <- eval_sym_state_sv.
        apply (transformer_commute_sv t mc ps f (StateCtr k)).
        change (is_varlike_in_ps ps (StateCtr k)) with ((t_state_map ps) ?? k).
        rewrite Ek. discriminate.
      * rewrite (pmap_get_default _ _ k), (pmap_get_default _ _ k);
          [ exact Hdef
          | apply (proj2 (pmap_map_dom _ _ _ _ k)); apply Hssk; exact Ek
          | apply (proj2 (Hsk' k)); apply (proj2 (pmap_map_dom _ _ _ _ k)); exact Ek ].
Qed.

(* ==================================================================== *)
(* 12. A PARSER DOES NOT CHANGE THE HEADER MAP'S SHAPE EITHER.           *)
(*                                                                       *)
(* Step 7 meets the same obligation step 6 did, in a different place.    *)
(* [gps_agree] wants [sh_hdr_map] structurally, and for a parser module  *)
(* that map is [pr_headers] of the run's result -- so the two sides have *)
(* to agree on defaults and domains, not only key by key.                *)
(*                                                                       *)
(* Both sides write a header with [PMap.set] at [get_key h], so neither  *)
(* moves a default; domains stay put exactly when every header the       *)
(* parser extracts is already a key, which is what the seeding gives.    *)
(* The symbolic side has one extra wrinkle the concrete side does not:   *)
(* [merge_header_maps] folds over the union of BOTH branches' keys, so   *)
(* its domain is a union -- which collapses back to the original only    *)
(* because both branches started from it.                                *)
(* ==================================================================== *)

Lemma in_pmap_keys_bound : forall (T : Type) (m : PMap.t T) k,
  In k (pmap_keys m) -> m ?? k <> None.
Proof.
  intros T m k H. unfold pmap_keys in H.
  apply List.in_map_iff in H as [[k' v] [Heq Hin]]. cbn [fst] in Heq. subst k'.
  intro Hc. rewrite (PTree.elements_complete _ _ _ Hin) in Hc. discriminate.
Qed.

Lemma pmap_fold_set_shape : forall (T : Type) (l : list positive) (F : positive -> T) (m : PMap.t T),
  (forall k, In k l -> m ?? k <> None) ->
  pmap_shape (List.fold_left (fun acc k => PMap.set k (F k) acc) l m) m.
Proof.
  intros T l. induction l as [| k r IH]; intros F m H; [apply pmap_shape_refl |].
  cbn [List.fold_left].
  assert (Hb : pmap_shape (PMap.set k (F k) m) m)
    by (apply pmap_shape_set; apply H; left; reflexivity).
  eapply pmap_shape_trans; [| exact Hb].
  apply IH. intros j Hj. destruct Hb as [_ Hd].
  intro Hc. apply (H j (or_intror Hj)). apply Hd. exact Hc.
Qed.

Lemma merge_header_maps_shape : forall cond m1 m2,
  (forall k, m2 ?? k = None <-> m1 ?? k = None) ->
  pmap_shape (merge_header_maps cond m1 m2) m1.
Proof.
  intros cond m1 m2 H. unfold merge_header_maps.
  apply pmap_fold_set_shape. intros k Hk.
  apply List.in_app_or in Hk as [Hk | Hk].
  - apply in_pmap_keys_bound. exact Hk.
  - intro Hc. apply (in_pmap_keys_bound _ m2 k Hk). apply H. exact Hc.
Qed.

(* Every header the parser can extract is already a key.  Stated over
   [parser_states], which is what [lookup_def] searches, so the recursion can
   discharge it at every state it reaches. *)
Definition parser_extracts_ok {T : Type} (p : Parser) (m : PMap.t T) : Prop :=
  List.Forall
    (fun d => match psd_action d with
              | Some (ExtractOpConstructor h _ _) => m ?? (get_key h) <> None
              | _ => True
              end)
    (parser_states p).

Lemma parser_extracts_ok_shape : forall (T : Type) (p : Parser) (m1 m2 : PMap.t T),
  pmap_shape m1 m2 -> parser_extracts_ok p m2 -> parser_extracts_ok p m1.
Proof.
  intros T p m1 m2 [_ Hd] H. unfold parser_extracts_ok in *.
  rewrite List.Forall_forall in *. intros d Hin. specialize (H d Hin).
  revert H. destruct (psd_action d) as [[w | h w of] |]; intro H; try exact I.
  intro Hc. apply H. apply Hd. exact Hc.
Qed.

Lemma lookup_def_in : forall p lbl d,
  lookup_def p lbl = Some d -> In d (parser_states p).
Proof.
  intros p lbl d H. unfold lookup_def in H.
  apply List.find_some in H as [H _]. exact H.
Qed.

Lemma apply_extract_concrete_shape : forall po ps ps',
  (match po with
   | ExtractOpConstructor h _ _ => (p_header_map ps) ?? (get_key h) <> None
   | _ => True
   end) ->
  apply_extract_concrete po ps = Some ps' ->
  pmap_shape (p_header_map ps') (p_header_map ps).
Proof.
  intros [w | h w of] ps ps' Hd H; cbn [apply_extract_concrete] in H.
  - destruct (Nat.leb (p_cursor ps + w) (List.length (p_packet ps))); [| discriminate].
    injection H as H; subst ps'. cbn [p_header_map]. apply pmap_shape_refl.
  - destruct (Nat.leb (p_cursor ps + w) (List.length (p_packet ps))); [| discriminate].
    injection H as H; subst ps'. cbn [p_header_map].
    apply pmap_shape_set. exact Hd.
Qed.

Theorem run_parser_concrete_shape : forall fuel p lbl ps r,
  parser_extracts_ok p (p_header_map ps) ->
  run_parser_concrete p lbl ps fuel = Some r ->
  pmap_shape (pr_headers r) (p_header_map ps).
Proof.
  induction fuel as [| fuel IH]; intros p lbl ps r Hok H; cbn [run_parser_concrete] in H;
    [discriminate |].
  destruct (lookup_def p lbl) as [d |] eqn:Hdef; [| discriminate].
  assert (Hact : match psd_action d with
                 | Some (ExtractOpConstructor h _ _) => (p_header_map ps) ?? (get_key h) <> None
                 | _ => True end).
  { unfold parser_extracts_ok in Hok. rewrite List.Forall_forall in Hok.
    apply Hok. apply (lookup_def_in p lbl d Hdef). }
  destruct (psd_action d) as [po |] eqn:Hpo.
  - destruct (apply_extract_concrete po ps) as [ps1 |] eqn:Hex.
    + assert (Hs1 : pmap_shape (p_header_map ps1) (p_header_map ps))
        by (eapply apply_extract_concrete_shape; [ exact Hact | exact Hex ]).
      destruct (eval_transition_concrete ps1 (psd_trans d)) as [[next | | ] |] eqn:Ht;
        try (injection H as H; subst r;
             cbn [parser_accept_concrete parser_reject_concrete pr_headers];
             exact Hs1).
      eapply pmap_shape_trans; [| exact Hs1 ].
      eapply IH; [| exact H ].
      eapply parser_extracts_ok_shape; [ exact Hs1 | exact Hok ].
    + injection H as H; subst r.
      cbn [parser_reject_concrete pr_headers]. apply pmap_shape_refl.
  - destruct (eval_transition_concrete ps (psd_trans d)) as [[next | | ] |] eqn:Ht;
      try (injection H as H; subst r;
           cbn [parser_accept_concrete parser_reject_concrete pr_headers];
           apply pmap_shape_refl).
    eapply IH; [ exact Hok | exact H ].
Qed.

Lemma apply_extract_symbolic_shape : forall po ps ps',
  (match po with
   | ExtractOpConstructor h _ _ => (p_header_map ps) ?? (get_key h) <> None
   | _ => True
   end) ->
  apply_extract_symbolic po ps = Some ps' ->
  pmap_shape (p_header_map ps') (p_header_map ps).
Proof.
  intros [w | h w of] ps ps' Hd H; cbn [apply_extract_symbolic] in H.
  - destruct (Nat.leb (p_cursor ps + w) (List.length (p_packet ps))); [| discriminate].
    injection H as H; subst ps'. cbn [p_header_map]. apply pmap_shape_refl.
  - destruct (Nat.leb (p_cursor ps + w) (List.length (p_packet ps))); [| discriminate].
    injection H as H; subst ps'. cbn [p_header_map].
    apply pmap_shape_set. exact Hd.
Qed.

Lemma run_target_shape : forall rec ps g tgt m,
  pmap_shape (p_header_map ps) m ->
  (forall next g', pmap_shape (pr_headers (rec next ps g')) m) ->
  pmap_shape (pr_headers (run_target_symbolic rec ps g tgt)) m.
Proof.
  intros rec ps g [next | | ] m Hps Hrec;
    cbn [run_target_symbolic pr_headers]; [ apply Hrec | exact Hps | exact Hps ].
Qed.

(* A [select] merges every case's result, and [merge_header_maps] takes the
   union of the two key sets -- which collapses back to the original exactly
   because both branches started from it. *)
Lemma resolve_select_shape : forall run_tgt ps cases default m,
  (forall tgt, pmap_shape (pr_headers (run_tgt tgt)) m) ->
  pmap_shape (pr_headers (resolve_select_symbolic run_tgt ps cases default)) m.
Proof.
  intros run_tgt ps cases. induction cases as [| c rest IH];
    intros default m H; cbn [resolve_select_symbolic]; [ apply H |].
  cbn [merge_results pr_headers].
  eapply pmap_shape_trans with (b := pr_headers (run_tgt (sc_target c))).
  - apply merge_header_maps_shape. intro k.
    destruct (IH default m H) as [_ Hr]. destruct (H (sc_target c)) as [_ Ht].
    eapply iff_trans; [ apply Hr |]. symmetry. apply Ht.
  - apply H.
Qed.

Theorem run_parser_symbolic_shape : forall fuel p lbl ps guard m,
  parser_extracts_ok p m ->
  pmap_shape (p_header_map ps) m ->
  pmap_shape (pr_headers (run_parser_symbolic p lbl ps guard fuel)) m.
Proof.
  induction fuel as [| fuel IH]; intros p lbl ps guard m Hok Hps;
    cbn [run_parser_symbolic]; cbv zeta.
  - cbn [pr_headers]. exact Hps.
  - destruct (lookup_def p lbl) as [d |] eqn:Hdef; [| cbn [pr_headers]; exact Hps].
    assert (Hact : match psd_action d with
                   | Some (ExtractOpConstructor h _ _) => m ?? (get_key h) <> None
                   | _ => True end).
    { unfold parser_extracts_ok in Hok. rewrite List.Forall_forall in Hok.
      apply Hok. apply (lookup_def_in p lbl d Hdef). }
    destruct (psd_action d) as [po |] eqn:Hpo.
    + destruct (apply_extract_symbolic po ps) as [ps1 |] eqn:Hex;
        [| cbn [pr_headers]; exact Hps].
      assert (Hs1 : pmap_shape (p_header_map ps1) m).
      { eapply pmap_shape_trans; [| exact Hps].
        eapply apply_extract_symbolic_shape; [| exact Hex ].
        destruct po as [w | h w of]; [exact I |].
        destruct Hps as [_ Hd]. intro Hc. apply Hact. apply Hd. exact Hc. }
      destruct (psd_trans d) as [tgt | cases default].
      * apply run_target_shape; [ exact Hs1 | intros next g'; apply IH; assumption ].
      * destruct (select_bits_available_symbolic ps1 cases);
          [| cbn [pr_headers]; exact Hs1 ].
        apply resolve_select_shape. intro tgt.
        apply run_target_shape; [ exact Hs1 | intros next g'; apply IH; assumption ].
    + destruct (psd_trans d) as [tgt | cases default].
      * apply run_target_shape; [ exact Hps | intros next g'; apply IH; assumption ].
      * destruct (select_bits_available_symbolic ps cases);
          [| cbn [pr_headers]; exact Hps ].
        apply resolve_select_shape. intro tgt.
        apply run_target_shape; [ exact Hps | intros next g'; apply IH; assumption ].
Qed.

Lemma parser_extracts_ok_dom : forall (T1 T2 : Type) (p : Parser)
    (m1 : PMap.t T1) (m2 : PMap.t T2),
  (forall k, m1 ?? k = None <-> m2 ?? k = None) ->
  parser_extracts_ok p m2 -> parser_extracts_ok p m1.
Proof.
  intros T1 T2 p m1 m2 Hd H. unfold parser_extracts_ok in *.
  rewrite List.Forall_forall in *. intros d Hin. specialize (H d Hin).
  revert H. destruct (psd_action d) as [[w | h w of] |]; intro H; try exact I.
  intro Hc. apply H. apply Hd. exact Hc.
Qed.

(* ==================================================================== *)
(* 13. THE PARSER MODULE.                                                *)
(*                                                                       *)
(* [eval_parser_commute] relates the two runs; this puts its conclusion   *)
(* into the shape [module_update_gs_*] consumes, which means turning the  *)
(* POINTWISE header agreement it gives into the whole-map equality        *)
(* [gps_agree] wants.  §12 is what closes that gap.                       *)
(*                                                                       *)
(* Note which half is unconditional.  The accept flags always agree --    *)
(* that is what carries the verdict through a rejecting parser, where     *)
(* nothing else does.  Everything else is guarded by acceptance, because  *)
(* on a rejecting path the symbolic run has read padding and carried on   *)
(* down a path the concrete run does not have.                            *)
(* ==================================================================== *)

Theorem parser_mod_commute : forall pr ps f m,
  well_formed_parser pr ->
  p_cursor ps = 0%nat ->
  pprefix f (p_packet ps) ->
  parser_extracts_ok pr m ->
  pmap_shape (p_header_map ps) m ->
  exists cr,
    eval_parser_concrete pr (eval_sym_parser_state ps f) = Some cr
    /\ pr_accept cr = eval_smt_bool (pr_accept (eval_parser_symbolic pr ps)) f
    /\ (pr_accept cr = true ->
          pr_headers cr = PMap.map (fun e => eval_smt_arith e f)
                            (pr_headers (eval_parser_symbolic pr ps))
          /\ pr_residual cr = present_bits (pr_residual (eval_parser_symbolic pr ps)) f
          /\ pr_bits_read cr = eval_smt_arith (pr_bits_read (eval_parser_symbolic pr ps)) f
          /\ ParserMod {| p_header_map := pr_headers cr;
                          p_packet     := pr_residual cr;
                          p_cursor     := 0 |}
             = concretize_sym_module_state
                 (ParserMod {| p_header_map := pr_headers (eval_parser_symbolic pr ps);
                               p_packet     := pr_residual (eval_parser_symbolic pr ps);
                               p_cursor     := 0 |}) f).
Proof.
  intros pr ps f m Hwf Hcur Hpp Hok Hps.
  destruct (eval_parser_commute pr ps f Hwf Hcur Hpp) as [cr [Hc Hra]].
  destruct Hra as [Hacc Hrest].
  cbn [eval_smt_bool] in Hacc, Hrest. rewrite andb_true_l in Hacc, Hrest.
  exists cr. split; [exact Hc | split; [symmetry; exact Hacc |]].
  intro Hv.
  destruct (Hrest Hv) as [Hhk [Hres Hbits]].
  symmetry in Hres. symmetry in Hbits.
  (* the header map, as a whole map: per key from [result_agree], defaults and
     domains from section 12 *)
  assert (Hhdr : pr_headers cr
                 = PMap.map (fun e => eval_smt_arith e f)
                     (pr_headers (eval_parser_symbolic pr ps))).
  { assert (Hcs : pmap_shape (pr_headers cr)
                    (p_header_map (eval_sym_parser_state ps f))).
    { unfold eval_parser_concrete in Hc.
      eapply run_parser_concrete_shape; [| exact Hc ].
      cbn [eval_sym_parser_state p_header_map].
      eapply parser_extracts_ok_dom; [| exact Hok ].
      intro k. eapply iff_trans; [ apply pmap_map_dom |]. apply Hps. }
    cbn [eval_sym_parser_state p_header_map] in Hcs.
    assert (Hss : pmap_shape (pr_headers (eval_parser_symbolic pr ps)) m)
      by (unfold eval_parser_symbolic; apply run_parser_symbolic_shape;
          [ exact Hok | exact Hps ]).
    destruct Hcs as [Hcd Hck]. destruct Hss as [Hsd Hsk]. destruct Hps as [Hpd Hpk].
    apply pmap_ext.
    - rewrite Hcd, !pmap_map_default, Hpd, Hsd. reflexivity.
    - intro k. eapply iff_trans; [ apply Hck |].
      eapply iff_trans; [ apply pmap_map_dom |].
      eapply iff_trans; [ apply Hpk |]. symmetry.
      eapply iff_trans; [ apply pmap_map_dom |]. apply Hsk.
    - intro k. rewrite PMap.gmap. symmetry. apply Hhk. }
  split; [exact Hhdr | split; [exact Hres | split; [exact Hbits |]]].
  cbn [concretize_sym_module_state eval_sym_parser_state].
  rewrite Hhdr, Hres. reflexivity.
Qed.

(* ==================================================================== *)
(* 14. THE EXTENT MAP'S DEFAULT NEVER MOVES.                             *)
(*                                                                       *)
(* §8 bridges the memory-safety check across [gps_agree]'s pointwise      *)
(* weakening, but only for extent maps whose DEFAULT is [mk_int u64 0] --  *)
(* the value that makes an untouched region in bounds.  So the network    *)
(* induction has to carry that as an invariant, and this is what          *)
(* preserves it: every writer of an extent map is a [PMap.set], on both   *)
(* sides, and [PMap.set] never moves [fst].                                *)
(*                                                                       *)
(* Only the transformer touches memory; a parser and a deparser leave the *)
(* extent map alone, so this section is about one module kind.            *)
(* ==================================================================== *)

Lemma bump_extent_concrete_default : forall mc r off,
  fst (mc_extent (bump_extent_concrete mc r off)) = fst (mc_extent mc).
Proof. intros mc r off. reflexivity. Qed.

Lemma bump_extent_span_concrete_default : forall mc r base n,
  fst (mc_extent (bump_extent_span_concrete mc r base n)) = fst (mc_extent mc).
Proof.
  intros mc r base n. unfold bump_extent_span_concrete.
  generalize (List.seq 0 n) as l. intro l. revert mc.
  induction l as [| i rest IH]; intros mc; cbn [List.fold_left]; [reflexivity |].
  rewrite IH. apply bump_extent_concrete_default.
Qed.

Lemma op_extent_default : forall op mc ps,
  fst (mc_extent (fst (eval_hdr_op_assign_concrete_mem op mc ps))) = fst (mc_extent mc).
Proof.
  intros op mc ps.
  destruct op; cbn [eval_hdr_op_assign_concrete_mem fst];
    solve [ reflexivity
          | apply bump_extent_span_concrete_default
          | rewrite bump_extent_span_concrete_default; reflexivity ].
Qed.

Lemma op_list_extent_default : forall hol mc ps,
  fst (mc_extent (fst (eval_hdr_op_list_concrete_mem hol mc ps))) = fst (mc_extent mc).
Proof.
  induction hol as [| op rest IH]; intros mc ps; [reflexivity |].
  rewrite eval_hdr_op_list_concrete_mem_cons, IH. apply op_extent_default.
Qed.

Lemma rule_extent_default : forall rule mc ps,
  fst (mc_extent (fst (eval_match_action_rule_concrete_mem rule mc ps)))
  = fst (mc_extent mc).
Proof.
  intros [[mp action] | [mp action]] mc ps;
    cbn [eval_match_action_rule_concrete_mem eval_seq_rule_concrete_mem
         eval_par_rule_concrete_mem];
    destruct (eval_match_concrete mp ps);
    solve [ apply op_list_extent_default | reflexivity ].
Qed.

Theorem transformer_extent_default : forall t mc ps,
  fst (mc_extent (fst (eval_transformer_concrete_mem t mc ps))) = fst (mc_extent mc).
Proof.
  intros t mc ps. unfold eval_transformer_concrete_mem. cbv zeta.
  destruct (find_first_match (List.combine (get_match_results t ps) t)) as [rule |];
    [ apply rule_extent_default | reflexivity ].
Qed.

(* The symbolic side rebuilds the extent map with one fold of [PMap.set], so
   the same holds -- and since the default is untouched, so is its value under
   any valuation. *)
Lemma pmap_fold_set_default : forall (T : Type) (l : list positive) (F : positive -> T) (m : PMap.t T),
  fst (List.fold_left (fun acc k => PMap.set k (F k) acc) l m) = fst m.
Proof.
  intros T l. induction l as [| k r IH]; intros F m; cbn [List.fold_left];
    [reflexivity | rewrite IH; reflexivity].
Qed.

Theorem transformer_smt_extent_default : forall t mc ps,
  fst (mc_extent (fst (eval_transformer_smt_mem t mc ps))) = fst (mc_extent mc).
Proof.
  intros t mc ps. unfold eval_transformer_smt_mem. cbv zeta. cbn [fst mc_extent].
  apply pmap_fold_set_default.
Qed.

(* At the module level.  A parser and a deparser do not touch the extent map
   at all; a transformer replaces it with what its own run produced, which by
   the section above has the default it started with. *)
Lemma module_update_concrete_extent_default : forall m ls gs,
  fst (sh_mem_extent gs) = mk_int u64 0 ->
  fst (sh_mem_extent (module_update_gs_concrete m ls gs)) = mk_int u64 0.
Proof.
  intros m ls gs H. unfold module_update_gs_concrete.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    cbv zeta;
    cbn [sh_mem_extent set_gps_valid set_gps_mod_states set_gps_mem
         set_gps_mem_extent set_gps_shared_headers set_gps_bits_read
         set_gps_shared_read_tape set_gps_shared_write_tape];
    try exact H.
  - destruct (eval_parser_concrete pp ps);
      cbn [sh_mem_extent set_gps_valid set_gps_mod_states set_gps_bits_read
           set_gps_shared_read_tape set_gps_shared_headers];
      exact H.
  - rewrite transformer_extent_default. exact H.
Qed.

Lemma module_update_symbolic_extent_default : forall m ls gs f,
  eval_smt_arith (fst (sh_mem_extent gs)) f = mk_int u64 0 ->
  eval_smt_arith (fst (sh_mem_extent (module_update_gs_symbolic m ls gs))) f
  = mk_int u64 0.
Proof.
  intros m ls gs f H. unfold module_update_gs_symbolic.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    cbv zeta;
    cbn [sh_mem_extent set_gps_valid set_gps_mod_states set_gps_mem
         set_gps_mem_extent set_gps_shared_headers set_gps_bits_read
         set_gps_shared_read_tape set_gps_shared_write_tape];
    try exact H.
  rewrite transformer_smt_extent_default. exact H.
Qed.

(* ==================================================================== *)
(* 15. ONE MODULE, AS A STEP.                                            *)
(*                                                                       *)
(* The three module-kind results are stated about the evaluators; the    *)
(* network recursion calls them through [module_update_gs_*], which      *)
(* threads the shared header map and tape in and copies the results back *)
(* out.  This section restates each kind in that shape, so the induction  *)
(* has one lemma per kind and no plumbing of its own.                     *)
(*                                                                       *)
(* A transformer is the case where nothing can go wrong: it does not     *)
(* write [gps_valid] at all, so its step is unconditional.  The memory   *)
(* is the only subtlety -- the concrete state's memory is only POINTWISE *)
(* equal to the concretized symbolic one, so the transformer results     *)
(* (stated over the literal [concretize_mem_ctx]) reach it through       *)
(* [eval_transformer_concrete_mem_cong].                                 *)
(* ==================================================================== *)

(* The fields of a concretized network state, as rewrite rules.  [cbn] does
   not reliably reduce a projection of [concretize_sym_modnet_state] under the
   hypotheses these proofs carry, so the equations are named. *)
Lemma cz_hdr : forall s f,
  sh_hdr_map (concretize_sym_modnet_state s f)
  = PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map s).
Proof. reflexivity. Qed.

Lemma cz_read : forall s f,
  sh_read_tape (concretize_sym_modnet_state s f) = present_bits (sh_read_tape s) f.
Proof. reflexivity. Qed.

Lemma cz_bits : forall s f,
  sh_bits_read (concretize_sym_modnet_state s f) = eval_smt_arith (sh_bits_read s) f.
Proof. reflexivity. Qed.

Lemma cz_write : forall s f,
  sh_write_tape (concretize_sym_modnet_state s f)
  = List.map (fun b => eval_smt_bool (cvv b) f) (sh_write_tape s).
Proof. reflexivity. Qed.

Lemma cz_mem : forall s f,
  sh_mem (concretize_sym_modnet_state s f)
  = PMap.map (fun a => eval_smt_mem a f) (sh_mem s).
Proof. reflexivity. Qed.

Lemma cz_ext : forall s f,
  sh_mem_extent (concretize_sym_modnet_state s f)
  = PMap.map (fun e => eval_smt_arith e f) (sh_mem_extent s).
Proof. reflexivity. Qed.

Lemma cz_ms : forall s f,
  mod_states (concretize_sym_modnet_state s f)
  = PMap.map (fun st => concretize_sym_module_state st f) (mod_states s).
Proof. reflexivity. Qed.

Lemma cz_valid : forall s f,
  gps_valid (concretize_sym_modnet_state s f) = eval_smt_bool (cvv (gps_valid s)) f.
Proof. reflexivity. Qed.

(* Setting one key on each side of a [PMap.map] relation keeps it, given the
   two values correspond.  Used at every module kind: the network stores each
   module's new state with one [PMap.set], so this is how [mod_states] stays a
   literal [PMap.map] of the symbolic one. *)
Lemma pmap_set_map_eq : forall (A B : Type) (g : A -> B) k (v : B) (w : A)
    (mc : PMap.t B) (ms : PMap.t A),
  mc = PMap.map g ms -> v = g w ->
  PMap.set k v mc = PMap.map g (PMap.set k w ms).
Proof.
  intros A B g k v w mc ms H1 H2. subst.
  unfold PMap.map, PMap.set. cbn [fst snd]. f_equal.
  apply PTree.extensionality. intros i.
  rewrite PTree.gmap1, !PTree.gsspec, PTree.gmap1.
  destruct (Coqlib.peq i k); reflexivity.
Qed.

Lemma gps_valid_transformer_concrete : forall mid s c t ts gs,
  gps_valid (module_update_gs_concrete (TransformerModule mid s c t) (TransformerMod ts) gs)
  = gps_valid gs.
Proof. reflexivity. Qed.

Lemma gps_valid_transformer_symbolic : forall mid s c t ts gs,
  gps_valid (module_update_gs_symbolic (TransformerModule mid s c t) (TransformerMod ts) gs)
  = gps_valid gs.
Proof. reflexivity. Qed.

Theorem transformer_mod_step : forall mid sdecl cdecl t ts f cgs sgs,
  (* the concrete memory agrees with the concretized symbolic memory, pointwise *)
  (forall k, (sh_mem cgs) !! k = (sh_mem (concretize_sym_modnet_state sgs f)) !! k) ->
  (forall k, (sh_mem_extent cgs) !! k
             = (sh_mem_extent (concretize_sym_modnet_state sgs f)) !! k) ->
  mod_states cgs = mod_states (concretize_sym_modnet_state sgs f) ->
  transformer_dom_ok t (eval_sym_state ts f) ->
  let m := TransformerModule mid sdecl cdecl t in
  let cls := TransformerMod (eval_sym_state ts f) in
  let sls := TransformerMod ts in
  sh_hdr_map (module_update_gs_concrete m cls cgs)
    = sh_hdr_map (concretize_sym_modnet_state (module_update_gs_symbolic m sls sgs) f)
  /\ mod_states (module_update_gs_concrete m cls cgs)
     = mod_states (concretize_sym_modnet_state (module_update_gs_symbolic m sls sgs) f)
  /\ (forall k, (sh_mem (module_update_gs_concrete m cls cgs)) !! k
                = (sh_mem (concretize_sym_modnet_state
                             (module_update_gs_symbolic m sls sgs) f)) !! k)
  /\ (forall k, (sh_mem_extent (module_update_gs_concrete m cls cgs)) !! k
                = (sh_mem_extent (concretize_sym_modnet_state
                                    (module_update_gs_symbolic m sls sgs) f)) !! k).
Proof.
  intros mid sdecl cdecl t ts f cgs sgs Hmem Hext Hms Hdom m cls sls.
  unfold m, cls, sls, module_update_gs_concrete, module_update_gs_symbolic.
  cbv zeta.
  cbn [sh_hdr_map mod_states sh_mem sh_mem_extent
       set_gps_mod_states set_gps_mem set_gps_mem_extent set_gps_shared_headers
       concretize_sym_modnet_state module_header_map].
  (* the two memory contexts the transformer is handed *)
  set (mcS := {| mc_mem := sh_mem sgs; mc_extent := sh_mem_extent sgs |}) in *.
  set (mcC := {| mc_mem := sh_mem cgs; mc_extent := sh_mem_extent cgs |}) in *.
  assert (Hmc : mc_agree mcC (concretize_mem_ctx mcS f)).
  { split; intro k; unfold mcC, mcS;
      cbn [mc_mem mc_extent concretize_mem_ctx].
    - rewrite Hmem. reflexivity.
    - rewrite Hext. reflexivity. }
  destruct (eval_transformer_concrete_mem_cong t mcC (concretize_mem_ctx mcS f)
              (eval_sym_state ts f) Hmc) as [[Hcm Hce] Hcs].
  (* the module-local state: proved equal by step 6 *)
  rewrite Hcs, (transformer_state_commute t mcS ts f Hdom).
  rewrite cz_ms in Hms.
  split; [| split; [| split]].
  - (* headers: [module_header_map] of the merged state, which is that state's
       header map -- and [eval_sym_state] commutes with the projection *)
    cbn [module_header_map]. apply eval_sym_state_hdr.
  - (* module states: one [PMap.set] on each side, at the same key *)
    eapply pmap_set_map_eq; [ exact Hms | reflexivity ].
  - (* memory *) intro k. rewrite Hcm, PMap.gmap.
    apply (transformer_commute_mem t mcS ts f k).
  - (* extents *) intro k. rewrite Hce, PMap.gmap.
    apply (transformer_commute_extent t mcS ts f k).
Qed.

(* A deparser writes only the write tape and its own module state.  Like the
   transformer it never touches [gps_valid], and unlike either other kind it
   does not touch the header map -- it only reads one.  The write tape is
   APPENDED to, so the step needs [List.map_app] and nothing else. *)
Lemma gps_valid_deparser_concrete : forall mid d ds gs,
  gps_valid (module_update_gs_concrete (DeparserModule mid d) (DeparserMod ds) gs)
  = gps_valid gs.
Proof. reflexivity. Qed.

Lemma gps_valid_deparser_symbolic : forall mid d ds gs,
  gps_valid (module_update_gs_symbolic (DeparserModule mid d) (DeparserMod ds) gs)
  = gps_valid gs.
Proof. reflexivity. Qed.

Theorem deparser_mod_step : forall mid d f cgs sgs hm cpkt spkt,
  sh_write_tape cgs = sh_write_tape (concretize_sym_modnet_state sgs f) ->
  mod_states cgs = mod_states (concretize_sym_modnet_state sgs f) ->
  let m := DeparserModule mid d in
  let sls := DeparserMod {| p_header_map := hm; p_packet := spkt; p_cursor := 0 |} in
  let cls := DeparserMod {| p_header_map := PMap.map (fun e => eval_smt_arith e f) hm;
                            p_packet := cpkt; p_cursor := 0 |} in
  sh_write_tape (module_update_gs_concrete m cls cgs)
    = sh_write_tape (concretize_sym_modnet_state (module_update_gs_symbolic m sls sgs) f)
  /\ mod_states (module_update_gs_concrete m cls cgs)
     = mod_states (concretize_sym_modnet_state (module_update_gs_symbolic m sls sgs) f).
Proof.
  intros mid d f cgs sgs hm cpkt spkt Hwt Hms m sls cls.
  pose proof (deparser_mod_commute d
                {| p_header_map := hm; p_packet := spkt; p_cursor := 0 |} f cpkt) as Hdp.
  cbn [p_header_map concretize_sym_module_state] in Hdp.
  unfold m, cls, sls, module_update_gs_concrete, module_update_gs_symbolic. cbv zeta.
  rewrite cz_write in Hwt. rewrite cz_ms in Hms.
  cbn [sh_write_tape mod_states set_gps_mod_states set_gps_shared_write_tape
       concretize_sym_modnet_state].
  (* Project the emitted packet out of the module-state equality, rather than
     restating the record: [f_equal] with a projector is robust to how the
     concretizer happens to be reduced. *)
  assert (Hpk := f_equal
    (fun ms => match ms with
               | DeparserMod q => p_packet q
               | _ => @nil bool
               end) Hdp).
  cbn [p_packet concretize_sym_module_state] in Hpk.
  split.
  - (* the write tape: both sides append what this deparser emitted *)
    rewrite List.map_app, <- Hwt. f_equal.
    exact Hpk.
  - (* module states *)
    eapply pmap_set_map_eq; [ exact Hms | exact Hdp ].
Qed.

Lemma esps_eq : forall ps f,
  eval_sym_parser_state ps f =
  {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
     p_packet     := present_bits (p_packet ps) f;
     p_cursor     := p_cursor ps |}.
Proof. reflexivity. Qed.

(* The parser is the only kind that writes [gps_valid], and the only one whose
   step splits.  The flag half is UNCONDITIONAL -- both sides conjoin the
   accept condition into the running validity, and the two accept conditions
   agree whatever the packet did.  Everything else is available only when the
   result is valid, because on a rejecting path the symbolic run read padding
   and carried on down a path the concrete run does not have. *)
Theorem parser_mod_step : forall mid pr f cgs sgs hm spkt m,
  well_formed_parser pr ->
  pprefix f spkt ->
  parser_extracts_ok pr m ->
  pmap_shape hm m ->
  gps_valid cgs = eval_smt_bool (cvv (gps_valid sgs)) f ->
  sh_bits_read cgs = sh_bits_read (concretize_sym_modnet_state sgs f) ->
  mod_states cgs = mod_states (concretize_sym_modnet_state sgs f) ->
  let md := ParserModule mid pr in
  let sls := ParserMod {| p_header_map := hm; p_packet := spkt; p_cursor := 0 |} in
  let cls := ParserMod {| p_header_map := PMap.map (fun e => eval_smt_arith e f) hm;
                          p_packet := present_bits spkt f; p_cursor := 0 |} in
  gps_valid (module_update_gs_concrete md cls cgs)
    = gps_valid (concretize_sym_modnet_state (module_update_gs_symbolic md sls sgs) f)
  /\ (gps_valid (module_update_gs_concrete md cls cgs) = true ->
        sh_hdr_map (module_update_gs_concrete md cls cgs)
          = sh_hdr_map (concretize_sym_modnet_state (module_update_gs_symbolic md sls sgs) f)
        /\ sh_read_tape (module_update_gs_concrete md cls cgs)
           = sh_read_tape (concretize_sym_modnet_state (module_update_gs_symbolic md sls sgs) f)
        /\ sh_bits_read (module_update_gs_concrete md cls cgs)
           = sh_bits_read (concretize_sym_modnet_state (module_update_gs_symbolic md sls sgs) f)
        /\ mod_states (module_update_gs_concrete md cls cgs)
           = mod_states (concretize_sym_modnet_state
                           (module_update_gs_symbolic md sls sgs) f)).
Proof.
  intros mid pr f cgs sgs hm spkt m Hwf Hpp Hok Hshape Hval Hbits Hms md sls cls.
  destruct (parser_mod_commute pr {| p_header_map := hm; p_packet := spkt; p_cursor := 0 |}
              f m Hwf eq_refl Hpp Hok Hshape) as [cr [Hc [Hacc Hrest]]].
  rewrite esps_eq in Hc. cbn [p_header_map p_packet p_cursor] in Hc.
  rewrite cz_bits in Hbits. rewrite cz_ms in Hms.
  unfold md, cls, sls, module_update_gs_concrete, module_update_gs_symbolic. cbv zeta.
  rewrite Hc.
  cbn [gps_valid sh_hdr_map sh_read_tape sh_bits_read mod_states cvv
       set_gps_valid set_gps_mod_states set_gps_bits_read
       set_gps_shared_read_tape set_gps_shared_headers
       concretize_sym_modnet_state].
  (* the flag, unconditionally *)
  assert (Hflag : (gps_valid cgs && pr_accept cr)%bool
                  = eval_smt_bool (SmtBoolAnd (cvv (gps_valid sgs))
                                     (pr_accept (eval_parser_symbolic pr
                                       {| p_header_map := hm; p_packet := spkt;
                                          p_cursor := 0 |}))) f).
  { cbn [eval_smt_bool]. rewrite Hval, Hacc. reflexivity. }
  split; [exact Hflag |].
  intro Hv.
  (* validity of the result forces the parser to have accepted *)
  assert (Hpa : pr_accept cr = true)
    by (destruct (pr_accept cr); [reflexivity |];
        rewrite andb_false_r in Hv; discriminate).
  destruct (Hrest Hpa) as [Hhdr [Hres [Hbr _]]].
  split; [exact Hhdr | split; [exact Hres | split]].
  - (* bits read: both sides add this parser's count to the running total *)
    cbn [eval_smt_arith]. rewrite Hbits, Hbr. reflexivity.
  - (* module states *)
    eapply pmap_set_map_eq; [ exact Hms |].
    cbn [concretize_sym_module_state eval_sym_parser_state].
    rewrite Hhdr, Hres. reflexivity.
Qed.

(* ==================================================================== *)
(* 16. THE DOMAIN CONDITIONS SURVIVE A MODULE.                           *)
(*                                                                       *)
(* Steps 6 and 7 each take a domain condition, stated against the state  *)
(* the module is HANDED.  The induction runs modules in sequence, so     *)
(* after module A runs, module B's condition has to still hold.  Both    *)
(* conditions depend on their state only through its SHAPE (that is what *)
(* [op_dom_ok_shape] and [parser_extracts_ok_shape] say), and every      *)
(* module preserves the header map's shape -- so this section is the     *)
(* lift of §10 and §12 to the network state.                             *)
(* ==================================================================== *)

Lemma pmap_shape_map : forall (A B : Type) (g : A -> B) (m1 m2 : PMap.t A),
  pmap_shape m1 m2 -> pmap_shape (PMap.map g m1) (PMap.map g m2).
Proof.
  intros A B g m1 m2 [Hd Hk]. split.
  - rewrite !pmap_map_default, Hd. reflexivity.
  - apply pmap_map_shape_iff. exact Hk.
Qed.

Lemma ts_shape_sym : forall (T : Type) (a b : TransformerState T),
  ts_shape a b -> ts_shape b a.
Proof.
  intros T a b [[H1 K1] [[H2 K2] [H3 K3]]].
  split; [| split]; split; try (symmetry; assumption);
    intro k; symmetry; solve [ apply K1 | apply K2 | apply K3 ].
Qed.

Lemma ts_shape_inject : forall (T : Type) (h1 h2 : PMap.t T) (a b : TransformerState T),
  pmap_shape h1 h2 -> pmap_shape (t_state_map a) (t_state_map b) ->
  pmap_shape (t_ctrl_map a) (t_ctrl_map b) ->
  ts_shape (inject_headers h1 a) (inject_headers h2 b).
Proof.
  intros T h1 h2 a b Hh Hs Hc. unfold inject_headers.
  split; [| split]; cbn [t_ctrl_map t_header_map t_state_map]; assumption.
Qed.

Lemma eval_sym_state_shape : forall a b f,
  ts_shape a b -> ts_shape (eval_sym_state a f) (eval_sym_state b f).
Proof.
  intros a b f [Hc [Hh Hs]]. unfold eval_sym_state. cbv zeta.
  rewrite !program_state_mapper_eq_local.
  split; [| split]; cbn [t_ctrl_map t_header_map t_state_map];
    apply pmap_shape_map; assumption.
Qed.

(* [transformer_dom_ok] through the same shape argument [op_dom_ok] uses. *)
Lemma rule_dom_ok_shape : forall (T : Type) rule (ps1 ps2 : TransformerState T),
  ts_shape ps1 ps2 -> rule_dom_ok rule ps2 -> rule_dom_ok rule ps1.
Proof.
  intros T rule ps1 ps2 Hs H. unfold rule_dom_ok in *.
  rewrite List.Forall_forall in *. intros op Hin.
  eapply op_dom_ok_shape; [ exact Hs | apply H; exact Hin ].
Qed.

Lemma transformer_dom_ok_shape : forall (T : Type) t (ps1 ps2 : TransformerState T),
  ts_shape ps1 ps2 -> transformer_dom_ok t ps2 -> transformer_dom_ok t ps1.
Proof.
  intros T t ps1 ps2 Hs H. unfold transformer_dom_ok in *.
  rewrite List.Forall_forall in *. intros rule Hin.
  eapply rule_dom_ok_shape; [ exact Hs | apply H; exact Hin ].
Qed.

(* ==================================================================== *)
(* 17. THE RECURSION, DESTRUCTURED.                                      *)
(*                                                                       *)
(* §3 says the fold over [downstream_modules] is at most one step under  *)
(* [no_fan_out].  These are that observation carried out: two equations  *)
(* per evaluator, one per case.                                          *)
(*                                                                       *)
(* The second is worth reading carefully.  The recursive call is handed  *)
(* [sh_hdr_map gs'] and [sh_read_tape gs'] while the fold's accumulator  *)
(* is [gs'] itself -- so the threaded header map and tape are always the *)
(* PROJECTIONS of the state being passed.  That is what lets the whole   *)
(* induction be stated about a state rather than about a state plus two  *)
(* loose arguments that have to be related to it.                        *)
(* ==================================================================== *)

Lemma network_concrete_stop : forall net start f_hdrs f_bits gs fuel' m ls,
  lookup_module net start = Some m ->
  (mod_states gs) ?? (unwrap start) = Some ls ->
  downstream_modules net start = [] ->
  eval_network_from_concrete net start f_hdrs f_bits gs (S fuel')
  = Some (module_update_gs_concrete m
            (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs).
Proof.
  intros net start f_hdrs f_bits gs fuel' m ls Hm Hls Hd.
  rewrite network_concrete_step, Hm, Hls, Hd. reflexivity.
Qed.

Lemma network_concrete_go : forall net start f_hdrs f_bits gs fuel' m ls dst,
  lookup_module net start = Some m ->
  (mod_states gs) ?? (unwrap start) = Some ls ->
  downstream_modules net start = [dst] ->
  eval_network_from_concrete net start f_hdrs f_bits gs (S fuel')
  = (let gs' := module_update_gs_concrete m
                  (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs in
     eval_network_from_concrete net dst (sh_hdr_map gs') (sh_read_tape gs') gs' fuel').
Proof.
  intros net start f_hdrs f_bits gs fuel' m ls dst Hm Hls Hd.
  rewrite network_concrete_step, Hm, Hls, Hd. reflexivity.
Qed.

Lemma network_symbolic_stop : forall net start f_hdrs f_bits gs fuel' m ls,
  lookup_module net start = Some m ->
  (mod_states gs) ?? (unwrap start) = Some ls ->
  downstream_modules net start = [] ->
  eval_network_from_symbolic net start f_hdrs f_bits gs (S fuel')
  = Some (module_update_gs_symbolic m
            (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs).
Proof.
  intros net start f_hdrs f_bits gs fuel' m ls Hm Hls Hd.
  rewrite network_symbolic_step, Hm, Hls, Hd. reflexivity.
Qed.

Lemma network_symbolic_go : forall net start f_hdrs f_bits gs fuel' m ls dst,
  lookup_module net start = Some m ->
  (mod_states gs) ?? (unwrap start) = Some ls ->
  downstream_modules net start = [dst] ->
  eval_network_from_symbolic net start f_hdrs f_bits gs (S fuel')
  = (let gs' := module_update_gs_symbolic m
                  (set_module_packet (set_module_header_map ls f_hdrs) f_bits) gs in
     eval_network_from_symbolic net dst (sh_hdr_map gs') (sh_read_tape gs') gs' fuel').
Proof.
  intros net start f_hdrs f_bits gs fuel' m ls dst Hm Hls Hd.
  rewrite network_symbolic_step, Hm, Hls, Hd. reflexivity.
Qed.

(* A lookup that fails makes the whole run [None], on either side. *)
Lemma network_concrete_none : forall net start f_hdrs f_bits gs fuel',
  (lookup_module net start = None \/ (mod_states gs) ?? (unwrap start) = None) ->
  eval_network_from_concrete net start f_hdrs f_bits gs (S fuel') = None.
Proof.
  intros net start f_hdrs f_bits gs fuel' [H | H]; rewrite network_concrete_step.
  - rewrite H. reflexivity.
  - destruct (lookup_module net start); [rewrite H |]; reflexivity.
Qed.

Lemma network_symbolic_none : forall net start f_hdrs f_bits gs fuel',
  (lookup_module net start = None \/ (mod_states gs) ?? (unwrap start) = None) ->
  eval_network_from_symbolic net start f_hdrs f_bits gs (S fuel') = None.
Proof.
  intros net start f_hdrs f_bits gs fuel' [H | H]; rewrite network_symbolic_step.
  - rewrite H. reflexivity.
  - destruct (lookup_module net start); [rewrite H |]; reflexivity.
Qed.

(* ==================================================================== *)
(* 18. THE NETWORK INVARIANT.                                            *)
(*                                                                       *)
(* [gs_rel] is what the induction carries between the two runs.  Three   *)
(* parts, and the split is forced by the rejecting case:                 *)
(*                                                                       *)
(*   (a) the module-state DOMAINS agree, unconditionally.  Without this  *)
(*       the two runs can disagree about whether the network completes   *)
(*       at all -- the recursion looks the start module's state up and   *)
(*       returns [None] when it is missing.                              *)
(*   (b) [gps_valid] agrees, unconditionally.  Carried by §4: once both  *)
(*       runs are invalid neither can clear the flag, so the verdicts    *)
(*       agree for the rest of the network with nothing known about the  *)
(*       states.                                                         *)
(*   (c) [gps_agree] only under validity.  On a rejecting path the       *)
(*       symbolic run has read padding and carried on down a path the    *)
(*       concrete run does not have, so there is nothing else to say.    *)
(* ==================================================================== *)

Definition ls_kind_agree (c : ConcreteModuleState) (s : SymbolicModuleState) : Prop :=
  match c, s with
  | TransformerMod _, TransformerMod _ => True
  | ParserMod _, ParserMod _ => True
  | DeparserMod _, DeparserMod _ => True
  | _, _ => False
  end.

Definition ms_kind_agree (cms : PMap.t ConcreteModuleState)
    (sms : PMap.t SymbolicModuleState) : Prop :=
  forall k, match cms ?? k, sms ?? k with
            | None, None => True
            | Some a, Some b => ls_kind_agree a b
            | _, _ => False
            end.

(* Reading the agreement at one key.  [rewrite] cannot reach inside the nested
   [match] the definition unfolds to, so this goes through [destruct]. *)
Lemma ms_kind_agree_at : forall cms sms k cls ls,
  ms_kind_agree cms sms -> cms ?? k = Some cls -> sms ?? k = Some ls ->
  ls_kind_agree cls ls.
Proof.
  intros cms sms k cls ls H Hc Hs. pose proof (H k) as Hk.
  destruct (cms ?? k) as [a |] eqn:E1; destruct (sms ?? k) as [b |] eqn:E2;
    try discriminate.
  injection Hc as <-. injection Hs as <-. exact Hk.
Qed.

(* Getting the concrete side's entry POSITIVELY, rather than refuting its
   absence.  Stated over plain map variables so the use site's conversion is
   handled by unification: [mod_states sgs] has type
   [PMap.t (ModuleState _ _)] while [ms_kind_agree] is typed at
   [PMap.t SymbolicModuleState], and the two are convertible but not
   syntactically equal -- enough to defeat [rewrite] and [congruence]. *)
Lemma ms_kind_agree_some : forall cms sms k ls,
  ms_kind_agree cms sms -> sms ?? k = Some ls ->
  exists cls, cms ?? k = Some cls /\ ls_kind_agree cls ls.
Proof.
  intros cms sms k ls H Hs. pose proof (H k) as Hk.
  destruct (cms ?? k) as [a |] eqn:E1; destruct (sms ?? k) as [b |] eqn:E2;
    try contradiction; try discriminate.
  injection Hs as <-. exists a. split; [reflexivity | exact Hk].
Qed.

Lemma ms_kind_agree_dom : forall cms sms,
  ms_kind_agree cms sms -> forall k, cms ?? k = None <-> sms ?? k = None.
Proof.
  intros cms sms H k. specialize (H k).
  destruct (cms ?? k) as [a |]; destruct (sms ?? k) as [b |];
    try contradiction; split; intro Hc; congruence.
Qed.

(* The middle clause is KIND agreement, not merely domain agreement -- see §19
   for why domain agreement is not preserved on its own. *)
Definition gs_rel (f : SmtValuation) (c : GeneralConcreteState) (s : GeneralSymbolicState) : Prop :=
  gps_valid c = eval_smt_bool (cvv (gps_valid s)) f
  /\ ms_kind_agree (mod_states c) (mod_states s)
  /\ (gps_valid c = true -> gps_agree c (concretize_sym_modnet_state s f)).

(* The domain condition steps 6 and 7 need, as a condition on the state the
   module is handed.  A deparser needs nothing: it writes no varlike. *)
Definition dom_ok_at (f : SmtValuation) (m : CrModule) (hm : PMap.t SmtArithExpr)
    (ls : SymbolicModuleState) : Prop :=
  match m, ls with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      transformer_dom_ok t (eval_sym_state (inject_headers hm ts) f)
  | ParserModule _ pr, _ => parser_extracts_ok pr hm
  | _, _ => True
  end.

Definition gs_dom_ok (net : ModuleNetwork) (f : SmtValuation) (gs : GeneralSymbolicState) : Prop :=
  forall lbl m ls,
    lookup_module net lbl = Some m ->
    (mod_states gs) ?? (unwrap lbl) = Some ls ->
    dom_ok_at f m (sh_hdr_map gs) ls.

(* [eval_transformer_smt_mem] does not touch the ctrl map: [update_all_varlike]
   runs over headers and state variables only. *)
Lemma smt_transformer_ctrl_eq : forall t mc ps,
  t_ctrl_map (snd (eval_transformer_smt_mem t mc ps)) = t_ctrl_map ps.
Proof.
  intros t mc ps. unfold eval_transformer_smt_mem. cbv zeta. cbn [snd].
  cbn [update_all_varlike CrVarLike_Header CrVarLike_State
       t_ctrl_map t_header_map t_state_map].
  reflexivity.
Qed.

(* Every module preserves the shared header map's SHAPE.  A transformer and a
   parser rebuild it (§10, §12); a deparser and the kind-mismatch fallback
   leave it alone. *)
Lemma module_update_symbolic_hdr_shape : forall f gs m ls,
  dom_ok_at f m (sh_hdr_map gs) ls ->
  pmap_shape
    (sh_hdr_map (module_update_gs_symbolic m
       (set_module_packet (set_module_header_map ls (sh_hdr_map gs))
          (sh_read_tape gs)) gs))
    (sh_hdr_map gs).
Proof.
  intros f gs m ls Hdom.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    unfold module_update_gs_symbolic; cbv zeta;
    cbn [set_module_header_map set_module_packet sh_hdr_map module_header_map
         set_gps_valid set_gps_mod_states set_gps_mem set_gps_mem_extent
         set_gps_shared_headers set_gps_bits_read set_gps_shared_read_tape
         set_gps_shared_write_tape];
    try apply pmap_shape_refl.
  - (* parser: §12, with the handed header map as its own reference shape *)
    cbn [dom_ok_at] in Hdom.
    unfold eval_parser_symbolic. apply run_parser_symbolic_shape;
      [ exact Hdom | cbn [p_header_map]; apply pmap_shape_refl ].
  - (* transformer: §11's symbolic half *)
    pose proof (smt_transformer_hdr_shape tt
      {| mc_mem := sh_mem gs; mc_extent := sh_mem_extent gs |}
      (inject_headers (sh_hdr_map gs) ts)) as H.
    cbn [inject_headers t_header_map] in H. exact H.
Qed.

(* [??] reads the TREE, not the map, so [PMap.gss]/[gso] -- which are about
   [!!] and see the default -- do not apply to it.  These are the two
   equations the module-state lookups need. *)
Lemma pmap_set_qq : forall (T : Type) (m : PMap.t T) k (v : T),
  (PMap.set k v m) ?? k = Some v.
Proof. intros T m k v. unfold PMap.set. cbn [snd]. apply PTree.gss. Qed.

Lemma pmap_set_qq_other : forall (T : Type) (m : PMap.t T) k j (v : T),
  j <> k -> (PMap.set k v m) ?? j = m ?? j.
Proof. intros T m k j v H. unfold PMap.set. cbn [snd]. apply PTree.gso. exact H. Qed.

(* [lookup_module] finds a module by its own name, so the name it was asked
   for is the name of what it returns.  Needed because a module stores its
   result in [mod_states] at ITS OWN key, and the induction has to know that
   is the key it just read. *)
Lemma lookup_module_name : forall net lbl m,
  lookup_module net lbl = Some m -> get_mod_name m = lbl.
Proof.
  intros net lbl m H. unfold lookup_module in H.
  apply List.find_some in H as [_ Hb].
  apply posesque_eqb_iff. exact Hb.
Qed.

(* Two module-local states have the same shape when they are the same kind and,
   for a transformer, agree on the two maps [dom_ok_at] reads.  The header map
   is not among them -- it is supplied separately at every module entry. *)
Definition ls_shape (a b : SymbolicModuleState) : Prop :=
  match a, b with
  | TransformerMod x, TransformerMod y =>
      pmap_shape (t_state_map x) (t_state_map y)
      /\ pmap_shape (t_ctrl_map x) (t_ctrl_map y)
  | ParserMod _, ParserMod _ => True
  | DeparserMod _, DeparserMod _ => True
  | _, _ => False
  end.

Lemma ls_shape_refl : forall a, ls_shape a a.
Proof.
  intros [x | x | x]; cbn [ls_shape]; try exact I.
  split; apply pmap_shape_refl.
Qed.

Lemma dom_ok_at_shape : forall f mm h1 h2 l1 l2,
  pmap_shape h1 h2 -> ls_shape l1 l2 ->
  dom_ok_at f mm h2 l2 -> dom_ok_at f mm h1 l1.
Proof.
  intros f mm h1 h2 l1 l2 Hh Hl H.
  destruct mm as [mi pp | mi dd | mi sd cd tt]; cbn [dom_ok_at] in *.
  - eapply parser_extracts_ok_shape; [ exact Hh | exact H ].
  - exact I.
  - destruct l1 as [x | |].
    + destruct l2 as [y | |]; cbn [ls_shape] in Hl; try contradiction.
      destruct Hl as [Hst Hct].
      eapply transformer_dom_ok_shape; [| exact H ].
      apply eval_sym_state_shape. apply ts_shape_inject; assumption.
    + exact I.
    + exact I.
Qed.

(* The domain conditions survive a module.  Two cases: at a key the module did
   not write, the stored state is unchanged and only the header map moved (by
   shape); at its own key the stored state is the one it just produced, whose
   state and ctrl maps it left the shape of. *)
Lemma gs_dom_ok_step : forall net f gs start m ls,
  lookup_module net start = Some m ->
  (mod_states gs) ?? (unwrap start) = Some ls ->
  gs_dom_ok net f gs ->
  gs_dom_ok net f
    (module_update_gs_symbolic m
       (set_module_packet (set_module_header_map ls (sh_hdr_map gs))
          (sh_read_tape gs)) gs).
Proof.
  intros net f gs start m ls Hm Hls Hdom.
  assert (Hd0 : dom_ok_at f m (sh_hdr_map gs) ls) by (apply (Hdom start m ls); assumption).
  pose proof (module_update_symbolic_hdr_shape f gs m ls Hd0) as Hsh.
  intros lbl m' ls' Hm' Hls'.
  destruct (Coqlib.peq (unwrap lbl) (unwrap (get_mod_name m))) as [Heq | Hne].
  - (* the module's own key: it stored what it produced *)
    assert (Hlm : lbl = get_mod_name m) by (apply unwrap_inj; exact Heq).
    pose proof (lookup_module_name net start m Hm) as Hname.
    rewrite Hname in Hlm. subst lbl.
    rewrite Hm in Hm'. injection Hm' as Hm'. subst m'.
    (* nine kind-pairs: the three matching ones store at their own key, the six
       mismatches take the fallback branch and store nothing.  Only the
       transformer pair has a real obligation -- everywhere else [dom_ok_at]
       is [True] or the header shape alone carries it. *)
    destruct m as [mi pp | mi dd | mi sd cd tt];
      cbn [get_mod_name] in Hname; subst mi;
      destruct ls as [b | |];
      unfold module_update_gs_symbolic in Hls'; cbv zeta in Hls';
      cbn [set_module_header_map set_module_packet mod_states
           set_gps_valid set_gps_mod_states set_gps_mem set_gps_mem_extent
           set_gps_shared_headers set_gps_bits_read set_gps_shared_read_tape
           set_gps_shared_write_tape] in Hls';
      first [ rewrite pmap_set_qq in Hls' | rewrite Hls in Hls' ];
      injection Hls' as Hls'; subst ls';
      (eapply dom_ok_at_shape; [ exact Hsh | | exact Hd0 ]);
      cbn [ls_shape];
      first [ exact I | (split; apply pmap_shape_refl) | idtac ].
    (* the transformer pair: its state and ctrl maps keep their shape *)
    split.
    + pose proof (smt_transformer_sv_shape tt
        {| mc_mem := sh_mem gs; mc_extent := sh_mem_extent gs |}
        (inject_headers (sh_hdr_map gs) b)) as H.
      cbn [inject_headers t_state_map] in H. exact H.
    + apply pmap_shape_of_eq.
      apply (smt_transformer_ctrl_eq tt
        {| mc_mem := sh_mem gs; mc_extent := sh_mem_extent gs |}
        (inject_headers (sh_hdr_map gs) b)).
  - (* any other key: the stored state is untouched *)
    assert (Hsame : (mod_states (module_update_gs_symbolic m
                       (set_module_packet (set_module_header_map ls (sh_hdr_map gs))
                          (sh_read_tape gs)) gs)) ?? (unwrap lbl)
                    = (mod_states gs) ?? (unwrap lbl)).
    { destruct m as [mi pp | mi dd | mi sd cd tt]; destruct ls as [b | |];
        unfold module_update_gs_symbolic; cbv zeta;
        cbn [set_module_header_map set_module_packet mod_states
             set_gps_valid set_gps_mod_states set_gps_mem set_gps_mem_extent
             set_gps_shared_headers set_gps_bits_read set_gps_shared_read_tape
             set_gps_shared_write_tape];
        try reflexivity;
        apply pmap_set_qq_other; cbn [get_mod_name] in Hne; exact Hne. }
    rewrite Hsame in Hls'.
    eapply dom_ok_at_shape;
      [ exact Hsh | apply ls_shape_refl | apply (Hdom lbl m' ls'); assumption ].
Qed.

(* The read tape stays a presence-prefix.  Only a parser rewrites it, to its
   own residual, and [ParserCommuteLemmas.pprefix_eval_parser_symbolic] says a
   residual of a prefix is a prefix.  Every other kind leaves it alone.

   This is the invariant that keeps step 7 applicable at the SECOND parser in a
   chain: [eval_parser_commute] needs its packet to be a presence-prefix, and
   after the first parser the tape is whatever that parser left. *)
Lemma module_update_symbolic_pprefix : forall f gs m ls,
  pprefix f (sh_read_tape gs) ->
  pprefix f (sh_read_tape (module_update_gs_symbolic m
    (set_module_packet (set_module_header_map ls (sh_hdr_map gs))
       (sh_read_tape gs)) gs)).
Proof.
  intros f gs m ls H.
  destruct m as [mid pp | mid dd | mid sd cd tt]; destruct ls as [ts | ps | ps];
    unfold module_update_gs_symbolic; cbv zeta;
    cbn [set_module_header_map set_module_packet sh_read_tape
         set_gps_valid set_gps_mod_states set_gps_mem set_gps_mem_extent
         set_gps_shared_headers set_gps_bits_read set_gps_shared_read_tape
         set_gps_shared_write_tape];
    try exact H.
  (* the parser: its residual is a prefix of the tape it was handed *)
  apply pprefix_eval_parser_symbolic. cbn [p_packet]. exact H.
Qed.

(* ==================================================================== *)
(* 19. THE MODULE-STATE KINDS AGREE.                                     *)
(*                                                                       *)
(* The induction's unconditional part was planned as module-state DOMAIN *)
(* agreement.  That is not strong enough, and the reason only shows       *)
(* up on a rejecting run.  Both [module_update_gs_*] dispatch on the      *)
(* module kind and the stored state's kind TOGETHER, and take a fallback  *)
(* branch that writes nothing when they disagree.  So if the two sides    *)
(* ever held different KINDS at one key, one would store its result and   *)
(* the other would not, and the domains would come apart -- after which   *)
(* the two runs can disagree about whether the network completes at all.  *)
(*                                                                       *)
(* Kinds cannot come apart, because each side writes a kind determined by *)
(* the MODULE, and both take the same branch exactly when the kinds       *)
(* already agree.  But that has to be carried, not derived.               *)
(* ==================================================================== *)

(* Concretization preserves the kind, which is how the invariant starts. *)
Lemma ms_kind_agree_concretize : forall sms f,
  ms_kind_agree (PMap.map (fun st => concretize_sym_module_state st f) sms) sms.
Proof.
  intros sms f k.
  unfold PMap.map. cbn [snd]. rewrite PTree.gmap1.
  destruct (PTree.get k (snd sms)) as [b |]; cbn [option_map]; [| exact I].
  destruct b as [x | x | x]; cbn [concretize_sym_module_state ls_kind_agree]; exact I.
Qed.

(* A module writes a kind fixed by the module itself, so one step keeps the
   agreement.  The parser case is where [well_formed_parser] is needed: the
   concrete evaluator must not return [None], or it would take the branch that
   stores nothing while the symbolic side stores its result. *)
Lemma ms_kind_agree_step : forall cgs sgs m cls ls chm cbits shm sbits,
  (match m with ParserModule _ pp => well_formed_parser pp | _ => True end) ->
  ms_kind_agree (mod_states cgs) (mod_states sgs) ->
  ls_kind_agree cls ls ->
  ms_kind_agree
    (mod_states (module_update_gs_concrete m
       (set_module_packet (set_module_header_map cls chm) cbits) cgs))
    (mod_states (module_update_gs_symbolic m
       (set_module_packet (set_module_header_map ls shm) sbits) sgs)).
Proof.
  intros cgs sgs m cls ls chm cbits shm sbits Hwf Hms Hls.
  destruct m as [mid pp | mid dd | mid sd cd tt];
    destruct cls as [cx | cx | cx]; destruct ls as [sx | sx | sx];
    cbn [ls_kind_agree] in Hls; try contradiction;
    unfold module_update_gs_concrete, module_update_gs_symbolic; cbv zeta;
    cbn [set_module_header_map set_module_packet mod_states
         p_header_map p_packet p_cursor
         set_gps_valid set_gps_mod_states set_gps_mem set_gps_mem_extent
         set_gps_shared_headers set_gps_bits_read set_gps_shared_read_tape
         set_gps_shared_write_tape];
    try exact Hms.
  - (* parser: the concrete run completes, by well-formedness *)
    cbn [well_formed_parser] in Hwf.
    destruct (eval_parser_concrete pp
                {| p_header_map := chm; p_packet := cbits; p_cursor := 0 |})
      as [r |] eqn:Hr.
    + (* the [match] on the concrete result is only now resolved, so the
         state projections need reducing a second time *)
      cbn [mod_states set_gps_valid set_gps_mod_states set_gps_bits_read
           set_gps_shared_read_tape set_gps_shared_headers].
      intro k. destruct (Coqlib.peq k (unwrap mid)) as [Heq | Hne].
      { rewrite Heq, !pmap_set_qq. exact I. }
      { rewrite !pmap_set_qq_other by exact Hne. apply Hms. }
    + exfalso. revert Hr. apply eval_parser_no_fuel_starvation; [ exact Hwf | reflexivity ].
  - (* deparser *)
    intro k. destruct (Coqlib.peq k (unwrap mid)) as [Heq | Hne].
    { rewrite Heq, !pmap_set_qq. exact I. }
    { rewrite !pmap_set_qq_other by exact Hne. apply Hms. }
  - (* transformer *)
    intro k. destruct (Coqlib.peq k (unwrap mid)) as [Heq | Hne].
    { rewrite Heq, !pmap_set_qq. exact I. }
    { rewrite !pmap_set_qq_other by exact Hne. apply Hms. }
Qed.

(* ==================================================================== *)
(* 20. ONE MODULE PRESERVES [gs_rel].                                    *)
(*                                                                       *)
(* The last piece of case analysis: three module kinds by two validity   *)
(* cases.  Under validity the incoming [gps_agree] says the concrete     *)
(* state's fields ARE the concretized symbolic ones, so §15's steps      *)
(* apply directly.  Under invalidity nothing is known about the states   *)
(* and nothing needs to be: both flags stay false by §4, and §19 keeps   *)
(* the module-state kinds in step.                                       *)
(* ==================================================================== *)

(* What each kind leaves alone.  Every one of these is a [reflexivity]; they
   are named so the agreement's untouched fields can be carried across a
   module without unfolding it. *)
Lemma tf_keep_c : forall mid sd cd tt ts gs,
  let g := module_update_gs_concrete (TransformerModule mid sd cd tt) (TransformerMod ts) gs in
  sh_read_tape g = sh_read_tape gs /\ sh_bits_read g = sh_bits_read gs
  /\ sh_write_tape g = sh_write_tape gs /\ gps_valid g = gps_valid gs.
Proof. intros. repeat split. Qed.

Lemma tf_keep_s : forall mid sd cd tt ts gs,
  let g := module_update_gs_symbolic (TransformerModule mid sd cd tt) (TransformerMod ts) gs in
  sh_read_tape g = sh_read_tape gs /\ sh_bits_read g = sh_bits_read gs
  /\ sh_write_tape g = sh_write_tape gs /\ gps_valid g = gps_valid gs.
Proof. intros. repeat split. Qed.

Lemma dp_keep_c : forall mid dd ps gs,
  let g := module_update_gs_concrete (DeparserModule mid dd) (DeparserMod ps) gs in
  sh_hdr_map g = sh_hdr_map gs /\ sh_read_tape g = sh_read_tape gs
  /\ sh_bits_read g = sh_bits_read gs /\ sh_mem g = sh_mem gs
  /\ sh_mem_extent g = sh_mem_extent gs /\ gps_valid g = gps_valid gs.
Proof. intros. repeat split. Qed.

Lemma dp_keep_s : forall mid dd ps gs,
  let g := module_update_gs_symbolic (DeparserModule mid dd) (DeparserMod ps) gs in
  sh_hdr_map g = sh_hdr_map gs /\ sh_read_tape g = sh_read_tape gs
  /\ sh_bits_read g = sh_bits_read gs /\ sh_mem g = sh_mem gs
  /\ sh_mem_extent g = sh_mem_extent gs /\ gps_valid g = gps_valid gs.
Proof. intros. repeat split. Qed.

(* A parser leaves the write tape and the memory alone -- on the concrete side
   in BOTH of its branches, which is why this is stated over the [match]. *)
Lemma ps_keep_c : forall mid pp ps gs,
  let g := module_update_gs_concrete (ParserModule mid pp) (ParserMod ps) gs in
  sh_write_tape g = sh_write_tape gs /\ sh_mem g = sh_mem gs
  /\ sh_mem_extent g = sh_mem_extent gs.
Proof.
  intros mid pp ps gs g. unfold g, module_update_gs_concrete. cbv zeta.
  destruct (eval_parser_concrete pp ps); repeat split.
Qed.

Lemma ps_keep_s : forall mid pp ps gs,
  let g := module_update_gs_symbolic (ParserModule mid pp) (ParserMod ps) gs in
  sh_write_tape g = sh_write_tape gs /\ sh_mem g = sh_mem gs
  /\ sh_mem_extent g = sh_mem_extent gs.
Proof. intros. repeat split. Qed.

(* --- the transformer, under validity --- *)
Theorem transformer_step_agree : forall mid sd cd tt ts f cgs sgs,
  gps_agree cgs (concretize_sym_modnet_state sgs f) ->
  transformer_dom_ok tt (eval_sym_state (inject_headers (sh_hdr_map sgs) ts) f) ->
  gps_agree
    (module_update_gs_concrete (TransformerModule mid sd cd tt)
      (set_module_packet
        (set_module_header_map (TransformerMod (eval_sym_state ts f)) (sh_hdr_map cgs))
        (sh_read_tape cgs)) cgs)
    (concretize_sym_modnet_state
      (module_update_gs_symbolic (TransformerModule mid sd cd tt)
        (set_module_packet
          (set_module_header_map (TransformerMod ts) (sh_hdr_map sgs))
          (sh_read_tape sgs)) sgs) f).
Proof.
  intros mid sd cd tt ts f cgs sgs Hag Hdom.
  destruct Hag as [Hh [Hr [Hb [Hw [Hm [He [Hms Hv]]]]]]].
  rewrite cz_hdr in Hh. rewrite cz_read in Hr. rewrite cz_bits in Hb.
  rewrite cz_write in Hw.
  (* the concrete module-local state is the concretization of the symbolic one *)
  cbn [set_module_header_map set_module_packet].
  rewrite Hh, inject_headers_commute.
  destruct (transformer_mod_step mid sd cd tt (inject_headers (sh_hdr_map sgs) ts)
              f cgs sgs Hm He Hms Hdom) as [Shdr [Sms [Smem Sext]]].
  cbn [inject_headers t_header_map] in Shdr, Sms, Smem, Sext.
  unfold gps_agree.
  (* the four fields a transformer leaves alone travel on the incoming
     agreement; the four it writes come from §15 *)
  destruct (tf_keep_c mid sd cd tt
              (eval_sym_state (inject_headers (sh_hdr_map sgs) ts) f) cgs)
    as [Cr [Cb [Cw Cv]]].
  destruct (tf_keep_s mid sd cd tt (inject_headers (sh_hdr_map sgs) ts) sgs)
    as [Sr [Sb [Sw Sv]]].
  repeat split.
  - exact Shdr.
  - rewrite Cr, cz_read, Sr. exact Hr.
  - rewrite Cb, cz_bits, Sb. exact Hb.
  - rewrite Cw, cz_write, Sw. exact Hw.
  - exact Smem.
  - exact Sext.
  - exact Sms.
  - rewrite Cv, cz_valid, Sv. exact Hv.
Qed.

(* --- the deparser, under validity ---
   [set_module_packet] and [set_module_header_map] between them overwrite every
   field of a parser-shaped module state, so the stored payload is discarded
   and only its KIND matters.  That is why these two take an arbitrary [cx]
   and [sx] rather than requiring one to concretize to the other. *)
Theorem deparser_step_agree : forall mid dd cx sx f cgs sgs,
  gps_agree cgs (concretize_sym_modnet_state sgs f) ->
  gps_agree
    (module_update_gs_concrete (DeparserModule mid dd)
      (set_module_packet (set_module_header_map (DeparserMod cx) (sh_hdr_map cgs))
        (sh_read_tape cgs)) cgs)
    (concretize_sym_modnet_state
      (module_update_gs_symbolic (DeparserModule mid dd)
        (set_module_packet (set_module_header_map (DeparserMod sx) (sh_hdr_map sgs))
          (sh_read_tape sgs)) sgs) f).
Proof.
  intros mid dd cx sx f cgs sgs Hag.
  pose proof Hag as [Hh [Hr [Hb [Hw [Hm [He [Hms Hv]]]]]]].
  rewrite cz_hdr in Hh. rewrite cz_read in Hr. rewrite cz_bits in Hb.
  rewrite cz_write in Hw. rewrite cz_ms in Hms. rewrite cz_valid in Hv.
  cbn [set_module_header_map set_module_packet p_header_map p_packet p_cursor].
  rewrite Hh.
  destruct (deparser_mod_step mid dd f cgs sgs (sh_hdr_map sgs)
              (sh_read_tape cgs) (sh_read_tape sgs)
              ltac:(rewrite cz_write; exact Hw)
              ltac:(rewrite cz_ms; exact Hms)) as [Dw Dms].
  destruct (dp_keep_c mid dd
              {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map sgs);
                 p_packet := sh_read_tape cgs; p_cursor := 0 |} cgs)
    as [Ch [Cr [Cb [Cm [Ce Cv]]]]].
  destruct (dp_keep_s mid dd
              {| p_header_map := sh_hdr_map sgs;
                 p_packet := sh_read_tape sgs; p_cursor := 0 |} sgs)
    as [Sh [Sr [Sb [Sm [Se Sv]]]]].
  unfold gps_agree. repeat split.
  - rewrite Ch, cz_hdr, Sh, <- cz_hdr. exact Hh.
  - rewrite Cr, cz_read, Sr. exact Hr.
  - rewrite Cb, cz_bits, Sb. exact Hb.
  - exact Dw.
  - intro k. rewrite Cm, cz_mem, Sm, <- cz_mem. apply Hm.
  - intro k. rewrite Ce, cz_ext, Se, <- cz_ext. apply He.
  - exact Dms.
  - rewrite Cv, cz_valid, Sv. exact Hv.
Qed.

(* --- the parser ---
   Two conclusions, not one, and the split is the whole point: the flag agrees
   UNCONDITIONALLY, which is what carries the verdict past a rejecting parser,
   while the rest is available only when the result is valid. *)
Theorem parser_step_agree : forall mid pp cx sx f cgs sgs m0,
  well_formed_parser pp ->
  pprefix f (sh_read_tape sgs) ->
  parser_extracts_ok pp m0 ->
  pmap_shape (sh_hdr_map sgs) m0 ->
  gps_agree cgs (concretize_sym_modnet_state sgs f) ->
  let gc := module_update_gs_concrete (ParserModule mid pp)
              (set_module_packet (set_module_header_map (ParserMod cx) (sh_hdr_map cgs))
                (sh_read_tape cgs)) cgs in
  let gsym := module_update_gs_symbolic (ParserModule mid pp)
                (set_module_packet (set_module_header_map (ParserMod sx) (sh_hdr_map sgs))
                  (sh_read_tape sgs)) sgs in
  gps_valid gc = gps_valid (concretize_sym_modnet_state gsym f)
  /\ (gps_valid gc = true -> gps_agree gc (concretize_sym_modnet_state gsym f)).
Proof.
  intros mid pp cx sx f cgs sgs m0 Hwf Hpp Hok Hshape Hag gc gsym.
  pose proof Hag as [Hh [Hr [Hb [Hw [Hm [He [Hms Hv]]]]]]].
  rewrite cz_hdr in Hh. rewrite cz_read in Hr. rewrite cz_bits in Hb.
  rewrite cz_write in Hw. rewrite cz_ms in Hms. rewrite cz_valid in Hv.
  unfold gc, gsym.
  cbn [set_module_header_map set_module_packet p_header_map p_packet p_cursor].
  rewrite Hh, Hr.
  destruct (parser_mod_step mid pp f cgs sgs (sh_hdr_map sgs) (sh_read_tape sgs) m0
              Hwf Hpp Hok Hshape Hv
              ltac:(rewrite cz_bits; exact Hb)
              ltac:(rewrite cz_ms; exact Hms)) as [Pflag Prest].
  destruct (ps_keep_c mid pp
              {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map sgs);
                 p_packet := present_bits (sh_read_tape sgs) f; p_cursor := 0 |} cgs)
    as [Cw [Cm Ce]].
  destruct (ps_keep_s mid pp
              {| p_header_map := sh_hdr_map sgs;
                 p_packet := sh_read_tape sgs; p_cursor := 0 |} sgs)
    as [Sw [Sm Se]].
  split; [exact Pflag |].
  intro Hvf. destruct (Prest Hvf) as [Phdr [Pread [Pbits Pms]]].
  unfold gps_agree. repeat split.
  - exact Phdr.
  - exact Pread.
  - exact Pbits.
  - rewrite Cw, cz_write, Sw. exact Hw.
  - intro k. rewrite Cm, cz_mem, Sm, <- cz_mem. apply Hm.
  - intro k. rewrite Ce, cz_ext, Se, <- cz_ext. apply He.
  - exact Pms.
  - exact Pflag.
Qed.

Lemma pmap_map_qq : forall (A B : Type) (g : A -> B) (m : PMap.t A) k v,
  m ?? k = Some v -> (PMap.map g m) ?? k = Some (g v).
Proof.
  intros A B g m k v H. unfold PMap.map. cbn [snd]. rewrite PTree.gmap1, H.
  reflexivity.
Qed.

(* One module preserves the whole relation. *)
Theorem module_step_rel : forall net f cgs sgs m cls ls start,
  lookup_module net start = Some m ->
  (mod_states sgs) ?? (unwrap start) = Some ls ->
  (mod_states cgs) ?? (unwrap start) = Some cls ->
  (match m with ParserModule _ pp => well_formed_parser pp | _ => True end) ->
  gs_dom_ok net f sgs ->
  pprefix f (sh_read_tape sgs) ->
  gs_rel f cgs sgs ->
  gs_rel f
    (module_update_gs_concrete m
      (set_module_packet (set_module_header_map cls (sh_hdr_map cgs))
        (sh_read_tape cgs)) cgs)
    (module_update_gs_symbolic m
      (set_module_packet (set_module_header_map ls (sh_hdr_map sgs))
        (sh_read_tape sgs)) sgs).
Proof.
  intros net f cgs sgs m cls ls start Hm Hls Hcls Hwf Hdom Hpp Hrel.
  pose proof Hrel as [Hflag [Hkind Hagree]].
  assert (Hlk : ls_kind_agree cls ls)
    by (eapply ms_kind_agree_at; eassumption).
  assert (Hd0 : dom_ok_at f m (sh_hdr_map sgs) ls)
    by (apply (Hdom start m ls); assumption).
  split; [| split; [ eapply ms_kind_agree_step; eassumption |]].
  - (* ---- the flag ---- *)
    destruct (gps_valid cgs) eqn:Hv.
    + (* valid: only a parser and the kind-mismatch fallback write it *)
      destruct m as [mid pp | mid dd | mid sd cd tt];
        destruct cls as [cx | cx | cx]; destruct ls as [sx | sx | sx];
        cbn [ls_kind_agree] in Hlk; try contradiction;
        try reflexivity.
      * (* parser *)
        refine (proj1 (parser_step_agree mid pp cx sx f cgs sgs (sh_hdr_map sgs)
                  Hwf Hpp _ (pmap_shape_refl _ _) (Hagree eq_refl))).
        exact Hd0.
      * (* deparser: leaves the flag alone on both sides *)
        cbn [module_update_gs_concrete module_update_gs_symbolic
             set_module_header_map set_module_packet gps_valid cvv
             set_gps_mod_states set_gps_shared_write_tape set_gps_mem
             set_gps_mem_extent set_gps_shared_headers].
        rewrite Hv. exact Hflag.
      * (* transformer: likewise *)
        cbn [module_update_gs_concrete module_update_gs_symbolic
             set_module_header_map set_module_packet gps_valid cvv
             set_gps_mod_states set_gps_mem set_gps_mem_extent
             set_gps_shared_headers].
        rewrite Hv. exact Hflag.
    + (* invalid: neither side can clear the flag *)
      rewrite (module_update_concrete_invalid _ _ _ Hv).
      symmetry. apply module_update_symbolic_invalid.
      rewrite <- Hflag. reflexivity.
  - (* ---- the agreement, under the NEW validity ---- *)
    intro Hvf.
    assert (Hv : gps_valid cgs = true).
    { destruct (gps_valid cgs) eqn:E; [reflexivity |].
      rewrite (module_update_concrete_invalid _ _ _ E) in Hvf. discriminate. }
    pose proof (Hagree Hv) as Hag.
    pose proof Hag as [_ [_ [_ [_ [_ [_ [Hms _]]]]]]]. rewrite cz_ms in Hms.
    destruct m as [mid pp | mid dd | mid sd cd tt];
      destruct cls as [cx | cx | cx]; destruct ls as [sx | sx | sx];
      cbn [ls_kind_agree] in Hlk; try contradiction;
      try (cbn [gps_valid module_update_gs_concrete set_gps_valid
                set_module_header_map set_module_packet] in Hvf;
           discriminate).
    + (* parser *)
      refine (proj2 (parser_step_agree mid pp cx sx f cgs sgs (sh_hdr_map sgs)
                Hwf Hpp Hd0 (pmap_shape_refl _ _) Hag) Hvf).
    + (* deparser *)
      apply deparser_step_agree. exact Hag.
    + (* transformer: its stored state IS the concretization of the symbolic one *)
      assert (Hcx : cx = eval_sym_state sx f).
      { assert (Hq : (mod_states cgs) ?? (unwrap start)
                     = Some (concretize_sym_module_state (TransformerMod sx) f))
          by (rewrite Hms;
              exact (pmap_map_qq _ _ (fun st => concretize_sym_module_state st f)
                       (mod_states sgs) (unwrap start) (TransformerMod sx) Hls)).
        assert (Heq2 : TransformerMod cx
                       = concretize_sym_module_state (TransformerMod sx) f)
          by congruence.
        cbn [concretize_sym_module_state] in Heq2.
        injection Heq2 as Heq2. exact Heq2. }
      subst cx. apply transformer_step_agree. exact Hag. exact Hd0.
Qed.

(* ==================================================================== *)
(* 21. THE NETWORK INDUCTION.                                            *)
(*                                                                       *)
(* Ordinary induction on fuel, given §17's destructuring.  Six things    *)
(* travel: the relation itself, the module-state kinds (inside it), the  *)
(* domain conditions, the read tape's presence-prefix, and the two       *)
(* extent defaults.  Every one of them has its preservation lemma above. *)
(* ==================================================================== *)

Definition net_parsers_wf (net : ModuleNetwork) : Prop :=
  forall m, In m (net_modules net) ->
    match m with ParserModule _ pp => well_formed_parser pp | _ => True end.

Lemma lookup_module_in : forall net lbl m,
  lookup_module net lbl = Some m -> In m (net_modules net).
Proof.
  intros net lbl m H. unfold lookup_module in H.
  apply List.find_some in H as [H _]. exact H.
Qed.

Theorem network_commute : forall fuel net f cgs sgs start sgs_f,
  no_fan_out net ->
  net_parsers_wf net ->
  gs_dom_ok net f sgs ->
  pprefix f (sh_read_tape sgs) ->
  fst (sh_mem_extent cgs) = mk_int u64 0 ->
  eval_smt_arith (fst (sh_mem_extent sgs)) f = mk_int u64 0 ->
  gs_rel f cgs sgs ->
  eval_network_from_symbolic net start (sh_hdr_map sgs) (sh_read_tape sgs) sgs fuel
    = Some sgs_f ->
  exists cgs_f,
    eval_network_from_concrete net start (sh_hdr_map cgs) (sh_read_tape cgs) cgs fuel
      = Some cgs_f
    /\ gs_rel f cgs_f sgs_f
    /\ fst (sh_mem_extent cgs_f) = mk_int u64 0
    /\ eval_smt_arith (fst (sh_mem_extent sgs_f)) f = mk_int u64 0.
Proof.
  induction fuel as [| fuel IH];
    intros net f cgs sgs start sgs_f Hnf Hwf Hdom Hpp Hce Hse Hrel Hsym;
    [ discriminate |].
  rewrite network_symbolic_step in Hsym.
  destruct (lookup_module net start) as [m |] eqn:Hm; [| discriminate].
  destruct ((mod_states sgs) ?? (unwrap start)) as [ls |] eqn:Hls; [| discriminate].
  (* the concrete lookup succeeds too: the kinds agree, hence the domains *)
  pose proof Hrel as [Hflag [Hkind Hagree]].
  destruct (ms_kind_agree_some _ _ _ _ Hkind Hls) as [cls [Hcls _]].
  assert (Hwfm : match m with ParserModule _ pp => well_formed_parser pp | _ => True end)
    by (apply Hwf; eapply lookup_module_in; exact Hm).
  (* one module runs on each side *)
  set (sgs' := module_update_gs_symbolic m
                 (set_module_packet (set_module_header_map ls (sh_hdr_map sgs))
                    (sh_read_tape sgs)) sgs) in *.
  set (cgs' := module_update_gs_concrete m
                 (set_module_packet (set_module_header_map cls (sh_hdr_map cgs))
                    (sh_read_tape cgs)) cgs) in *.
  assert (Hrel' : gs_rel f cgs' sgs')
    by (eapply module_step_rel; eassumption).
  assert (Hce' : fst (sh_mem_extent cgs') = mk_int u64 0)
    by (apply module_update_concrete_extent_default; exact Hce).
  assert (Hse' : eval_smt_arith (fst (sh_mem_extent sgs')) f = mk_int u64 0)
    by (apply module_update_symbolic_extent_default; exact Hse).
  assert (Hdom' : gs_dom_ok net f sgs')
    by (eapply gs_dom_ok_step; eassumption).
  assert (Hpp' : pprefix f (sh_read_tape sgs'))
    by (apply module_update_symbolic_pprefix; exact Hpp).
  (* the fold is at most one step *)
  destruct (downstream_cases net start Hnf) as [Hd | [dst Hd]];
    rewrite Hd in Hsym; cbn [List.fold_left] in Hsym.
  - (* this module is the sink *)
    injection Hsym as Hsym. subst sgs_f.
    exists cgs'. split; [| split; [exact Hrel' | split; [exact Hce' | exact Hse']]].
    rewrite (network_concrete_stop net start _ _ cgs fuel m cls Hm Hcls Hd).
    reflexivity.
  - (* one downstream module: recurse *)
    destruct (IH net f cgs' sgs' dst sgs_f Hnf Hwf Hdom' Hpp' Hce' Hse' Hrel' Hsym)
      as [cgs_f [Hrun [Hr2 [Hc2 Hs2]]]].
    exists cgs_f. split; [| split; [exact Hr2 | split; [exact Hc2 | exact Hs2]]].
    rewrite (network_concrete_go net start _ _ cgs fuel m cls dst Hm Hcls Hd).
    cbv zeta. exact Hrun.
Qed.

Lemma gps_agree_refl : forall c, gps_agree c c.
Proof.
  intro c. unfold gps_agree.
  repeat split; try reflexivity; intro k; reflexivity.
Qed.

(* ==================================================================== *)
(* 22. THE BRIDGE, MODULO ITS ENTRY CONDITIONS.                          *)
(*                                                                       *)
(* [SmtModuleQuery.eval_general_program_commute]'s conclusion, from five  *)
(* hypotheses about the state the run starts from.  Three of them are     *)
(* about that state rather than about the program, and that is not        *)
(* incidental: over an ARBITRARY symbolic state the conclusion is false   *)
(* (see the comment on [eval_general_program_commute] for the read-tape   *)
(* counterexample), so they cannot be dropped.                            *)
(*                                                                        *)
(* §23 discharges all five at [init_general_symbolic_state], which is     *)
(* what the checker passes.                                               *)
(* ==================================================================== *)
Theorem program_commute_full : forall p f s s_f,
  no_fan_out (get_network_from_general p) ->
  net_parsers_wf (get_network_from_general p) ->
  gs_dom_ok (get_network_from_general p) f s ->
  pprefix f (sh_read_tape s) ->
  eval_smt_arith (fst (sh_mem_extent s)) f = mk_int u64 0 ->
  eval_general_program_symbolic p s = Some s_f ->
  exists c_f,
    eval_general_program_concrete p (concretize_sym_modnet_state s f) = Some c_f /\
    gps_valid c_f = gps_valid (concretize_sym_modnet_state s_f f) /\
    (gps_valid c_f = true -> gps_agree c_f (concretize_sym_modnet_state s_f f)).
Proof.
  intros p f s s_f Hnf Hwf Hdom Hpp Hse Hprog.
  (* the symbolic network run, out of the program wrapper *)
  pose proof Hprog as Hprog'.
  unfold eval_general_program_symbolic in Hprog'. cbv zeta in Hprog'.
  destruct ((mod_states s) ?? (unwrap (start_module (get_network_from_general p))))
    as [st |] eqn:Hms; [| discriminate].
  destruct (eval_network_from_symbolic (get_network_from_general p)
              (start_module (get_network_from_general p))
              (sh_hdr_map s) (sh_read_tape s) s
              (List.length (net_modules (get_network_from_general p))))
    as [sgs_f |] eqn:Hsym; [| discriminate].
  (* the initial states are related: concretization is the identity on the
     relation's three clauses *)
  assert (Hrel : gs_rel f (concretize_sym_modnet_state s f) s).
  { split; [reflexivity | split ].
    - rewrite cz_ms. apply ms_kind_agree_concretize.
    - intros _. apply gps_agree_refl. }
  assert (Hce : fst (sh_mem_extent (concretize_sym_modnet_state s f)) = mk_int u64 0)
    by (rewrite cz_ext, pmap_map_default; exact Hse).
  destruct (network_commute _ _ f (concretize_sym_modnet_state s f) s _ _
              Hnf Hwf Hdom Hpp Hce Hse Hrel Hsym)
    as [cgs_f [Hconc [Hrel_f [Hce_f Hse_f]]]].
  destruct Hrel_f as [Hflag_f [_ Hag_f]].
  eapply program_commute_from_network;
    [ exact Hsym | exact Hconc | exact Hflag_f | exact Hce_f | exact Hse_f
    | exact Hag_f | exact Hprog ].
Qed.

(* ==================================================================== *)
(* 23. THE ENTRY CONDITIONS, AT THE INITIAL STATE.                       *)
(*                                                                       *)
(* §22 reduced the bridge to five hypotheses about the state the run     *)
(* starts from.  This section discharges them for the state              *)
(* [init_general_symbolic_state] builds -- which is what                 *)
(* [modnet_equivalence_checker_sound] actually passes.                   *)
(*                                                                       *)
(* None of it is about the semantics.  It is about the SEEDING: that     *)
(* [collect_write_headers] really does hold every header any module      *)
(* writes, that [force_keys] over [collect_module_state_targets] really  *)
(* does hold every state variable a transformer writes, and that the     *)
(* module-state fold stores each module's state at its own key.          *)
(* ==================================================================== *)

(* A fold of [PMap.set] binds every key it is given, and never unbinds one. *)
Lemma pmap_fold_set_binds : forall (T C : Type) (key : C -> positive)
    (val : C -> PMap.t T -> T) (l : list C) (m : PMap.t T) k,
  (In k (List.map key l) \/ m ?? k <> None) ->
  (List.fold_left (fun acc c => PMap.set (key c) (val c acc) acc) l m) ?? k <> None.
Proof.
  intros T C key val l. induction l as [| c r IH]; intros m k H; cbn [List.fold_left].
  - destruct H as [H | H]; [ destruct H | exact H ].
  - apply IH. cbn [List.map] in H. destruct H as [[Heq | Hin] | Hm].
    + right. rewrite <- Heq, pmap_set_qq. discriminate.
    + left. exact Hin.
    + right. destruct (Coqlib.peq k (key c)) as [-> | Hne].
      * rewrite pmap_set_qq. discriminate.
      * rewrite pmap_set_qq_other by exact Hne. exact Hm.
Qed.

(* ...and leaves alone every key it is not given. *)
Lemma pmap_fold_set_untouched : forall (T C : Type) (key : C -> positive)
    (val : C -> T) (l : list C) (m : PMap.t T) k,
  ~ In k (List.map key l) ->
  (List.fold_left (fun acc c => PMap.set (key c) (val c) acc) l m) ?? k = m ?? k.
Proof.
  intros T C key val l. induction l as [| c r IH]; intros m k H; cbn [List.fold_left];
    [reflexivity |].
  cbn [List.map] in H.
  rewrite IH by (intro Hc; apply H; right; exact Hc).
  apply pmap_set_qq_other. intro Hc. apply H. left. symmetry. exact Hc.
Qed.

(* With distinct keys, the fold stores each element's own value at its own key. *)
Lemma pmap_fold_set_get : forall (T C : Type) (key : C -> positive)
    (val : C -> T) (l : list C) (m : PMap.t T) c,
  Coqlib.list_norepet (List.map key l) ->
  In c l ->
  (List.fold_left (fun acc c' => PMap.set (key c') (val c') acc) l m) ?? (key c)
  = Some (val c).
Proof.
  intros T C key val l. induction l as [| a r IH]; intros m c Hnr Hin; [destruct Hin |].
  cbn [List.map] in Hnr. inversion Hnr as [| x xs Hna Hnr' Heq]; subst.
  cbn [List.fold_left]. destruct Hin as [-> | Hin].
  - rewrite pmap_fold_set_untouched by exact Hna. apply pmap_set_qq.
  - apply IH; assumption.
Qed.

(* --- the two seeded maps hold what the collectors gathered --- *)

Lemma seed_header_syms_dom : forall hts hs h,
  In h hs -> (seed_header_syms hts hs) ?? (unwrap h) <> None.
Proof.
  intros hts hs h Hin. unfold seed_header_syms.
  apply (pmap_fold_set_binds _ _ (fun x => unwrap x)
           (fun x _ => match lookup_header_type hts x with
                       | Some ty => SmtCast u64 ty (SmtVarVal (seed_name "" (SVHdr (unwrap x))))
                       | None => SmtUninit
                       end)).
  left. apply List.in_map. exact Hin.
Qed.

Lemma force_keys_dom : forall (T : Type) (ks : list positive) (m : PMap.t T) k,
  In k ks -> (force_keys ks m) ?? k <> None.
Proof.
  intros T ks m k Hin. unfold force_keys.
  apply (pmap_fold_set_binds _ _ (fun x : positive => x) (fun x acc => acc !! x)).
  left. rewrite List.map_id. exact Hin.
Qed.

(* --- [extract_all_targets] really does gather every op's target --- *)

Local Notation eat_step :=
  (fun (acc : list State * list Header) (op : HdrOp) =>
     let (state_vars, headers) := extract_targets op in
     (state_vars ++ fst acc, headers ++ snd acc)).

Lemma eat_mono : forall ops acc,
  (forall x, In x (fst acc) -> In x (fst (List.fold_left eat_step ops acc)))
  /\ (forall x, In x (snd acc) -> In x (snd (List.fold_left eat_step ops acc))).
Proof.
  induction ops as [| op r IH]; intros acc; cbn [List.fold_left];
    [split; intros x H; exact H |].
  destruct (IH (let (sv, hd) := extract_targets op in (sv ++ fst acc, hd ++ snd acc)))
    as [IH1 IH2].
  split; intros x H.
  - apply IH1. destruct (extract_targets op) as [sv hd]. cbn [fst].
    apply List.in_or_app. right. exact H.
  - apply IH2. destruct (extract_targets op) as [sv hd]. cbn [snd].
    apply List.in_or_app. right. exact H.
Qed.

Lemma eat_in : forall ops op acc,
  In op ops ->
  (forall x, In x (fst (extract_targets op)) ->
     In x (fst (List.fold_left eat_step ops acc)))
  /\ (forall x, In x (snd (extract_targets op)) ->
       In x (snd (List.fold_left eat_step ops acc))).
Proof.
  induction ops as [| a r IH]; intros op acc Hin; [destruct Hin |].
  cbn [List.fold_left]. destruct Hin as [-> | Hin].
  - destruct (eat_mono r (let (sv, hd) := extract_targets op in
                            (sv ++ fst acc, hd ++ snd acc))) as [M1 M2].
    split; intros x H.
    + apply M1. destruct (extract_targets op) as [sv hd]. cbn [fst] in *.
      apply List.in_or_app. left. exact H.
    + apply M2. destruct (extract_targets op) as [sv hd]. cbn [snd] in *.
      apply List.in_or_app. left. exact H.
  - apply IH. exact Hin.
Qed.

Lemma extract_all_targets_state : forall ops op sv,
  In op ops -> In sv (fst (extract_targets op)) ->
  In sv (fst (extract_all_targets ops)).
Proof.
  intros ops op sv Hop Hsv. unfold extract_all_targets.
  exact (proj1 (eat_in ops op ([], []) Hop) sv Hsv).
Qed.

Lemma extract_all_targets_hdr : forall ops op h,
  In op ops -> In h (snd (extract_targets op)) ->
  In h (snd (extract_all_targets ops)).
Proof.
  intros ops op h Hop Hh. unfold extract_all_targets.
  exact (proj2 (eat_in ops op ([], []) Hop) h Hh).
Qed.

(* --- [parser_headers] gathers every extraction target --- *)

Local Notation ph_sel_step :=
  (fun (acc : list Header) (c : SelectCase) =>
     match sc_origin c with SelHdr h _ _ => h :: acc | Peek _ _ => acc end).

Local Notation ph_step :=
  (fun (acc : list Header) (d : ParserStateDef) =>
     let acc' := match psd_action d with
                 | Some (ExtractOpConstructor h _ _) => h :: acc
                 | _ => acc
                 end in
     match psd_trans d with
     | Unconditional _ => acc'
     | Select cases _ => List.fold_left ph_sel_step cases acc'
     end).

Lemma ph_sel_mono : forall cases acc x,
  In x acc -> In x (List.fold_left ph_sel_step cases acc).
Proof.
  induction cases as [| c r IH]; intros acc x H; cbn [List.fold_left]; [exact H |].
  apply IH. destruct (sc_origin c); [right |]; exact H.
Qed.

Lemma ph_mono : forall ds acc x,
  In x acc -> In x (List.fold_left ph_step ds acc).
Proof.
  induction ds as [| d r IH]; intros acc x H; cbn [List.fold_left]; [exact H |].
  apply IH.
  destruct (psd_trans d); [| apply ph_sel_mono];
    destruct (psd_action d) as [[ | h w ty] |]; try exact H; right; exact H.
Qed.

Lemma ph_in : forall ds d acc h w ty,
  In d ds -> psd_action d = Some (ExtractOpConstructor h w ty) ->
  In h (List.fold_left ph_step ds acc).
Proof.
  induction ds as [| a r IH]; intros d acc h w ty Hin Hact; [destruct Hin |].
  cbn [List.fold_left]. destruct Hin as [-> | Hin];
    [| eapply IH; eassumption ].
  apply ph_mono. rewrite Hact.
  destruct (psd_trans d); [left; reflexivity | apply ph_sel_mono; left; reflexivity].
Qed.

Lemma parser_headers_extract : forall pr d h w ty,
  In d (parser_states pr) -> psd_action d = Some (ExtractOpConstructor h w ty) ->
  In h (parser_headers pr).
Proof.
  intros pr d h w ty Hin Hact. unfold parser_headers.
  eapply ph_in; eassumption.
Qed.

(* --- lifting to the per-module collectors --- *)

Lemma collect_module_headers_tf : forall mid sd cd tt rule op h,
  In rule tt -> In op (rule_ops rule) -> In h (snd (extract_targets op)) ->
  In h (collect_module_headers (TransformerModule mid sd cd tt)).
Proof.
  intros mid sd cd tt rule op h Hr Hop Hh.
  cbn [collect_module_headers]. apply List.in_flat_map. exists rule. split; [exact Hr |].
  destruct rule as [[mp ops] | [mp ops]]; cbn [rule_ops] in Hop;
    eapply extract_all_targets_hdr; eassumption.
Qed.

Lemma collect_module_state_targets_tf : forall mid sd cd tt rule op sv,
  In rule tt -> In op (rule_ops rule) -> In sv (fst (extract_targets op)) ->
  In sv (collect_module_state_targets (TransformerModule mid sd cd tt)).
Proof.
  intros mid sd cd tt rule op sv Hr Hop Hsv.
  cbn [collect_module_state_targets]. apply List.in_flat_map.
  exists rule. split; [exact Hr |].
  destruct rule as [[mp ops] | [mp ops]]; cbn [rule_ops] in Hop;
    eapply extract_all_targets_state; eassumption.
Qed.

Lemma collect_write_headers_in : forall mods m h,
  In m mods -> In h (collect_module_headers m) -> In h (collect_write_headers mods).
Proof.
  intros mods m h Hm Hh. unfold collect_write_headers.
  apply List.in_flat_map. exists m. split; assumption.
Qed.

(* --- the module-state fold stores each module at its own key --- *)

Lemma init_mod_states_get : forall p pf m,
  mod_names_unique (get_network_from_general p) ->
  In m (net_modules (get_network_from_general p)) ->
  (mod_states (init_general_symbolic_state pf p)) ?? (unwrap (get_mod_name m))
  = Some (init_sym_mod_state pf m).
Proof.
  intros p pf m Hnr Hin.
  cbn [mod_states init_general_symbolic_state].
  apply (pmap_fold_set_get _ _ (fun x => unwrap (get_mod_name x))
           (init_sym_mod_state pf)); [| exact Hin].
  (* distinct names give distinct keys, [unwrap] being injective *)
  unfold mod_names_unique in Hnr.
  replace (List.map (fun x => unwrap (get_mod_name x))
             (net_modules (get_network_from_general p)))
    with (List.map unwrap
           (List.map get_mod_name (net_modules (get_network_from_general p))))
    by (rewrite List.map_map; reflexivity).
  apply Coqlib.list_map_norepet; [exact Hnr |].
  intros x y _ _ Hne Hc. apply Hne. apply unwrap_inj. exact Hc.
Qed.

(* --- the domain condition holds at the initial state --- *)

(* [op_dom_ok] of an injected, concretization-shaped state, in terms of the two
   maps it actually reads.  Stated this way so the caller never has to write
   the seeded [TransformerState] record out. *)
Lemma op_dom_ok_of_maps : forall f op (ts : SymbolicTransformerState) H,
  (forall tgt, In tgt (snd (extract_targets op)) -> H ?? (unwrap tgt) <> None) ->
  (forall tgt, In tgt (fst (extract_targets op)) ->
     (t_state_map ts) ?? (unwrap tgt) <> None) ->
  op_dom_ok op (eval_sym_state (inject_headers H ts) f).
Proof.
  intros f op ts H Hh Hs.
  assert (Hhm : t_header_map (eval_sym_state (inject_headers H ts) f)
                = PMap.map (fun e => eval_smt_arith e f) H)
    by (rewrite eval_sym_state_hdr; cbn [inject_headers t_header_map]; reflexivity).
  assert (Hsm : t_state_map (eval_sym_state (inject_headers H ts) f)
                = PMap.map (fun e => eval_smt_arith e f) (t_state_map ts))
    by (rewrite eval_sym_state_sv; cbn [inject_headers t_state_map]; reflexivity).
  destruct op; cbn [op_dom_ok]; try exact I;
    [ rewrite Hsm | rewrite Hhm | rewrite Hsm | rewrite Hhm
    | rewrite Hhm | rewrite Hsm ];
    intro Hc; apply (proj1 (pmap_map_dom _ _ _ _ _)) in Hc;
    solve [ eapply Hh; [ cbn [extract_targets snd]; left; reflexivity | exact Hc ]
          | eapply Hs; [ cbn [extract_targets fst]; left; reflexivity | exact Hc ] ].
Qed.

Theorem init_gs_dom_ok : forall p pf f,
  mod_names_unique (get_network_from_general p) ->
  gs_dom_ok (get_network_from_general p) f (init_general_symbolic_state pf p).
Proof.
  intros p pf f Hnr lbl m ls Hm Hls.
  pose proof (lookup_module_in _ _ _ Hm) as Hin.
  pose proof (lookup_module_name _ _ _ Hm) as Hname.
  (* the stored state is this module's own seed *)
  rewrite <- Hname in Hls.
  rewrite (init_mod_states_get p pf m Hnr Hin) in Hls.
  injection Hls as Hls. subst ls.
  (* the seeded header map holds every header any module writes *)
  assert (Hhdr : forall h, In h (collect_module_headers m) ->
            (sh_hdr_map (init_general_symbolic_state pf p)) ?? (unwrap h) <> None).
  { intros h Hh. cbn [sh_hdr_map init_general_symbolic_state].
    apply seed_header_syms_dom. eapply collect_write_headers_in; eassumption. }
  destruct m as [mid pp | mid dd | mid sd cd tt];
    unfold init_sym_mod_state; cbv zeta; cbn [dom_ok_at].
  - (* parser: every extraction target is a write header *)
    unfold parser_extracts_ok. rewrite List.Forall_forall. intros d Hd.
    destruct (psd_action d) as [[w | h w ty] |] eqn:Ha; try exact I.
    apply Hhdr. cbn [collect_module_headers]. eapply parser_headers_extract; eassumption.
  - (* deparser: writes no varlike *) exact I.
  - (* transformer: header targets in the seeded map, state targets in its own *)
    unfold transformer_dom_ok. rewrite List.Forall_forall. intros rule Hr.
    unfold rule_dom_ok. rewrite List.Forall_forall. intros op Hop.
    apply op_dom_ok_of_maps.
    + intros tgt Htgt. apply Hhdr. eapply collect_module_headers_tf; eassumption.
    + intros tgt Htgt. cbn [t_state_map].
      apply force_keys_dom. apply List.in_map.
      eapply collect_module_state_targets_tf; eassumption.
Qed.

(* --- the other four, each a one-liner about the seeding --- *)

Lemma init_pprefix : forall p pf f,
  pprefix f (sh_read_tape (init_general_symbolic_state pf p)).
Proof.
  intros p pf f. cbn [sh_read_tape init_general_symbolic_state].
  apply pprefix_symbolic_input_bits.
Qed.

Lemma init_extent_default : forall p pf f,
  eval_smt_arith (fst (sh_mem_extent (init_general_symbolic_state pf p))) f
  = mk_int u64 0.
Proof.
  intros p pf f. cbn [sh_mem_extent init_general_symbolic_state fst eval_smt_arith].
  apply mk_int_u64_mask_idem.
Qed.

Lemma wf_net_parsers : forall p,
  well_formed_general_program p -> net_parsers_wf (get_network_from_general p).
Proof.
  intros p [_ Hmods] m Hin.
  rewrite List.Forall_forall in Hmods. specialize (Hmods m Hin).
  destruct m as [mid pp | mid dd | mid sd cd tt]; cbn [well_formed_module] in Hmods;
    [ exact Hmods | exact I | exact I ].
Qed.

Lemma wf_mod_names_unique : forall p,
  well_formed_general_program p -> mod_names_unique (get_network_from_general p).
Proof. intros p [[H _] _]. exact H. Qed.

(* ==================================================================== *)
(* 24. THE BRIDGE, FOR THE STATES THE CHECKER ACTUALLY PASSES.           *)
(*                                                                       *)
(* [modnet_equivalence_checker_sound] runs each program from             *)
(* [init_general_symbolic_state], so this is the form it can consume.    *)
(* Its two hypotheses are the ones that theorem already has -- the       *)
(* second is [is_linear_chain]'s third projection, taken here directly   *)
(* because [is_linear_chain] is defined in [SmtModuleQuery], which       *)
(* imports this file.                                                    *)
(* ==================================================================== *)
Theorem program_commute_init : forall p pf f s_f,
  well_formed_general_program p ->
  no_fan_out (get_network_from_general p) ->
  eval_general_program_symbolic p (init_general_symbolic_state pf p) = Some s_f ->
  exists c_f,
    eval_general_program_concrete p
      (concretize_sym_modnet_state (init_general_symbolic_state pf p) f) = Some c_f /\
    gps_valid c_f = gps_valid (concretize_sym_modnet_state s_f f) /\
    (gps_valid c_f = true -> gps_agree c_f (concretize_sym_modnet_state s_f f)).
Proof.
  intros p pf f s_f Hwf Hnf Hsym.
  apply (program_commute_full p f (init_general_symbolic_state pf p) s_f).
  - exact Hnf.
  - apply wf_net_parsers. exact Hwf.
  - apply init_gs_dom_ok. apply wf_mod_names_unique. exact Hwf.
  - apply init_pprefix.
  - apply init_extent_default.
  - exact Hsym.
Qed.
