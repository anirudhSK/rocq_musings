From MyProject Require Import CrDsl.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrModule.
From MyProject Require Import ListUtils.
From MyProject Require Import CrTransformer.
From Stdlib Require Import PArith.BinPos.
From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Sorting.Sorted.

(* Check for duplicate identifiers in the header, state, and control lists *)
Definition check_for_duplicate_identifiers (program : CaracaraProgram) : bool :=
  match program with
  | CaracaraProgramDef h s c _ =>
      (* TODO: can probably adjust has_duplicates *)
      has_duplicates varlike_equal h ||
      has_duplicates varlike_equal s ||
      has_duplicates varlike_equal c
  end.

(* Compare two headers based on their uids *)
Section VarlikeCmp.
Context {A : Type} {CrVarLike_A : CrVarLike A}.
Definition varlike_lt (v1 v2: A) : Prop :=
  Pos.lt (get_key v1) (get_key v2).
Definition varlike_ltb (v1 v2: A) : bool :=
  Pos.ltb (get_key v1) (get_key v2).
End VarlikeCmp.

(* require that a transformer ends with a matchall (make no-op or otherwise explicit) *)
Fixpoint transformer_has_default (t : Transformer) : Prop :=
  match t with
  | [] => False
  | [rule] => match rule with
    | Seq (SeqCtr mp _)
    | Par (ParCtr mp _) => match mp with
        | [] => True
        | _ => False
      end
    end
  | _ :: rest => transformer_has_default rest
  end.

(* No duplicates in Caracara Program *)
Definition well_formed_program (p : CaracaraProgram) : Prop :=
  match p with
  | CaracaraProgramDef h s c t =>
      Coqlib.list_norepet h /\ Coqlib.list_norepet s /\ Coqlib.list_norepet c /\
      Sorted varlike_lt h /\ Sorted varlike_lt s /\ Sorted varlike_lt c /\
      transformer_has_default t
  end.

(* TODO: Write a program to check for the well_formed_program property *)
(* TODO: This would involve checking for duplicates and sorting the lists *)
(* TODO: And then verifying the well_formed_program property holds *)

(* Per-module analogue of well_formed_program. *)
(* TODO: Needs extension once parser semantics are fleshed out *)
Definition well_formed_module (m : CrModule) : Prop :=
  match m with
  (* TODO: parser/deparser modules are currently unconstrained.  A deparser
     should at least require its emit widths to be well-formed (and, once
     header types carry widths, that each emit width match its header). *)
  | ParserModule _ _ => True
  | DeparserModule _ _ => True
  | TransformerModule _ states ctrls t =>
      Coqlib.list_norepet states /\ Coqlib.list_norepet ctrls /\
      Sorted varlike_lt states /\ Sorted varlike_lt ctrls /\
      transformer_has_default t
  end.

Definition all_network_states (net : ModuleNetwork) : list State :=
  List.flat_map module_states (net_modules net).

Definition all_network_ctrls (net : ModuleNetwork) : list Ctrl :=
  List.flat_map module_ctrls (net_modules net).

(* extend well-formedness to GeneralCaracaraProgram *)
(* NOTE: depending on the extent to which sortedness actually matters,
 * it could be possible to remove the 3rd and 4th clauses *)
Definition well_formed_general_program (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  let headers := get_headers_from_general p in
  let sig := get_signature_from_general p in
  wf_module_network net /\
  Coqlib.list_norepet headers /\
  Coqlib.list_norepet sig /\
  Sorted varlike_lt headers /\
  Sorted varlike_lt sig /\
  List.Forall well_formed_module (net_modules net) /\
  Coqlib.list_norepet (all_network_states net) /\
  Coqlib.list_norepet (all_network_ctrls net).

Fixpoint Sortedb {A} (leb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: rest =>
    match rest with
    | [] => true
    | y :: _ => leb x y && Sortedb leb rest
    end
  end.

Lemma sorted_is_sorted_lemma :
  forall T (L : list T) (lt : T -> T -> Prop) (ltb : T -> T -> bool),
    (forall x y, lt x y <-> ltb x y = true) ->
    Sorted lt L <-> Sortedb ltb L = true.
Proof.
  intros T L lt ltb H_iff.
  induction L as [| x rest IH].
  - split; intro; [reflexivity | constructor].
  - destruct rest as [| y rest'].
    + split; intro; [reflexivity | repeat constructor].
    + simpl. rewrite Bool.andb_true_iff. split.
      * intros Hs.
        inversion Hs as [| ? ? Hsr Hhd]; subst.
        inversion Hhd as [| ? ? Hvlt]; subst.
        exact (conj (proj1 (H_iff x y) Hvlt) (proj1 IH Hsr)).
      * intros [Hlt Hsr].
        apply Sorted_cons.
        -- exact (proj2 IH Hsr).
        -- apply HdRel_cons. exact (proj2 (H_iff x y) Hlt).
Qed.

Fixpoint transformer_has_defaultb (t : Transformer) : bool :=
  match t with
  | [] => false
  | [rule] => match rule with
    | Seq (SeqCtr mp _)
    | Par (ParCtr mp _) => match mp with
        | [] => true
        | _ => false
      end
    end
  | _ :: rest => transformer_has_defaultb rest
  end.

Lemma transformer_has_default_prop_bool_lemma :
  forall t,
    transformer_has_default t <-> transformer_has_defaultb t = true.
Proof.
  intro t. induction t as [| rule rest IH].
  - simpl. split; intro H; [destruct H | discriminate].
  - destruct rest as [| rule2 rest'].
    + destruct rule as [s | p].
      * destruct s as [mp ops]. destruct mp as [| hd tl]; simpl;
          split; intro H; [reflexivity | exact I | destruct H | discriminate].
      * destruct p as [mp ops]. destruct mp as [| hd tl]; simpl;
          split; intro H; [reflexivity | exact I | destruct H | discriminate].
    + simpl. exact IH.
Qed.

Definition well_formed_programb (p : CaracaraProgram) : bool :=
  match p with
  | CaracaraProgramDef h s c t =>
      negb (has_duplicates varlike_equal h) &&
      negb (has_duplicates varlike_equal s) &&
      negb (has_duplicates varlike_equal c) &&
      Sortedb varlike_ltb h &&
      Sortedb varlike_ltb s &&
      Sortedb varlike_ltb c &&
      transformer_has_defaultb t
  end.

Lemma varlike_equal_refl : forall {A} {VA : CrVarLike A} (v : A),
  varlike_equal v v = true.
Proof.
  intros. unfold varlike_equal. apply Pos.eqb_eq. reflexivity.
Qed.

Lemma varlike_equal_sym_bool : forall {A} {VA : CrVarLike A} (v1 v2 : A),
  varlike_equal v1 v2 = varlike_equal v2 v1.
Proof.
  intros. unfold varlike_equal.
  destruct (Pos.eqb (get_key v1) (get_key v2)) eqn:H12;
  destruct (Pos.eqb (get_key v2) (get_key v1)) eqn:H21;
  try reflexivity; exfalso.
  - apply Pos.eqb_eq in H12. rewrite H12 in H21.
    assert (Hrefl : Pos.eqb (get_key v2) (get_key v2) = true) by (apply Pos.eqb_eq; reflexivity).
    congruence.
  - apply Pos.eqb_eq in H21. rewrite <- H21 in H12.
    assert (Hrefl : Pos.eqb (get_key v1) (get_key v1) = true) by (apply Pos.eqb_eq; reflexivity).
    congruence.
Qed.

Lemma list_norepet_implies_no_duplicates :
  forall {A} {VA : CrVarLike A} (l : list A),
    Coqlib.list_norepet l -> has_duplicates varlike_equal l = false.
Proof.
  intros A VA l Hnr.
  induction Hnr as [| x xs Hni Hnr IH].
  - reflexivity.
  - simpl.
    destruct (List.existsb (fun y => varlike_equal y x) xs) eqn:He.
    + exfalso.
      apply List.existsb_exists in He.
      destruct He as [y [Hyin Heqyx]].
      apply varlike_equal_lemma in Heqyx.
      rewrite <- Heqyx in Hyin.
      exact (Hni Hyin).
    + exact IH.
Qed.

Lemma well_formed_program_prop_bool_lemma :
  forall p,
    well_formed_program p <-> well_formed_programb p = true.
Proof.
  intro p. destruct p as [h s c t].
  unfold well_formed_program, well_formed_programb.
  (* Instantiate sorted_is_sorted_lemma with explicit type to bypass typeclass ambiguity *)
  pose proof (sorted_is_sorted_lemma Header h varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFh.
  pose proof (sorted_is_sorted_lemma State s varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFs.
  pose proof (sorted_is_sorted_lemma Ctrl c varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFc.
  split.
  - intros (Hnrh & Hnrs & Hnrc & Sorh & Sors & Sorc & Hthd).
    pose proof (list_norepet_implies_no_duplicates h Hnrh) as Hdh.
    pose proof (list_norepet_implies_no_duplicates s Hnrs) as Hds.
    pose proof (list_norepet_implies_no_duplicates c Hnrc) as Hdc.
    pose proof (proj1 SIFFh Sorh) as HSh.
    pose proof (proj1 SIFFs Sors) as HSs.
    pose proof (proj1 SIFFc Sorc) as HSc.
    pose proof (proj1 (transformer_has_default_prop_bool_lemma t) Hthd) as HTt.
    rewrite Hdh, Hds, Hdc, HSh, HSs, HSc, HTt. reflexivity.
  - intro Hb.
    repeat rewrite Bool.andb_true_iff in Hb.
    destruct Hb as ((((((HnDh & HnDs) & HnDc) & HSh) & HSs) & HSc) & HTt).
    rewrite Bool.negb_true_iff in HnDh, HnDs, HnDc.
    repeat split.
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl varlike_equal_sym_bool h HnDh).
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl varlike_equal_sym_bool s HnDs).
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl varlike_equal_sym_bool c HnDc).
    + exact (proj2 SIFFh HSh).
    + exact (proj2 SIFFs HSs).
    + exact (proj2 SIFFc HSc).
    + exact (proj2 (transformer_has_default_prop_bool_lemma t) HTt).
Qed.

Definition well_formed_moduleb (m : CrModule) : bool :=
  match m with
  | ParserModule _ _ => true
  | DeparserModule _ _ => true
  | TransformerModule _ states ctrls t =>
      negb (has_duplicates varlike_equal states) &&
      negb (has_duplicates varlike_equal ctrls) &&
      Sortedb varlike_ltb states &&
      Sortedb varlike_ltb ctrls &&
      transformer_has_defaultb t
  end.

Lemma well_formed_module_prop_bool_lemma :
  forall m,
    well_formed_module m <-> well_formed_moduleb m = true.
Proof.
  intros.
  unfold well_formed_module, well_formed_moduleb.
  destruct m; try (split; intros; reflexivity).
  pose proof (sorted_is_sorted_lemma State s varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFs.
  pose proof (sorted_is_sorted_lemma Ctrl c varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFc.
  split; intros.
  - destruct H as (Hnrs & Hnrc & HSs & HSc & HTd).
    apply list_norepet_implies_no_duplicates in Hnrs.
    apply list_norepet_implies_no_duplicates in Hnrc.
    apply (proj1 SIFFs) in HSs.
    apply (proj1 SIFFc) in HSc.
    apply transformer_has_default_prop_bool_lemma in HTd.
    rewrite Hnrs, Hnrc, HSs, HSc, HTd. reflexivity.
  - repeat rewrite Bool.andb_true_iff in H.
    destruct H as ((((HnDs & HnDc) & HSs) & HSc) & HTd).
    rewrite Bool.negb_true_iff in HnDs, HnDc.
    repeat split.
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool s HnDs).
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool c HnDc).
    + exact (proj2 SIFFs HSs).
    + exact (proj2 SIFFc HSc).
    + apply transformer_has_default_prop_bool_lemma. exact HTd.
Qed.

Definition well_formed_general_programb (p : GeneralCaracaraProgram) : bool :=
  let net := get_network_from_general p in
  let headers := get_headers_from_general p in
  let sig := get_signature_from_general p in
  wf_module_networkb net &&
  negb (has_duplicates varlike_equal headers) &&
  negb (has_duplicates varlike_equal sig) &&
  Sortedb varlike_ltb headers &&
  Sortedb varlike_ltb sig &&
  List.forallb well_formed_moduleb (net_modules net) &&
  negb (has_duplicates varlike_equal (all_network_states net)) &&
  negb (has_duplicates varlike_equal (all_network_ctrls net)).

Lemma well_formed_general_program_prop_bool_lemma :
  forall p,
    well_formed_general_program p <-> well_formed_general_programb p = true.
Proof.
  intros p.
  destruct p as [headers net sig].
  unfold well_formed_general_program, well_formed_general_programb.
  simpl.
  pose proof (sorted_is_sorted_lemma Header headers varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFh.
  pose proof (sorted_is_sorted_lemma Header sig varlike_lt varlike_ltb
    (fun x y => iff_sym (Pos.ltb_lt (get_key x) (get_key y)))) as SIFFsig.

  (* Reflection of [List.Forall] against [List.forallb] for well-formed
     modules. *)
  assert (FAFB : List.Forall well_formed_module (net_modules net) <->
                 List.forallb well_formed_moduleb (net_modules net) = true).
  { rewrite Forall_forall, forallb_forall. split; intros H x Hx;
      apply well_formed_module_prop_bool_lemma; auto. }

  (* Reflexivity, symmetry, and injectivity of [posesque_eqb] on
     [ModuleName], reusing the canonical lemmas from CrIdentifiers.
     Used to handle [mod_names_unique{,b}] below. *)
  pose proof (@posesque_eqb_refl ModuleName _) as Hpr.
  pose proof (@posesque_eqb_sym ModuleName _) as Hps.
  pose proof (fun x y => proj1 (@posesque_eqb_iff ModuleName _ x y)) as Hpeq.

  (* [mod_names_unique <-> mod_names_uniqueb = true]. *)
  assert (MNU : mod_names_unique net <-> mod_names_uniqueb net = true).
  { unfold mod_names_unique, mod_names_uniqueb. split.
    - intros Hnr. apply Bool.negb_true_iff.
      induction Hnr as [| x xs Hni _ IH].
      + reflexivity.
      + simpl.
        destruct (List.existsb (fun y => posesque_eqb y x) xs) eqn:He.
        * exfalso. apply List.existsb_exists in He.
          destruct He as [y [Hyin Heqyx]]. apply Hpeq in Heqyx.
          subst. exact (Hni Hyin).
        * exact IH.
    - intros Hb. apply Bool.negb_true_iff in Hb.
      exact (has_duplicates_correct _ posesque_eqb Hpr Hps _ Hb). }

  (* [wf_module_network <-> wf_module_networkb = true]. *)
  assert (WFB : wf_module_network net <-> wf_module_networkb net = true).
  { unfold wf_module_network, wf_module_networkb.
    pose proof (start_module_defined_prop_bool_lemma net) as SMD.
    pose proof (is_dag_prop_bool_lemma net) as IDP.
    split.
    - intros (HMU & HSM & HDG).
      rewrite (proj1 MNU HMU), (proj1 SMD HSM), (proj1 IDP HDG).
      reflexivity.
    - intros Hb. repeat rewrite Bool.andb_true_iff in Hb.
      destruct Hb as ((HMU & HSM) & HDG).
      split; [apply MNU | split; [apply SMD | apply IDP]]; assumption. }

  split.
  - intros (Hwf & Hnrh & Hnrsig & HSh & HSsig & HFa & Hnrst & Hnrct).
    apply WFB in Hwf.
    apply list_norepet_implies_no_duplicates in Hnrh.
    apply list_norepet_implies_no_duplicates in Hnrsig.
    apply (proj1 SIFFh) in HSh.
    apply (proj1 SIFFsig) in HSsig.
    apply FAFB in HFa.
    apply list_norepet_implies_no_duplicates in Hnrst.
    apply list_norepet_implies_no_duplicates in Hnrct.
    rewrite Hwf, Hnrh, Hnrsig, HSh, HSsig, HFa, Hnrst, Hnrct.
    reflexivity.
  - intros Hb.
    repeat rewrite Bool.andb_true_iff in Hb.
    destruct Hb as (((((((Hwf & Hnrh) & Hnrsig) & HSh) & HSsig) & HFa) & Hnrst)
                    & Hnrct).
    rewrite Bool.negb_true_iff in Hnrh, Hnrsig, Hnrst, Hnrct.
    (* Build the 8-way conjunction explicitly with [conj] so the
       transparent [wf_module_network] is not unfolded by [split]. *)
    refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))).
    + apply (proj2 WFB). exact Hwf.
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool headers Hnrh).
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool sig Hnrsig).
    + exact (proj2 SIFFh HSh).
    + exact (proj2 SIFFsig HSsig).
    + apply (proj2 FAFB). exact HFa.
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool (all_network_states net) Hnrst).
    + exact (has_duplicates_correct _ varlike_equal varlike_equal_refl
               varlike_equal_sym_bool (all_network_ctrls net) Hnrct).
Qed.
