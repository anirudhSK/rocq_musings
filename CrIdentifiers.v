Require Import Strings.String.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import InitStatus.
Require Import ZArith.
Require Import Bool.
Require Import List.
Import ListNotations.

(* Define the different types of identifiers in the Caracara DSL *)
Inductive ParserState : Type := ParserStateCtr (uid : positive).
Inductive ModuleName : Type := ModuleNameCtr (uid : positive).
Inductive FunctionName : Type := FunctionNameCtr (uid : positive).
Inductive ConnectionName : Type := ConnectionNameCtr (uid : positive).

(* Unified CrVar that represents Header / State / Ctrl identifiers *)
Inductive CrVar : Type :=
| CrHdr  (uid : positive)
| CrState (uid : positive)
| CrCtrl  (uid : positive).

(* Projection to the underlying uid *)
Definition crvar_id (v: CrVar) : positive :=
  match v with
  | CrHdr uid => uid
  | CrState uid => uid
  | CrCtrl uid => uid
  end.

(* Kind predicates (bools are convenient for decisions and proofs) *)
Definition is_header (v: CrVar) : bool :=
  match v with CrHdr _ => true | _ => false end.
Definition is_state (v: CrVar) : bool :=
  match v with CrState _ => true | _ => false end.
Definition is_ctrl (v: CrVar) : bool :=
  match v with CrCtrl _ => true | _ => false end.

(* Wrapper records that carry the invariant that the CrVar is of the expected kind.
   Keeping the old names (Header / State / Ctrl) lets other modules remain largely unchanged. *)
Record Header := mkHeader { hdr_var : CrVar; hdr_ok : is_header hdr_var = true }.
Record State  := mkState  { st_var  : CrVar; st_ok  : is_state st_var = true }.
Record Ctrl   := mkCtrl   { ctrl_var : CrVar; ctrl_ok : is_ctrl ctrl_var = true }.

(* Coercions allow a Header/State/Ctrl to be used where CrVar is expected *)
Coercion hdr_var : Header >-> CrVar.
Coercion st_var  : State  >-> CrVar.
Coercion ctrl_var: Ctrl   >-> CrVar.

(* Smart constructors for easy construction where the underlying invariant is evident *)
Definition make_header (uid : positive) : Header := mkHeader (CrHdr uid) eq_refl.
Definition make_state  (uid : positive) : State  := mkState  (CrState uid) eq_refl.
Definition make_ctrl   (uid : positive) : Ctrl   := mkCtrl   (CrCtrl uid) eq_refl.

Definition injective_contravariant {A B} (f : A -> B) : Prop :=
  forall x y, x <> y -> f x <> f y.

Class CrVarLike (A : Type) := {
  make_item : positive -> A;
  get_key   : A -> positive;
  inverses : forall (x : A), make_item (get_key x) = x;
  inj : injective_contravariant get_key;
}.

Require Import Coq.Logic.ProofIrrelevance.
Instance CrVarLike_Header : CrVarLike Header.
Proof.
  refine {| make_item := make_header;
            get_key := fun h => crvar_id (hdr_var h);
            inverses := _;
            inj := _ |}.
  - (* inverses : forall x, make_item (get_key x) = x *)
    intros [v p]. simpl.
    destruct v; simpl in p; try discriminate.
    simpl.
    unfold make_header.
    f_equal.
    apply proof_irrelevance.
  - (* inj : injective_contravariant get_key *)
    intros x y Hxy Heq.
    destruct x as [v1 p1], y as [v2 p2]; simpl in Heq.
    destruct v1; destruct v2; simpl in Heq; try discriminate.
    rewrite Heq in Hxy.
    assert (Htmp : {| hdr_var := CrHdr uid0; hdr_ok := p1 |} =
{| hdr_var := CrHdr uid0; hdr_ok := p2 |}). { 
      f_equal.
      apply proof_irrelevance. }
    rewrite Htmp in Hxy.
    congruence.
Defined.

(* Convenience equality test on CrVar by id and constructor tag *)
Definition crvar_eqb (a b : CrVar) : bool :=
  match a, b with
  | CrHdr sa,   CrHdr sb   => Pos.eqb sa sb
  | CrState sa, CrState sb => Pos.eqb sa sb
  | CrCtrl sa,  CrCtrl sb  => Pos.eqb sa sb
  | _, _ => false
  end.

(* Equality check functions for the identifiers above *)
Definition parser_state_equal (p1 p2 : ParserState) :=
    match p1, p2 with
            | ParserStateCtr xid, ParserStateCtr yid => Pos.eqb xid yid
    end.
(* Use positive equality directly for identifiers *)
Definition parser_state_equal' (p1 p2 : ParserState) :=
        match p1, p2 with
        | ParserStateCtr xid, ParserStateCtr yid => Pos.eqb xid yid
        end.

(* Do the same thing as parser_state_equal for Header *)
Definition header_equal (h1 h2 : Header) :=
    crvar_eqb h1 h2.

(* Do the same thing as parser_state_equal for State *)
Definition state_equal (sv1 sv2 : State) :=
    crvar_eqb sv1 sv2.

(* Do the same thing as parser_state_equal for ModuleName *)
Definition module_name_equal (m1 m2 : ModuleName) :=
    match m1, m2 with
            | ModuleNameCtr xid, ModuleNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for FunctionName *)
Definition function_name_equal (f1 f2 : FunctionName) :=
    match f1, f2 with
            | FunctionNameCtr xid, FunctionNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for ConnectionName *)
Definition connection_name_equal (c1 c2 : ConnectionName) :=
    match c1, c2 with
            | ConnectionNameCtr xid, ConnectionNameCtr yid => Pos.eqb xid yid
    end.

(* Do the same thing as parser_state_equal for Ctrl *)
Definition ctrl_equal (cc1 cc2 : Ctrl) :=
    crvar_eqb cc1 cc2.

Require Import Coq.Logic.ProofIrrelevance.

Lemma header_equal_lemma :
  forall h1 h2,
  header_equal h1 h2 = true ->
  h1 = h2.
Proof.
  intros [v1 p1] [v2 p2] H.
  unfold header_equal, crvar_eqb in H. simpl in H.
  destruct v1; destruct v2; simpl in H; try discriminate.
  apply Pos.eqb_eq in H. subst. f_equal. apply proof_irrelevance.
Qed.

Fixpoint hdr_list_equal (h1 : list Header) (h2 : list Header) :=
  match h1, h2 with
  | nil, nil => true
  | h::y, h'::y' => andb (header_equal h h') (hdr_list_equal y y')
  | _, _ => false
  end.
       
Lemma hdr_list_equal_lemma:
  forall h1 h2,
  hdr_list_equal h1 h2 = true ->
  h1 = h2.
Proof.
  intros h1.
  induction h1 as [|h1' h1''].
  - destruct h2; simpl; congruence.
  - destruct h2 as [|h2' h2''].
    + simpl. congruence.
    + intros H. simpl in H.
      rewrite andb_true_iff in H. destruct H as [H1 H2].
      apply header_equal_lemma in H1. subst. f_equal.
      apply IHh1''.
      assumption.
Qed.

Lemma state_equal_lemma :
  forall s1 s2,
  state_equal s1 s2 = true ->
  s1 = s2.
Proof.
  intros s1 s2 H.
  destruct s1, s2; simpl in H; try congruence.
  destruct st_var0, st_var1; simpl in H; try discriminate.
  apply Pos.eqb_eq in H. subst. f_equal. apply proof_irrelevance.
Qed.

(* Do the same thing as above
   for state_list and ctrl_list (including the lemmas)*)
Fixpoint state_list_equal (s1 : list State) (s2 : list State) :=
  match s1, s2 with
  | nil, nil => true
  | s::y, s'::y' => andb (state_equal s s') (state_list_equal y y')
  | _, _ => false
  end. 

Lemma state_list_equal_lemma:
  forall s1 s2,
  state_list_equal s1 s2 = true ->
  s1 = s2.
Proof.
  intros s1.
  induction s1 as [|s1' s1''].
  - destruct s2; simpl; congruence.
  - destruct s2 as [|s2' s2''].
    + simpl. congruence.
    + intros H. simpl in H.
      rewrite andb_true_iff in H. destruct H as [H1 H2].
      apply state_equal_lemma in H1. subst. f_equal.
      apply IHs1''.
      assumption.
Qed.

Fixpoint ctrl_list_equal (c1 : list Ctrl) (c2 : list Ctrl) :=
  match c1, c2 with
  | nil, nil => true
  | c::y, c'::y' => andb (ctrl_equal c c') (ctrl_list_equal y y')
  | _, _ => false
  end.

Lemma ctrl_equal_lemma :
  forall c1 c2,
  ctrl_equal c1 c2 = true ->
  c1 = c2.
Proof.
  intros c1 c2 H.
  destruct c1, c2; simpl in H.
  unfold ctrl_equal, crvar_eqb in H. simpl in H.
  destruct ctrl_var0, ctrl_var1; simpl in H; try discriminate.
  apply Pos.eqb_eq in H. subst. f_equal. apply proof_irrelevance.
Qed.

Lemma ctrl_list_equal_lemma:
  forall c1 c2,
  ctrl_list_equal c1 c2 = true ->
  c1 = c2.
Proof.
  intros c1.
  induction c1 as [|c1' c1''].
  - destruct c2; simpl; congruence.
  - destruct c2 as [|c2' c2''].
    + simpl. congruence.
    + intros H. simpl in H.
      rewrite andb_true_iff in H. destruct H as [H1 H2].
      apply ctrl_equal_lemma in H1. subst. f_equal.
      apply IHc1''.
      assumption.
Qed.