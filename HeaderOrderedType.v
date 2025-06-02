Require Export OrderedType.
Require Export OrderedTypeEx.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Coq.Arith.Arith.
Module String_as_OT <: UsualOrderedType.

  Definition t := string.

  Definition eq := @eq string.
  Definition eq_refl := @eq_refl t.
  Definition eq_sym := @eq_sym t.
  Definition eq_trans := @eq_trans t.

  Inductive lts : string -> string -> Prop :=
    | lts_empty : forall a s, lts EmptyString (String a s)
    | lts_tail : forall a s1 s2, lts s1 s2 -> lts (String a s1) (String a s2)
    | lts_head : forall (a b : ascii) s1 s2,
        lt (nat_of_ascii a) (nat_of_ascii b) ->
        lts (String a s1) (String b s2).

  Definition lt := lts.

  Lemma nat_of_ascii_inverse a b : nat_of_ascii a = nat_of_ascii b -> a = b.
  Proof.
    intro H.
    rewrite <- (ascii_nat_embedding a).
    rewrite <- (ascii_nat_embedding b).
    apply f_equal; auto.
  Qed.

  Lemma lts_tail_unique a s1 s2 : lt (String a s1) (String a s2) ->
    lt s1 s2.
  Proof.
    intro H; inversion H; subst; auto.
    remember (nat_of_ascii a) as x.
    apply Nat.lt_irrefl in H1; inversion H1.
  Qed.

  Lemma lt_trans : forall x y z : t, lt x y -> lt y z -> lt x z.
  Proof.
    induction x; intros y z H1 H2.
    - destruct y as [| b y']; inversion H1.
      destruct z as [| c z']; inversion H2; constructor.
    - destruct y as [| b y']; inversion H1; subst;
        destruct z as [| c z']; inversion H2; subst.
      + constructor. eapply IHx; eauto.
      + constructor; assumption.
      + constructor; assumption.
      + constructor. eapply Nat.lt_trans; eassumption.
  Qed.

  Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
  Proof.
    induction x; intros y LT.
    - inversion LT. intro. inversion H.
    - inversion LT; subst; intros EQ.
      * specialize (IHx s2 H2).
        inversion EQ; subst; auto.
        apply IHx; unfold eq; auto.
      * inversion EQ; subst; auto.
        apply Nat.lt_irrefl in H2; auto.
  Qed.

  Definition cmp : string -> string -> comparison := String.compare.

  Lemma cmp_eq (a b : string):
    cmp a b = Eq  <->  a = b.
  Proof.
    revert b.
    induction a, b; try easy.
    cbn.
    remember (Ascii.compare _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; split; try discriminate;
      try rewrite Ascii_as_OT.cmp_eq in Heqc; try subst;
      try rewrite IHa; intro H.
    { now subst. }
    { now inversion H. }
    { inversion H; subst. rewrite<- Heqc. now rewrite Ascii_as_OT.cmp_eq. }
    { inversion H; subst. rewrite<- Heqc. now rewrite Ascii_as_OT.cmp_eq. }
  Qed.

  Lemma cmp_antisym (a b : string):
    cmp a b = CompOpp (cmp b a).
  Proof.
    revert b.
    induction a, b; try easy.
    cbn. rewrite IHa. clear IHa.
    remember (Ascii.compare _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; rewrite Ascii_as_OT.cmp_antisym in Heqc;
      destruct Ascii_as_OT.cmp; cbn in *; easy.
  Qed.

  Lemma cmp_lt (a b : string):
    cmp a b = Lt  <->  lt a b.
  Proof.
    revert b.
    induction a as [ | a_head a_tail ], b; try easy; cbn.
    { split; trivial. intro. apply lts_empty. }
    remember (Ascii.compare _ _) as c eqn:Heqc. symmetry in Heqc.
    destruct c; split; intro H; try discriminate; trivial.
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      apply String_as_OT.lts_tail.
      apply IHa_tail.
      assumption.
    }
    {
      rewrite Ascii_as_OT.cmp_eq in Heqc. subst.
      inversion H; subst. { rewrite IHa_tail. assumption. }
      exfalso. apply (Nat.lt_irrefl (nat_of_ascii a)). assumption.
    }
    {
      apply String_as_OT.lts_head.
      rewrite<- Ascii_as_OT.cmp_lt_nat.
      assumption.
    }
    {
      exfalso. inversion H; subst.
      {
         assert(X: Ascii.compare a a = Eq). { apply Ascii_as_OT.cmp_eq. trivial. }
         rewrite Heqc in X. discriminate.
      }
      rewrite<- Ascii_as_OT.cmp_lt_nat in *.
      unfold Ascii_as_OT.cmp in *.
      rewrite Heqc in *. discriminate.
    }
  Qed.

  Local Lemma compare_helper_lt {a b : string} (L : cmp a b = Lt):
    lt a b.
  Proof.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_gt {a b : string} (G : cmp a b = Gt):
    lt b a.
  Proof.
    rewrite cmp_antisym in G.
    rewrite CompOpp_iff in G.
    now apply cmp_lt.
  Qed.

  Local Lemma compare_helper_eq {a b : string} (E : cmp a b = Eq):
    a = b.
  Proof.
    now apply cmp_eq.
  Qed.

  Definition compare (a b : string) : Compare lt eq a b :=
    match cmp a b as z return _ = z -> _ with
    | Lt => fun E => LT (compare_helper_lt E)
    | Gt => fun E => GT (compare_helper_gt E)
    | Eq => fun E => EQ (compare_helper_eq E)
    end Logic.eq_refl.

  Definition eq_dec (x y : string): {x = y} + { ~ (x = y)} := string_dec x y.
End String_as_OT.