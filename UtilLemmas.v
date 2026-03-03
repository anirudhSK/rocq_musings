From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Lists.List.
From Stdlib Require Import ZArith.ZArith.

Lemma not_none_is_some : forall {A : Type} (y : option A),
  y <> None -> exists x, y = Some x.
Proof.
  intros A y H.
  destruct y as [x|].
  - exists x. reflexivity.
  - exfalso. apply H. reflexivity.
Qed.

(* This is what I am going to call the Joe subtlety in honor of
   https://gist.github.com/jtassarotti/57f65712869af462a01b46b660e0d92d 
   This is the buggy lemma here:
   Lemma some_is_not_none : forall {A : Type} (y : option A),
       exists x, y = Some x -> y <> None.
   Btw, as of Aug 4, 2025, Copilot points this out *)
Lemma some_is_not_none : forall {A : Type} (y : option A) (x: A),
  y = Some x -> y <> None.
Proof.
  intros A y x H.
  rewrite H.
  discriminate.
Qed.

Lemma forallb_in_hdr_list :
  forall (f : Header -> bool) (l : list Header),
  forallb f l = true ->
  forall x, In x l -> f x = true.
Proof.
  intros f l H.
  induction l as [|x t IH].
  - intros x H_in. exfalso. simpl in H_in. contradiction.
  - simpl in H.
    apply andb_true_iff in H as [H1 H2].
    specialize (IH H2).
    simpl.
    intros x0.
    intros H_in.
    destruct H_in as [H_eq | H_in_t].
    + subst x0. assumption.
    + apply IH. assumption.
Qed.

(* Same lemma as above but for state var list *)
Lemma forallb_in_state_var_list :
  forall (f :State -> bool) (l : list State),
  forallb f l = true ->
  forall x, In x l -> f x = true.
Proof.
  intros f l H.
  induction l as [|x t IH].
  - intros x H_in. exfalso. simpl in H_in. contradiction.
  - simpl in H.
    apply andb_true_iff in H as [H1 H2].
    specialize (IH H2).
    simpl.
    intros x0.
    intros H_in.
    destruct H_in as [H_eq | H_in_t].
    + subst x0. assumption.
    + apply IH. assumption.
Qed.

Lemma map_pair_split : forall (A B C : Type) (f : A -> B * C) (l : list A),
  map f l = combine (map (fun x => fst (f x)) l) (map (fun x => snd (f x)) l).
Proof.
  intros A B C f l.
  induction l as [|a l' IH].
  - reflexivity.
  - simpl. f_equal.
    + destruct (f a). reflexivity.
    + apply IH.
Qed.

Lemma functional_list_helper :
  forall (X : Type) (l : list X) (key_fn : X -> positive) (val_fn : X -> SmtArithExpr) (x : X),
  In x l ->
  In (key_fn x, val_fn x) (combine (map key_fn l) (map val_fn l)).
Proof.
  intros X l key_fn val_fn x H_in.
  induction l as [|x' t IH].
  - simpl in H_in. exfalso. congruence.
  - simpl.
    simpl in H_in.
    destruct H_in.
    -- left. rewrite H. reflexivity.
    -- right. apply IH. assumption.
Qed.

Lemma map_combine2:
   forall {T V K} (l : list T) (val_fn : T -> V) (key_fn : T -> K),
    (map fst (combine (map key_fn l) (map val_fn l))) =
    (map key_fn l).
Proof.
  intros T V K l val_fn key_fn.
  induction l as [|x t IH].
  - reflexivity.
  - simpl. f_equal. apply IH.
Qed.