(* Create a list of 5 elements in the coq functional language *)
Require Import List.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Logic.Classical_Prop.

(* Define a list of 5 elements *)
Definition my_list : list nat := [1; 2; 3; 4; 5].

Eval compute in (length my_list).

(* Check if there are any duplicates in my_list.
   Use an existing library function directly if one exists. *)
Fixpoint has_duplicates {T : Type} (eqb : T -> T -> bool) (l : list T) : bool :=
    match l with
    | x :: xs => if List.existsb (fun y => eqb y x) xs then true else has_duplicates eqb xs
    | [] => false
    end.

Eval compute in (has_duplicates Nat.eqb my_list).

Eval compute in (has_duplicates Nat.eqb [1; 2; 3; 4; 5; 1]). (* Should return true *)

Eval compute in (has_duplicates Nat.eqb [1; 2; 3; 4; 10]). (* Should return false *)

Eval compute in (has_duplicates Nat.eqb []). (* Should return false *)

Eval compute in (has_duplicates Nat.eqb [1; 2; 3; 4; 6; 10; 3]). (* Should return true *)

Eval compute in (has_duplicates Nat.eqb [1; 2; 3; 4; 6; 10; 30]). (* Should return false *)

Lemma not_exists_not_in : forall (l : list nat) (a : nat),
    List.existsb (fun y => Nat.eqb y a) l = false ->
    ~ In a l.
Proof.
    intros l a H.
    induction l.
    - auto.
    - simpl in H.
      simpl in IHl.
      destruct (existsb (fun y : nat => y =? a) l).
       + destruct (a0 =? a) eqn:Heq.
          * discriminate H.
          * assert (~ In a l) by (apply IHl; discriminate).
            clear IHl.
            simpl.
            simpl in Heq.
            intros [H1 | H2].
            -- simpl in H.
               discriminate H.
            -- simpl in H.
               discriminate H.
       + destruct (a0 =? a) eqn:Heq.
          * simpl in H.
            discriminate H.
          * intros [H1 | H2].
            -- rewrite H1 in Heq.
               rewrite Nat.eqb_refl in Heq.
               discriminate Heq.
            -- simpl in IHl.
               specialize (IHl eq_refl).
               contradiction.
Qed.

(* Theorem stating that has_duplicates returns a duplicate free list *)
Theorem has_duplicates_correct : forall l, has_duplicates Nat.eqb l = false -> NoDup l.
Proof.
    intros l H.
    induction l.
    - constructor.
    - simpl in H.
      destruct (List.existsb (fun y => Nat.eqb y a) l) eqn:E.
      + apply existsb_exists in E.
        destruct E as [y [H1 H2]].
        discriminate H.
      + apply IHl in H.
        simpl in E.
        constructor.
        * apply not_exists_not_in.
          apply E.
        * apply H.
Qed.