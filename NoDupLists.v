Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Lists.ListSet.
Require Import Lia.

(* Define a type for lists with no duplicates *)
Definition NoDupList (A : Type) := { l : list A | NoDup l }.

Lemma my_list_nodup : NoDup [1; 2; 3].
Proof. apply NoDup_cons; simpl; auto.
- lia.
- apply NoDup_cons; simpl; auto.
  + lia.
  + apply NoDup_cons; simpl; auto.
    * apply NoDup_nil.
Qed.

Definition my_actions : NoDupList nat := exist (fun l : list nat => NoDup l) [1; 2; 3] my_list_nodup.