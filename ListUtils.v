Require Import List.
Require Import Coq.Lists.List.
Require Import Coq.Arith.EqNat.
Require Import Coq.Arith.PeanoNat.
Import ListNotations.
Require Import Coq.Logic.Classical_Prop.
From Coq Require Import FunctionalExtensionality.
Require Import Coq.Strings.String.
Open Scope string_scope.
From MyProject Require Import Coqlib.

(* Check if there are any duplicates in my_list.
   Use an existing library function directly if one exists. *)
Fixpoint has_duplicates {T : Type} (eqb : T -> T -> bool) (l : list T) : bool :=
    match l with
    | x :: xs => if List.existsb (fun y => eqb y x) xs then true else has_duplicates eqb xs
    | [] => false
    end.

(* Function to find first match given:
   a list of pair,
   each pair consists of a bool that says if there was a match or not and the element itself *)
Fixpoint find_first_match {T : Set} (list_of_pair : list (bool*T)) : option T :=
    match list_of_pair with
    | [] => None                                       (* empty, return error *)
    | (true,r) :: _ => Some r                          (* found a match, return the corresponding rule, ignore the rest (_) *)
    | (false,_) :: rest => find_first_match rest (* continue searching *)
    end.

(* Create a few examples to test out find_first_match *)
(* Use a string for the type T above *)
Definition example_list_of_pair : list (bool * string) :=
  [(false, "rule1"); (true, "rule2"); (false, "rule3")].
Definition example_list_of_pair2 : list (bool * string) :=
  [(true, "ruleA"); (false, "ruleB"); (true, "ruleC")].
Definition example_list_of_pair3 : list (bool * string) :=
  [(false, "ruleX"); (false, "ruleY"); (true, "ruleZ")].
(* One example with all false *)
Definition example_list_of_pair4 : list (bool * string) :=
  [(false, "rule1"); (false, "rule2"); (false, "rule3")].

(* Test the find_first_match function on all examples above *)
(*
Eval compute in (find_first_match example_list_of_pair). (* should return Some "rule2" *)
Eval compute in (find_first_match example_list_of_pair2). (* should return Some "ruleA" *)
Eval compute in (find_first_match example_list_of_pair3). (* should return Some "ruleZ" *)
Eval compute in (find_first_match example_list_of_pair4). (* should return None *)
*)

Section ListUtilsLemmas.
   Context (T : Type).
   Context (eqb : T -> T -> bool).

   Context (my_eqb_reflexive: forall (a : T), eqb a a = true).

   Context (my_eqb_symmetric: forall (a b : T), eqb a b = eqb b a).

   Lemma not_exists_not_in : forall (l : list T) (a : T),
      List.existsb (eqb a) l = false ->
      ~ In a l.
   Proof.
      intros l a H.
      induction l.
      - auto.
      - simpl in H.
        simpl in IHl.
        destruct (existsb (eqb a) l).
        + destruct (eqb a a0) eqn:Heq.
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
        + destruct (eqb a a0) eqn:Heq.
            * simpl in H.
              discriminate H.
            * intros [H1 | H2].
              -- rewrite H1 in Heq.
                rewrite my_eqb_reflexive in Heq.
                discriminate Heq.
              -- simpl in IHl.
                specialize (IHl eq_refl).
                contradiction.
    Qed.

    (* Theorem stating that has_duplicates returning false implies a duplicate free list *)
    Theorem has_duplicates_correct : forall (l : list T),
        has_duplicates eqb l = false -> Coqlib.list_norepet l.
    Proof.
        intros l H.
        induction l.
        - constructor.
        - simpl in H.
          destruct (List.existsb (fun y => eqb y a) l) eqn:E.
          + apply existsb_exists in E.
            destruct E as [y [H1 H2]].
            discriminate H.
          + apply IHl in H.
            simpl in E.
            constructor.
            * apply not_exists_not_in.
              assert (test: (fun y : T => eqb y a) =
                      (fun y : T => eqb a y)).
                      { apply functional_extensionality.
                        intros y.
                        rewrite my_eqb_symmetric.
                        reflexivity.
                        }
              rewrite test in E.
              apply E.  
            * apply H.
    Qed.
End ListUtilsLemmas.

(* Check has_duplicates_correct. *)