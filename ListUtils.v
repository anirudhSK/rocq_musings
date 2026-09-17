From Stdlib Require Import Lists.List.
Import ListNotations.
From Stdlib Require Import Strings.String.
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

   (* [existsb] respects pointwise equality of its predicate.  This is the
      congruence [has_duplicates_correct] needs to turn [existsb (fun y =>
      eqb y a)] into [existsb (eqb a)]: the two predicates agree at every
      point by [my_eqb_symmetric], but they are not the same TERM.

      Proving it pointwise, by induction on the list, is what keeps this file
      axiom-free.  Rewriting the lambda itself instead -- [apply
      functional_extensionality] on [(fun y => eqb y a) = (fun y => eqb a y)]
      -- also works and is shorter, but it charges the whole development an
      axiom: [functional_extensionality] is a stdlib LEMMA derived from the
      axiom [functional_extensionality_dep], so [Print Assumptions] on
      anything downstream reports the dependent version even though nothing
      here is dependently typed.  Downstream includes [PosGraphLemmas] and so
      the parser termination and well-formedness results, none of which
      otherwise assume anything.  Equality of functions is never actually
      needed -- only that a fold over a list gives the same answer. *)
   Lemma existsb_ext : forall (f g : T -> bool) (l : list T),
      (forall x, f x = g x) -> List.existsb f l = List.existsb g l.
   Proof.
      intros f g l Hfg. induction l as [| x xs IH]; simpl.
      - reflexivity.
      - rewrite Hfg, IH. reflexivity.
   Qed.

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
              rewrite (existsb_ext (eqb a) (fun y => eqb y a) l).
              -- exact E.
              -- intros y. apply my_eqb_symmetric.
            * apply H.
    Qed.
End ListUtilsLemmas.

(* Check has_duplicates_correct. *)