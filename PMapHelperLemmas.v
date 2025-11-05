From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import Maps.
From MyProject Require Import UtilLemmas.
From MyProject Require Import CrIdentifiers.
Require Import Coq.Lists.List.
Require Import ZArith.

Transparent map_from_ps.
Transparent lookup_varlike_map.
Lemma commute_lookup_eval_generic:
  forall (A: Type) `{CrVarLike A} (v : A) field_type f ps,
  lookup_varlike_map (map_from_ps field_type (eval_sym_state ps f)) v =
  eval_smt_arith (lookup_varlike_map (map_from_ps field_type ps) v) f.
Proof.
  intros.
  unfold map_from_ps.
  destruct field_type; simpl; apply PMap.gmap.
Qed.

(* Same as the above lemma for hdr and state *)
Transparent lookup_varlike.
Lemma commute_lookup_eval_hdr:
  forall h f s,
  lookup_varlike PSHeader (eval_sym_state s f) h =
  eval_smt_arith (lookup_varlike PSHeader s h) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.

Lemma commute_lookup_eval_state:
  forall sv f s,
  lookup_varlike PSState (eval_sym_state s f) sv =
  eval_smt_arith (lookup_varlike PSState s sv) f.
Proof.
  intros.
  apply PMap.gmap.
Qed.

Lemma ptree_of_list_lemma_generic:
    forall (X : Type) `(CrVarLike X)
    (l : list X) (val_fn : X -> SmtArithExpr)
    (x : X),
    Coqlib.list_norepet l ->
    In x l ->
    In x (map (fun '(key, _) => make_item key)
    (PTree.elements (PTree_Properties.of_list (combine (map get_key l) (map val_fn l))))).
Proof.
  intros X crvarlike l val_fn x H' H.
  generalize H as H_in.
  apply functional_list_helper with (key_fn := get_key) (val_fn := val_fn) in H.
  intros.
  remember (fun '(key, _) => make_item key) as f.
  assert(H_tmp: x =
          f (get_key x, val_fn (x))). {
  rewrite Heqf.
  Print CrVarLike.
  Check CrVarLike.
  Check inverses x.
  rewrite (inverses x).
  reflexivity. }
  rewrite H_tmp.
  apply in_map with (f := f) (x := (get_key x, val_fn x)) (l := (PTree.elements
  (PTree_Properties.of_list (combine (map get_key l) (map val_fn l))))).
  remember (get_key x, val_fn x) as pair_val.
  remember (combine (map get_key l) (map val_fn l)) as l_combined.
  rewrite Heqpair_val in *.
  apply PTree.elements_correct with (m := PTree_Properties.of_list l_combined).
  apply PTree_Properties.of_list_norepet.
  - rewrite Heql_combined.
    simpl.
    rewrite map_combine2.
    apply Coqlib.list_map_norepet.
    -- assumption.
    -- intros.
       apply (inj x0 y).
       assumption.
  - simpl in H. rewrite Heqf in H_tmp.
    rewrite H_tmp.
    rewrite inverses.
    assumption.
Qed.

Global Opaque lookup_varlike_map.