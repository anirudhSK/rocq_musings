From MyProject Require Import SmtExpr.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import Maps.
From MyProject Require Import UtilLemmas.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
Require Import Coq.Lists.List.
Require Import ZArith.

Transparent map_from_ps.
Transparent lookup_varlike_map.

Class CrVarLikeEval (A: Type) `(CrVarLike A) := {
  test : A;
  commute_lookup_eval_generic:
  forall (v : A) f ps,
  lookup_varlike_map (map_from_ps (eval_sym_state ps f)) v =
  eval_smt_arith (lookup_varlike_map (map_from_ps ps) v) f;
}.

Instance CrVarLikeEval_Header : CrVarLikeEval Header CrVarLike_Header.
Proof.
  refine {| test := HeaderCtr xH;|}. (* TODO: Another hack, unsued *)
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

Instance CrVarLikeEval_State : CrVarLikeEval State CrVarLike_State.
Proof.
  refine {| test := StateCtr xH;|}. (* TODO: Another hack, unsued *)
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

Instance CrVarLikeEval_Ctrl : CrVarLikeEval Ctrl CrVarLike_Ctrl.
Proof.
  refine {| test := CtrlCtr xH;|}. (* TODO: Another hack, unsued *)
  intros. unfold map_from_ps. apply PMap.gmap.
Defined.

(* Same as the above lemma for hdr and state *)
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