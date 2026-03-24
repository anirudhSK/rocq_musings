From Stdlib Require Import List.
Import ListNotations.

From MyProject Require Import CrMem.
From MyProject Require Import MyInts.

Axiom z3_sound_some:
  forall e sval aval f,
    z3_query e = Z3Sat sval aval f ->
    eval_z3_bool e sval aval = true.
Axiom z3_sound_none:
  forall e,
    z3_query e = Z3Unsat ->
    forall sval aval,
    eval_z3_bool e sval aval = false.

Lemma eval_neg:
  forall e sval aval,
    eval_z3_bool (Z3_Neg e) sval aval = negb (eval_z3_bool e sval aval).
Proof. reflexivity. Qed.
Lemma Inteqb_prop:
  forall {wordsize : BinNums.positive} (x y : @Integers.bit_int wordsize),
  Integers.eq x y = true -> x = y.
Proof.
  intros.
  unfold Integers.eq in H.
  destruct (Rocqlib.zeq (Integers.unsigned x) (Integers.unsigned y));
  try congruence.
  apply uintw_eq_from_unsigned in e.
  assumption.
Qed.
Lemma Intneqb_prop:
  forall {wordsize : BinNums.positive} (x y : @Integers.bit_int wordsize),
  Integers.eq x y = false -> x <> y.
Proof.
  intros.
  unfold Integers.eq in H.
  destruct (Rocqlib.zeq (Integers.unsigned x) (Integers.unsigned y));
  try congruence.
Qed.
Lemma eval_eq_true:
  forall e1 e2 sval aval,
  eval_z3_bool (Z3_Eq e1 e2) sval aval = true ->
  eval_z3_expr e1 sval aval = eval_z3_expr e2 sval aval.
Proof.
  intros.
  simpl in H.
  destruct (eval_z3_expr e1 sval aval), (eval_z3_expr e2 sval aval);
  simpl in H;
  try congruence.
  - unfold CrVal.iveqb in H.
    destruct val, val0; try congruence;
    apply Inteqb_prop in H; rewrite H;
    reflexivity.
  - destruct val; congruence.
  - destruct val, val0; try congruence.
    apply Inteqb_prop in H; rewrite H;
    reflexivity.
  - destruct val; congruence.
  - destruct val; congruence.
Qed.
Lemma eval_eq_false:
  forall e1 e2 sval aval,
  eval_z3_bool (Z3_Eq e1 e2) sval aval = false ->
  eval_z3_expr e1 sval aval <> eval_z3_expr e2 sval aval.
Proof.
  intros.
  simpl in H.
  destruct (eval_z3_expr e1 sval aval), (eval_z3_expr e2 sval aval);
  simpl in H;
  try congruence.
  - unfold CrVal.iveqb in H.
    destruct val, val0; try congruence;
    apply Intneqb_prop in H; injection;
    intros; congruence.
  - destruct val, val0; try congruence.
    apply Intneqb_prop in H. injection.
    intros. congruence.
Qed.
Lemma eval_conj:
  forall e1 e2 sval aval,
    eval_z3_bool (Z3_Conj e1 e2) sval aval =
    andb (eval_z3_bool e1 sval aval) (eval_z3_bool e2 sval aval).
Proof. reflexivity. Qed.
Lemma eval_bool_fold_lemma:
  forall {T} (f1 f2 : T -> TypedExpr Z3Expr) a A b B,
  fold_right Z3_Conj Z3_T
    (map (fun '((_, x), (_, y)) => Z3_Eq x y)
      (combine (map f1 (a :: A)) (map f2 (b :: B)))) =
  Z3_Conj
    (Z3_Eq (snd (f1 a)) (snd (f2 b)))
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine (map f1 A) (map f2 B)))).
Proof.
  intros. simpl. destruct (f1 a), (f2 b).
  reflexivity.
Qed.

Lemma eval_fold_conj_true:
  forall {T} (f1 f2 : T -> TypedExpr Z3Expr) l sval aval,
  eval_z3_bool
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine (map f1 l) (map f2 l)))) sval aval = true ->
  forall v,
    In v l -> eval_z3_expr (snd (f1 v)) sval aval = eval_z3_expr (snd (f2 v)) sval aval.
Proof.
  intros.
  induction l.
  - simpl in *. exfalso. assumption.
  - rewrite eval_bool_fold_lemma in H.
    rewrite eval_conj in H.
    apply andb_prop in H. destruct H as [Hfst Hrst].
    simpl in H0. destruct H0.
    + apply eval_eq_true in Hfst. rewrite H in Hfst.
      assumption.
    + apply IHl in Hrst; assumption.
Qed.

Definition matching_fn_io (p1 p2 : IM_Program) : Prop :=
  (fn_in p1) = (fn_in p2) /\
  (fn_out_vars p1) = (fn_out_vars p2) /\
  (fn_out_iaddrs p1) = (fn_out_iaddrs p2) /\
  (fn_out_vaddrs p1) = (fn_out_vaddrs p2).

Ltac unfold_query_expr H :=
  unfold query_expression in H;
  rewrite eval_neg in H;
  rewrite Bool.negb_false_iff in H;
  rewrite eval_conj in H;
  let Hqo := fresh "Hqo" in
  let Hqb := fresh "Hqb" in
  apply andb_prop in H; destruct H as [Hqo Hqb].

Definition matching_error (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val),
    errored (sym_eval_program p1) = errored (sym_eval_program p2).
Lemma mem_prog_soundness_error:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_error p1 p2.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_none with (e := query_expression p1 p2) as H1.
  unfold matching_error. intros.
  specialize (H1 H0 sval aval).
  unfold_query_expr H1.
  clear Hqb.
  unfold query_outputs in Hqo.
  rewrite eval_conj in Hqo.
  apply andb_prop in Hqo. destruct Hqo as [Herr Hval]. clear Hval.
  destruct (errored (sym_eval_program p1)) eqn:He1;
  destruct ((errored (sym_eval_program p2))) eqn:He2; auto.
Qed.

Definition matching_io_vars (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (v : var_id),
    In v (fn_out_vars p1) ->
    eval_z3_expr
      (snd ((var_val (sym_eval_program p1)) v))
      sval aval =
    eval_z3_expr
      (snd ((var_val (sym_eval_program p2)) v))
      sval aval.
Lemma mem_prog_soundness_io_vars:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_io_vars p1 p2.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_none with (e := query_expression p1 p2) as H1.
  unfold matching_io_vars. intros.
  specialize (H1 H0 sval aval).
  unfold_query_expr H1.
  clear Hqb.
  unfold query_outputs in Hqo.
  rewrite eval_conj in Hqo.
  apply andb_prop in Hqo. destruct Hqo as [Herr Hval]. clear Herr.
  rewrite eval_conj in Hval.
  apply andb_prop in Hval. destruct Hval as [Hio Hval]. clear Hval.
  rewrite <- H_v in Hio.
  rewrite eval_fold_conj_true with
    (f1 := var_val (sym_eval_program p1))
    (f2 := var_val (sym_eval_program p2))
    (l := fn_out_vars p1); auto.
Qed.

Definition matching_abs_addrs (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (ia : uintbptr) (ix1 : uint32),
    In (ia, ix1) (fn_out_iaddrs p1) ->
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p1)) (ia, ix1)))
      sval aval =
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p2)) (ia, ix1)))
      sval aval.
Lemma mem_prog_soundness_abs_addrs:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_abs_addrs p1 p2.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_none with (e := query_expression p1 p2) as H1.
  unfold matching_abs_addrs. intros.
  specialize (H1 H0 sval aval).
  unfold_query_expr H1.
  clear Hqb.
  unfold query_outputs in Hqo.
  rewrite eval_conj in Hqo.
  apply andb_prop in Hqo. destruct Hqo as [Herr Hval]. clear Herr.
  rewrite eval_conj in Hval.
  apply andb_prop in Hval. destruct Hval as [Hio Hval]. clear Hio.
  rewrite eval_conj in Hval.
  apply andb_prop in Hval. destruct Hval as [Hio Hval]. clear Hval.
  rewrite <- H_ia in Hio.
  rewrite eval_fold_conj_true with
    (f1 := iptr_val (sym_eval_program p1))
    (f2 := iptr_val (sym_eval_program p2))
    (l := fn_out_iaddrs p1); auto.
Qed.

Definition matching_var_addrs (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (va : var_id) (ix2 : uint32),
    In (va, ix2) (fn_out_vaddrs p1) ->
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p1)) (va, ix2)))
      sval aval =
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p2)) (va, ix2)))
      sval aval.
Lemma mem_prog_soundness_var_addrs:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_var_addrs p1 p2.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_none with (e := query_expression p1 p2) as H1.
  unfold matching_var_addrs. intros.
  specialize (H1 H0 sval aval).
  unfold_query_expr H1.
  clear Hqb.
  unfold query_outputs in Hqo.
  rewrite eval_conj in Hqo.
  apply andb_prop in Hqo. destruct Hqo as [Herr Hval]. clear Herr.
  rewrite eval_conj in Hval.
  apply andb_prop in Hval. destruct Hval as [Hio Hval]. clear Hio.
  rewrite eval_conj in Hval.
  apply andb_prop in Hval. destruct Hval as [Hio Hval]. clear Hio.
  rewrite <- H_va in Hval.
  rewrite eval_fold_conj_true with
    (f1 := vptr_val (sym_eval_program p1))
    (f2 := vptr_val (sym_eval_program p2))
    (l := fn_out_vaddrs p1); auto.
Qed.

Definition matching_access_bounds (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (va : var_id),
    (In va (List.map fst (List.filter (fun '(_, t) => match t with uintptr_t => true | _ => false end) (fn_in p1))) \/
     In va (List.map fst (fn_out_vaddrs p1))) ->
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p1)) va))
      sval aval =
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p2)) va))
      sval aval.
Lemma mem_prog_soundness_access_bounds:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_access_bounds p1 p2.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_none with (e := query_expression p1 p2) as H1.
  unfold matching_access_bounds. intros.
  specialize (H1 H0 sval aval).
  unfold_query_expr H1.
  clear Hqo.
  unfold query_bounds in Hqb.
  rewrite eval_fold_conj_true with
    (f1 := vptr_bound (sym_eval_program p1))
    (f2 := vptr_bound (sym_eval_program p2))
    (l := (map fst (filter (fun pat : var_id * ValType =>
      match pat with
      | (_, uintptr_t) => true
      | _ => false
      end) (fn_in p1))
      ++ map fst (fn_out_vaddrs p1))); auto.
  apply in_or_app in H. assumption.
Qed.

(*
For any two programs, p1 and p2,
If they have the same inputs and outputs,
and if Z3 cannot find a satisfying assignment,
then the two programs must:
- have the same static error behavior
- make the same variable assignments
- make the same memory assignments
- have the same memory access extents 
*)
Lemma mem_prog_soundness:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
    matching_error p1 p2 /\
    matching_io_vars p1 p2 /\
    matching_abs_addrs p1 p2 /\
    matching_var_addrs p1 p2 /\
    matching_access_bounds p1 p2.
Proof with assumption.
  intros. repeat split.
  - apply mem_prog_soundness_error...
  - apply mem_prog_soundness_io_vars...
  - apply mem_prog_soundness_abs_addrs...
  - apply mem_prog_soundness_var_addrs...
  - apply mem_prog_soundness_access_bounds...
Qed.

Definition differing_error (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  errored (sym_eval_program p1) <> errored (sym_eval_program p2).

Definition differing_io_vars (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (v : var_id),
    In v (fn_out_vars p1) /\
    eval_z3_expr
      (snd ((var_val (sym_eval_program p1)) v))
      sval aval <>
    eval_z3_expr
      (snd ((var_val (sym_eval_program p2)) v))
      sval aval.

Definition differing_abs_addrs (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (ia : uintbptr) (ix1 : uint32),
    In (ia, ix1) (fn_out_iaddrs p1) /\
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p1)) (ia, ix1)))
      sval aval <>
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p2)) (ia, ix1)))
      sval aval.

Definition differing_var_addrs (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (va : var_id) (ix2 : uint32),
    In (va, ix2) (fn_out_vaddrs p1) /\
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p1)) (va, ix2)))
      sval aval <>
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p2)) (va, ix2)))
      sval aval.

Definition differing_access_bounds (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (va : var_id),
    (In va (List.map fst (List.filter (fun '(_, t) => match t with uintptr_t => true | _ => false end) (fn_in p1))) \/
     In va (List.map fst (fn_out_vaddrs p1))) /\
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p1)) va))
      sval aval <>
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p2)) va))
      sval aval.

Lemma eval_fold_conj_false:
  forall {T} (f1 f2 : T -> TypedExpr Z3Expr) l sval aval,
  eval_z3_bool
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine (map f1 l) (map f2 l)))) sval aval = false ->
  exists v,
    In v l /\ eval_z3_expr (snd (f1 v)) sval aval <> eval_z3_expr (snd (f2 v)) sval aval.
Proof.
  intros.
  induction l.
  - simpl in *. congruence.
  - rewrite eval_bool_fold_lemma in H.
    rewrite eval_conj in H.
    apply Bool.andb_false_iff in H. destruct H as [Hfst | Hrst].
    + exists a. split.
      * simpl. left. reflexivity.
      * apply eval_eq_false in Hfst. assumption.
    + apply IHl in Hrst.
      destruct Hrst. destruct H.
      exists x. split.
      * simpl. right. assumption.
      * assumption.
Qed.

Lemma mem_prog_completeness_error:
  forall p1 p2 sval aval,
  eval_z3_bool
    (if
      (errored (sym_eval_program p1) && errored (sym_eval_program p2)
      || negb (errored (sym_eval_program p1))
      && negb (errored (sym_eval_program p2)))%bool
    then Z3_T
    else Z3_F) sval aval = false ->
  differing_error p1 p2 sval aval.
Proof.
  intros.
  unfold differing_error.
  destruct ((errored (sym_eval_program p1) && errored (sym_eval_program p2)
    || negb (errored (sym_eval_program p1)) &&
    negb (errored (sym_eval_program p2)))%bool) eqn:Hcond; simpl in H; try congruence.
  apply Bool.orb_false_elim in Hcond. destruct Hcond.
  apply Bool.andb_false_iff in H0, H1.
  repeat rewrite Bool.negb_false_iff in H1.
  destruct H0, H1; congruence.
Qed.

Lemma mem_prog_completeness_io_vars:
  forall p1 p2 sval aval,
  eval_z3_bool
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine
          (map (var_val (sym_eval_program p1)) (fn_out_vars p1))
          (map (var_val (sym_eval_program p2)) (fn_out_vars p1))))
    ) sval aval = false ->
  differing_io_vars p1 p2 sval aval.
Proof.
  intros.
  apply eval_fold_conj_false in H. assumption.
Qed.

Lemma mem_prog_completeness_abs_addrs:
  forall p1 p2 sval aval,
  eval_z3_bool
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine
          (map (iptr_val (sym_eval_program p1)) (fn_out_iaddrs p1))
          (map (iptr_val (sym_eval_program p2)) (fn_out_iaddrs p1))))
    ) sval aval = false ->
  differing_abs_addrs p1 p2 sval aval.
Proof.
  intros.
  apply eval_fold_conj_false in H.
  destruct H. destruct x.
  unfold differing_abs_addrs.
  exists u. exists u0.
  assumption.
Qed.

Lemma mem_prog_completeness_var_addrs:
  forall p1 p2 sval aval,
  eval_z3_bool
    (fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y)
        (combine
          (map (vptr_val (sym_eval_program p1)) (fn_out_vaddrs p1))
          (map (vptr_val (sym_eval_program p2)) (fn_out_vaddrs p1))))
    ) sval aval = false ->
  differing_var_addrs p1 p2 sval aval.
Proof.
  intros.
  apply eval_fold_conj_false in H.
  destruct H. destruct x.
  unfold differing_var_addrs.
  exists v. exists u.
  assumption.
Qed.

(*
For any two programs, p1 and p2,
If Z3 returns a satisfying assignment, that is,
- a specific scalar variable valuation (sval)
- a specific array variable valuation (aval)
- a specific failure mode under those valuations (f)
Then the two program must either
- lead to different static errors
- lead to different final variable assignments
- lead to different final memory assignments
- lead to different memory access extents
*)
Lemma mem_prog_completeness:
  forall (p1 p2 : IM_Program) sval aval f,
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Sat sval aval f ->
  differing_error p1 p2 sval aval \/
  differing_io_vars p1 p2 sval aval \/
  differing_abs_addrs p1 p2 sval aval \/
  differing_var_addrs p1 p2 sval aval \/
  differing_access_bounds p1 p2 sval aval.
Proof.
  intros.
  unfold matching_fn_io in H.
  destruct H as [H_in [H_v [H_ia H_va]]].
  specialize z3_sound_some with (e := query_expression p1 p2) as H1.
  specialize (H1 sval aval f H0).
  unfold query_expression in H1.
  rewrite eval_neg in H1.
  rewrite Bool.negb_true_iff in H1.
  rewrite eval_conj in H1.
  rewrite Bool.andb_false_iff in H1.
  destruct H1 as [Hqo | Hqb].
  - unfold query_outputs in Hqo.
    rewrite eval_conj in Hqo. rewrite Bool.andb_false_iff in Hqo.
    destruct Hqo as [Herr | Hqo].
  + left.
    apply mem_prog_completeness_error. assumption.

  + rewrite eval_conj in Hqo. rewrite Bool.andb_false_iff in Hqo.
    destruct Hqo as [Hvar | Hqo].
  * right. left.
    rewrite <- H_v in Hvar.
    apply mem_prog_completeness_io_vars. assumption.

  * rewrite eval_conj in Hqo. rewrite Bool.andb_false_iff in Hqo.
    destruct Hqo as [Hia | Hva].
 ** right. right. left.
    rewrite <- H_ia in Hia.
    apply mem_prog_completeness_abs_addrs. assumption.

 ** right. right. right. left.
    rewrite <- H_va in Hva.
    apply mem_prog_completeness_var_addrs. assumption.

  - right. right. right. right.
    unfold query_bounds in Hqb.
    apply eval_fold_conj_false in Hqb.
    destruct Hqb. destruct H.
    apply in_app_or in H.
    unfold differing_access_bounds.
    exists x. split; assumption.
Qed.
