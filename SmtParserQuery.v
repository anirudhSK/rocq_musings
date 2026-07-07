(* Parser-vs-parser equivalence checking.                                     *)
(*                                                                            *)
(* Analogous to [equivalence_checker_cr_dsl] for transformers, but a parser's *)
(* interface is (packet bits -> headers) and its observable result includes    *)
(* accept/reject.  Two parsers are equivalent over a header interface and a    *)
(* packet length when, for every input packet of that length (and every        *)
(* initial header valuation), they (a) accept the same packets and (b) agree   *)
(* on every interface header whenever they both accept.                        *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import SmtQuery.
From MyProject Require Import Maps.
From MyProject Require Import ParserCommuteLemmas.

(* Every interface header agrees across the two final (symbolic) header maps. *)
Definition headers_agree_symbolic
    (hm1 hm2 : PMap.t SmtArithExpr) (headers : list Header) : SmtBoolExpr :=
  List.fold_right
    (fun h acc =>
       SmtBoolAnd acc
         (SmtBoolEq (lookup_varlike_map hm1 h) (lookup_varlike_map hm2 h)))
    SmtTrue headers.

(* The non-equivalence query: SAT witnesses a packet on which the parsers
   differ.  They differ if their accept conditions disagree (XOR), or if they
   both accept but some interface header ends up different. *)
Definition parser_neq_query
    (r1 r2 : SymParserResult) (headers : list Header) : SmtBoolExpr :=
  let a1 := spr_accept r1 in
  let a2 := spr_accept r2 in
  let accept_differs := smt_bool_ite a1 (SmtBoolNot a2) a2 in   (* a1 XOR a2 *)
  let both_accept    := SmtBoolAnd a1 a2 in
  let hdrs_differ    :=
    SmtBoolNot (headers_agree_symbolic (spr_headers r1) (spr_headers r2) headers) in
  SmtBoolOr accept_differs (SmtBoolAnd both_accept hdrs_differ).

(* Check two parsers for equivalence over the given header interface and a
   packet of exactly [packet_len] bits.  Both are run symbolically from the same
   start state, so they range over one common input packet. *)
Definition parser_equivalence_checker
    (headers : list Header) (packet_len : nat) (p1 p2 : Parser)
    : EquivalenceResult :=
  let ps := init_symbolic_parser_state_n headers packet_len in
  let r1 := eval_parser_symbolic_acc p1 ps in
  let r2 := eval_parser_symbolic_acc p2 ps in
  match smt_query (parser_neq_query r1 r2 headers) with
  | SmtUnsat  => Equivalent
  | SmtSat f  => NotEquivalent f
  | SmtUnknown => NotEquivalentUnknown
  end.

(* --- The [parser_neq_query] boolean, evaluated, splits into an accept-XOR and a
   both-accept/headers-differ conjunct. --- *)
Lemma eval_parser_neq_query :
  forall r1 r2 headers f,
    eval_smt_bool (parser_neq_query r1 r2 headers) f =
    orb (xorb (eval_smt_bool (spr_accept r1) f) (eval_smt_bool (spr_accept r2) f))
        (andb (andb (eval_smt_bool (spr_accept r1) f) (eval_smt_bool (spr_accept r2) f))
              (negb (eval_smt_bool
                       (headers_agree_symbolic (spr_headers r1) (spr_headers r2) headers) f))).
Proof.
  intros r1 r2 headers f.
  unfold parser_neq_query, smt_bool_ite.
  cbn [eval_smt_bool].
  destruct (eval_smt_bool (spr_accept r1) f), (eval_smt_bool (spr_accept r2) f);
    reflexivity.
Qed.

(* [headers_agree_symbolic] on a cons unfolds definitionally. *)
Lemma headers_agree_cons :
  forall hm1 hm2 h0 rest,
    headers_agree_symbolic hm1 hm2 (h0 :: rest) =
    SmtBoolAnd (headers_agree_symbolic hm1 hm2 rest)
               (SmtBoolEq (lookup_varlike_map hm1 h0) (lookup_varlike_map hm2 h0)).
Proof. reflexivity. Qed.

(* If the header-agreement query holds under [f], every interface header agrees. *)
Lemma eval_headers_agree_true :
  forall headers hm1 hm2 f,
    eval_smt_bool (headers_agree_symbolic hm1 hm2 headers) f = true ->
    forall h, In h headers ->
      eval_smt_arith (lookup_varlike_map hm1 h) f =
      eval_smt_arith (lookup_varlike_map hm2 h) f.
Proof.
  induction headers as [| h0 rest IH]; intros hm1 hm2 f Hall h Hin.
  - inversion Hin.
  - rewrite headers_agree_cons in Hall. cbn [eval_smt_bool] in Hall.
    apply andb_true_iff in Hall as [Hrest Hh0].
    destruct Hin as [Heq | Hin'].
    + subst h0. apply crval_concrete_if_else. exact Hh0.
    + apply IH; assumption.
Qed.

(* ...and if it fails, some interface header disagrees. *)
Lemma eval_headers_agree_false :
  forall headers hm1 hm2 f,
    eval_smt_bool (headers_agree_symbolic hm1 hm2 headers) f = false ->
    exists h, In h headers /\
      eval_smt_arith (lookup_varlike_map hm1 h) f <>
      eval_smt_arith (lookup_varlike_map hm2 h) f.
Proof.
  induction headers as [| h0 rest IH]; intros hm1 hm2 f Hall.
  - discriminate Hall.
  - rewrite headers_agree_cons in Hall. cbn [eval_smt_bool] in Hall.
    apply andb_false_iff in Hall as [Hrest | Hh0].
    + destruct (IH hm1 hm2 f Hrest) as [h [Hin Hne]].
      exists h. split; [ right; exact Hin | exact Hne ].
    + exists h0. split; [ left; reflexivity | ].
      apply crval_concrete_if_else2. exact Hh0.
Qed.


(* Soundness: if the checker calls two parsers equivalent, then on the [f]-
   concretization of their shared symbolic start state they accept the same packet
   and, whenever both accept, agree on every interface header. *)
Lemma parser_equivalence_checker_sound :
  forall headers packet_len p1 p2 f,
    parser_equivalence_checker headers packet_len p1 p2 = Equivalent ->
    let ps := eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f in
    (eval_parser_concrete p1 ps = None <-> eval_parser_concrete p2 ps = None) /\
    (forall ps1 ps2,
       eval_parser_concrete p1 ps = Some ps1 ->
       eval_parser_concrete p2 ps = Some ps2 ->
       forall h, In h headers ->
         lookup_varlike_map (p_header_map ps1) h =
         lookup_varlike_map (p_header_map ps2) h).
Proof.
  intros headers packet_len p1 p2 f Hchk. cbv zeta.
  unfold parser_equivalence_checker in Hchk.
  destruct (smt_query (parser_neq_query
              (eval_parser_symbolic_acc p1 (init_symbolic_parser_state_n headers packet_len))
              (eval_parser_symbolic_acc p2 (init_symbolic_parser_state_n headers packet_len))
              headers)) eqn:Hq; try discriminate.
  pose proof (smt_query_sound_none _ Hq f) as Hfalse.
  rewrite eval_parser_neq_query in Hfalse.
  apply orb_false_iff in Hfalse as [Hxor Hand].
  pose proof (eval_parser_commute headers packet_len p1 f) as C1.
  pose proof (eval_parser_commute headers packet_len p2 f) as C2.
  split.
  - (* accept/reject agree *)
    destruct (eval_parser_concrete p1
                (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f)) as [cps1|] eqn:E1;
    destruct (eval_parser_concrete p2
                (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f)) as [cps2|] eqn:E2.
    + split; intro H; discriminate H.
    + destruct C1 as [Hba1 _]. rewrite Hba1, C2 in Hxor. discriminate Hxor.
    + destruct C2 as [Hba2 _]. rewrite C1, Hba2 in Hxor. discriminate Hxor.
    + tauto.
  - (* both accept -> every interface header agrees *)
    intros ps1 ps2 Hs1 Hs2 h Hin.
    rewrite Hs1 in C1. destruct C1 as [Hba1 rel1].
    rewrite Hs2 in C2. destruct C2 as [Hba2 rel2].
    rewrite Hba1, Hba2 in Hand. cbn in Hand. apply negb_false_iff in Hand.
    rewrite (rel1 h Hin), (rel2 h Hin).
    apply (eval_headers_agree_true headers _ _ f Hand h Hin).
Qed.

(* Completeness: if the checker reports [NotEquivalent f], then on the packet
   witnessed by [f] the two parsers observably differ — either one accepts and the
   other rejects, or both accept but some interface header ends up different.
   ([eval_sym_parser_state] preserves packet length, so this witness has exactly
   [packet_len] bits.) *)
Lemma parser_equivalence_checker_complete :
  forall headers packet_len p1 p2 f,
    parser_equivalence_checker headers packet_len p1 p2 = NotEquivalent f ->
    let ps := eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f in
    (exists ps1, eval_parser_concrete p1 ps = Some ps1 /\ eval_parser_concrete p2 ps = None) \/
    (exists ps2, eval_parser_concrete p1 ps = None /\ eval_parser_concrete p2 ps = Some ps2) \/
    (exists ps1 ps2 h,
       eval_parser_concrete p1 ps = Some ps1 /\
       eval_parser_concrete p2 ps = Some ps2 /\
       In h headers /\
       lookup_varlike_map (p_header_map ps1) h <> lookup_varlike_map (p_header_map ps2) h).
Proof.
  intros headers packet_len p1 p2 f Hchk. cbv zeta.
  unfold parser_equivalence_checker in Hchk.
  destruct (smt_query (parser_neq_query
              (eval_parser_symbolic_acc p1 (init_symbolic_parser_state_n headers packet_len))
              (eval_parser_symbolic_acc p2 (init_symbolic_parser_state_n headers packet_len))
              headers)) eqn:Hq; try discriminate.
  injection Hchk as Hf. subst f0.
  pose proof (smt_query_sound_some _ _ Hq) as Htrue.
  rewrite eval_parser_neq_query in Htrue.
  pose proof (eval_parser_commute headers packet_len p1 f) as C1.
  pose proof (eval_parser_commute headers packet_len p2 f) as C2.
  destruct (eval_parser_concrete p1
              (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f)) as [cps1|] eqn:E1;
  destruct (eval_parser_concrete p2
              (eval_sym_parser_state (init_symbolic_parser_state_n headers packet_len) f)) as [cps2|] eqn:E2.
  - (* both accept: some interface header differs *)
    right. right.
    destruct C1 as [Hba1 rel1]. destruct C2 as [Hba2 rel2].
    rewrite Hba1, Hba2 in Htrue. cbn in Htrue. apply negb_true_iff in Htrue.
    destruct (eval_headers_agree_false headers _ _ f Htrue) as [h [Hin Hne]].
    exists cps1, cps2, h. split; [ reflexivity | ]. split; [ reflexivity | ].
    split; [ exact Hin | ]. rewrite (rel1 h Hin), (rel2 h Hin). exact Hne.
  - (* p1 accepts, p2 rejects *)
    left. exists cps1. split; reflexivity.
  - (* p1 rejects, p2 accepts *)
    right. left. exists cps2. split; reflexivity.
  - (* both reject: the query could not have been satisfiable *)
    rewrite C1, C2 in Htrue. cbn in Htrue. discriminate Htrue.
Qed.
