(* Compiling a query into the core fragment.

   [SmtExpr] is a rich language: an arith term denotes a [CrVal], which carries
   an integer TYPE beside its bits, and every operation type-checks its
   operands.  A bitvector solver has none of that.  Bridging the two is real
   work -- masking to widths, propagating [ErrorVal], guarding a partial
   [ld_arr] against a total [select] -- and it used to be done in
   [extracted_code/Z3Solver.ml], in OCaml, where nothing related it to the
   definitions in [CrVal.v] that it was reproducing.  Getting it wrong there
   made [SmtQuery.smt_query_sound_some] FALSE for the real solver rather than
   merely imprecise: an untyped lowering returned [NotEquivalent] on models
   [eval_smt_bool] rejects.

   This file moves that work into Rocq.  [compile_bool] rewrites a query into
   the CORE FRAGMENT -- the sublanguage whose every node has a direct Z3
   counterpart -- so the extracted lowering becomes a transliteration.  The
   fragment is a subset of [SmtExpr], not a new type, so there is one syntax,
   one evaluator and one theorem shape:

     eval_smt_bool (compile_bool e) v = eval_smt_bool e v

   No second semantics to define, and no encoding relation between two
   valuations to get right -- both sides are read by the same [eval_smt_bool]
   under the SAME valuation.  That is what the five core constructors in
   [SmtExpr.v] buy: [SmtVarVal]/[SmtVarTag] split a variable in the SYNTAX
   rather than splitting the valuation.

   WHY THE FRAGMENT COLLAPSES ONTO QF_BV.  Every core arith term denotes
   [IntVal _ u64].  At [u64] the rich operations are exactly their bitvector
   counterparts: [mask_width W64] is the identity, so [add_at u64] is [bvadd];
   [eqb] on two [u64]s is [crinttype_eqb u64 u64 && Integers.eq], i.e. bitvector
   equality; and [ltb] is [Integers.ltu], i.e. [bvult].  So the fragment needs
   no constructors of its own for arithmetic -- it reuses [SmtBitAdd u64] and
   friends, which the lowering can emit unconditionally.

   WHAT IS NOT COMPILED, and stays a trusted correspondence:

   - [SmtArrEq].  Z3's array equality is extensional; Rocq cannot compute
     extensional equality of a function, so [arr_agree_upto] takes a bound.
     Compiling it to a bounded conjunction WOULD be faithful and is what this
     checker used to do -- it was quadratic and put any program that rewrites a
     header out of reach (32 cells against 4 stores: 125s, against 0.02s for the
     extensional form).  So this one node keeps its existing justification: both
     sides of every merge the checker builds are rooted at the same [SmtArrVar],
     so extensional and bounded equality coincide.  See SOUNDNESS.md.
   - The free-variable side constraints in [Z3Solver.solve], which pin a region's
     cells and a scalar's tag into the range [CrVal] can denote.  They are
     assertions about a MODEL, not part of any expression; making them query
     conjuncts is a separate change.
   - [SmtBitDiv]'s zero-divisor guard, which stays in the lowering because it is
     one line and provably the right one: [Integers.divu] is [Z.div], and
     [Z.div _ 0 = 0], where [bvudiv] by zero is all-ones. *)

From MyProject Require Import SmtTypes.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From MyProject Require Import Coqlib.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From Stdlib.Strings Require Import String.
From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.
From Stdlib Require Import List.
Import ListNotations.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(* Core term builders.                                                  *)

(* A 64-bit word constant. *)
Definition cw (z : Z) : SmtArithExpr := SmtArithConst (repr z) u64.

Definition tag_z (ty : CrIntType) : Z :=
  match it_width ty with W8 => 2 | W16 => 3 | W32 => 4 | W64 => 5 end.

(* ------------------------------------------------------------------ *)
(* Sharing the fixed literals.

   [cw] BUILDS a node, so every occurrence of [cw 2] in this file is a distinct
   [SmtArithConst] once extracted -- and the lowering memo compares by physical
   identity, so each one became its own Z3 numeral.  On a fuzzed tuple-space
   query that was 23k constant nodes standing for about twenty values, a third
   of the whole term.

   Naming them makes extraction emit ONE value per literal, shared by every
   use.  Each is convertible with the [cw] application it replaces, so nothing
   downstream has to change -- the proofs below [unfold] them exactly as they
   unfolded [cw]. *)
Definition c_two  : SmtArithExpr := cw 2.
Definition c_six  : SmtArithExpr := cw 6.
Definition c_tag8 : SmtArithExpr := cw 2.
Definition c_tag16 : SmtArithExpr := cw 3.
Definition c_tag32 : SmtArithExpr := cw 4.
Definition c_tag64 : SmtArithExpr := cw 5.

(* [cw (tag_z ty)] with the four results shared. *)
Definition ctag (ty : CrIntType) : SmtArithExpr :=
  match it_width ty with
  | W8 => c_tag8 | W16 => c_tag16 | W32 => c_tag32 | W64 => c_tag64
  end.

Lemma ctag_cw : forall ty, ctag ty = cw (tag_z ty).
Proof. intro ty. unfold ctag, tag_z, c_tag8, c_tag16, c_tag32, c_tag64.
       destruct (it_width ty); reflexivity. Qed.

(* Mask a word into [ty]'s width.  [W64] is the identity rather than an
   [and] with all-ones so the compiled term does not grow for the common case. *)
Definition c_ones8  : SmtArithExpr := cw (Z.ones (width_bits W8)).
Definition c_ones16 : SmtArithExpr := cw (Z.ones (width_bits W16)).
Definition c_ones32 : SmtArithExpr := cw (Z.ones (width_bits W32)).

Definition cmask (ty : CrIntType) (e : SmtArithExpr) : SmtArithExpr :=
  match it_width ty with
  | W64 => e
  | W8  => SmtBitAnd u64 e c_ones8
  | W16 => SmtBitAnd u64 e c_ones16
  | W32 => SmtBitAnd u64 e c_ones32
  end.

(* [2 <= t <= 5]: the tag says [IntVal].  Written with [<] alone because that
   is the one comparison the fragment has. *)
Definition is_int_tag (t : SmtArithExpr) : SmtBoolExpr :=
  SmtBoolAnd (SmtBoolNot (SmtBoolLt t c_two)) (SmtBoolLt t c_six).

Definition tag_is (t : SmtArithExpr) (ty : CrIntType) : SmtBoolExpr :=
  SmtBoolEq t (ctag ty).

(* ------------------------------------------------------------------ *)
(* Folding smart constructors.

   Every case of the compiler below builds its node through one of these
   instead of through the raw constructor.  Each is EXTENSIONALLY the raw
   constructor -- the [_eval] lemma beside it says exactly that -- so the
   correctness proof rewrites them away and then proceeds as before; what they
   change is only how big the term is.

   Why this is worth a smart constructor at all: a compiled comparison is
   [and (eq t1 t2) (or (not (is_int_tag t1)) (eq v1 v2))], and in a well-typed
   program both tags are the SAME LITERAL.  Folding turns that eleven-node term
   into [eq v1 v2].  Nothing here inspects a term deeply -- every test is on a
   constructor or on two [SmtArithConst] leaves -- so none of it walks the DAG,
   which is what makes it safe to do here at all. *)

Definition bool_lit (b : bool) : SmtBoolExpr := if b then SmtTrue else SmtFalse.

(* What [SmtArithConst] denotes.  It is [mk_int], not [IntVal]: the constant is
   masked into its own width first, so a fold that compared the raw words would
   be wrong on an out-of-range literal. *)
Definition lit_val (x : uint64) (ty : CrIntType) : CrVal := mk_int ty (unsigned x).

Lemma lit_val_eval : forall x ty v,
  eval_smt_arith (SmtArithConst x ty) v = lit_val x ty.
Proof. reflexivity. Qed.

Lemma bool_lit_eval : forall b v, eval_smt_bool (bool_lit b) v = b.
Proof. destruct b; reflexivity. Qed.

Definition mk_not (e : SmtBoolExpr) : SmtBoolExpr :=
  match e with
  | SmtTrue => SmtFalse
  | SmtFalse => SmtTrue
  | SmtBoolNot e1 => e1
  | _ => SmtBoolNot e
  end.

Lemma mk_not_eval : forall e v,
  eval_smt_bool (mk_not e) v = negb (eval_smt_bool e v).
Proof.
  intros e v. destruct e; try reflexivity.
  cbn [mk_not eval_smt_bool]. rewrite negb_involutive. reflexivity.
Qed.

Definition mk_and (a b : SmtBoolExpr) : SmtBoolExpr :=
  match a with
  | SmtFalse => SmtFalse
  | SmtTrue => b
  | _ => match b with
         | SmtFalse => SmtFalse
         | SmtTrue => a
         | _ => SmtBoolAnd a b
         end
  end.

Lemma mk_and_eval : forall a b v,
  eval_smt_bool (mk_and a b) v = (eval_smt_bool a v && eval_smt_bool b v)%bool.
Proof.
  intros a b v. destruct a; cbn [mk_and];
    try (rewrite andb_true_l; reflexivity);
    try (rewrite andb_false_l; reflexivity);
    destruct b; cbn [eval_smt_bool];
    try (rewrite andb_true_r; reflexivity);
    try (rewrite andb_false_r; reflexivity);
    reflexivity.
Qed.

Definition mk_or (a b : SmtBoolExpr) : SmtBoolExpr :=
  match a with
  | SmtTrue => SmtTrue
  | SmtFalse => b
  | _ => match b with
         | SmtTrue => SmtTrue
         | SmtFalse => a
         | _ => SmtBoolOr a b
         end
  end.

Lemma mk_or_eval : forall a b v,
  eval_smt_bool (mk_or a b) v = (eval_smt_bool a v || eval_smt_bool b v)%bool.
Proof.
  intros a b v. destruct a; cbn [mk_or];
    try (rewrite orb_true_l; reflexivity);
    try (rewrite orb_false_l; reflexivity);
    destruct b; cbn [eval_smt_bool];
    try (rewrite orb_true_r; reflexivity);
    try (rewrite orb_false_r; reflexivity);
    reflexivity.
Qed.

(* Are these the SAME literal?  Only two [SmtArithConst] leaves are compared,
   so this is O(1) and never descends -- a structural equality on arbitrary
   [SmtArithExpr] would walk a DAG as a tree, which is the blow-up the
   [cstep]/[compile] split exists to avoid. *)
Definition lit_eqb (a b : SmtArithExpr) : bool :=
  match a, b with
  | SmtArithConst x tx, SmtArithConst y ty =>
      (crinttype_eqb tx ty && Integers.eq x y)%bool
  | _, _ => false
  end.

Lemma lit_eqb_eval : forall a b v,
  lit_eqb a b = true -> eval_smt_arith a v = eval_smt_arith b v.
Proof.
  intros a b v H. destruct a; try discriminate. destruct b; try discriminate.
  cbn [lit_eqb] in H. apply andb_prop in H as [Hty Hv].
  apply crinttype_eqb_true in Hty. apply int_eq_true in Hv. subst.
  reflexivity.
Qed.

(* [ite c k k] denotes [k] whichever way [c] goes.  Restricted to a literal [k]
   for the reason on [lit_eqb]: that is the case that actually fires, because
   the two branches of a merged TAG are usually the same shared literal. *)
Definition mk_ite (c : SmtBoolExpr) (t f : SmtArithExpr) : SmtArithExpr :=
  match c with
  | SmtTrue => t
  | SmtFalse => f
  | _ => if lit_eqb t f then t else SmtConditional c t f
  end.

Lemma mk_ite_eval : forall c t f v,
  eval_smt_arith (mk_ite c t f) v =
    (if eval_smt_bool c v then eval_smt_arith t v else eval_smt_arith f v).
Proof.
  intros c t f v.
  destruct c; try reflexivity;
    (cbn [mk_ite]; destruct (lit_eqb t f) eqn:Hl;
     [ rewrite (lit_eqb_eval t f v Hl); destruct (eval_smt_bool _ v); reflexivity
     | reflexivity ]).
Qed.

(* ------------------------------------------------------------------ *)
(* Deciding [is_int_tag] on a tag the compiler built itself.

   A tag half is a literal, or a merge of tag halves.  [tag_decide] answers
   "every leaf of this tag is in 2..5" / "none is", and [None] as soon as the
   leaves disagree or a leaf is not a literal.  When it answers, the guard --
   and with it the whole comparison wrapped around it -- collapses.

   It recurses only through [SmtConditional], and a tag spine is built by the
   compiler rather than by the program, so it is short.  The [None] answer
   short-circuits, so a spine that cannot fold is abandoned at its first
   non-literal leaf. *)
(* [is_int_tag] reads its argument only through its VALUE, which is what lets
   [tag_decide] push through a merge. *)
Definition itv (x : CrVal) : bool :=
  (negb (CrVal.ltb x (IntVal (repr 2) u64)) && CrVal.ltb x (IntVal (repr 6) u64))%bool.

(* FUEL, and it is not a formality.  A tag is a DAG -- the merge at every rule
   shares its branches -- and a structural walk visits a shared subterm once
   per PATH, which is the blow-up the [cstep]/[compile] split exists to avoid.
   Rather than memoise a second traversal, this one is simply not allowed to be
   deep: running out returns [None], the answer that folds nothing, so the
   bound costs precision and never soundness.

   Depth 8 is enough in practice because [mk_ite] has already collapsed
   [ite c k k] to [k], so a spine only survives where the branches genuinely
   differ. *)
Fixpoint tag_decide (fuel : nat) (t : SmtArithExpr) : option bool :=
  match fuel with
  | O => None
  | S fuel' =>
      match t with
      | SmtArithConst x ty => Some (itv (lit_val x ty))
      | SmtConditional _ a b =>
          match tag_decide fuel' a with
          | None => None
          | Some xa =>
              match tag_decide fuel' b with
              | None => None
              | Some xb =>
                  (* agreeing leaves only; written out rather than with
                     [Bool.eqb] so extraction pulls in no extra module *)
                  match xa, xb with
                  | true, true => Some true
                  | false, false => Some false
                  | _, _ => None
                  end
              end
          end
      | _ => None
      end
  end.

Definition tag_fuel : nat := 8.

Definition mk_int_tag (t : SmtArithExpr) : SmtBoolExpr :=
  match tag_decide tag_fuel t with
  | Some b => bool_lit b
  | None => is_int_tag t
  end.

(* Comparisons between two literals decide.  Same O(1) restriction as
   [lit_eqb]: only [SmtArithConst] leaves are looked at. *)
Definition mk_beq (a b : SmtArithExpr) : SmtBoolExpr :=
  match a, b with
  | SmtArithConst x tx, SmtArithConst y ty =>
      bool_lit (CrVal.eqb (lit_val x tx) (lit_val y ty))
  | _, _ => SmtBoolEq a b
  end.

Lemma mk_beq_eval : forall a b v,
  eval_smt_bool (mk_beq a b) v = eval_smt_bool (SmtBoolEq a b) v.
Proof.
  intros a b v. destruct a; try reflexivity. destruct b; try reflexivity.
  cbn [mk_beq]. rewrite bool_lit_eval.
  cbn [eval_smt_bool]. rewrite !lit_val_eval.
  match goal with |- _ = (if ?g then _ else _) => destruct g end; reflexivity.
Qed.

Definition mk_blt (a b : SmtArithExpr) : SmtBoolExpr :=
  match a, b with
  | SmtArithConst x tx, SmtArithConst y ty =>
      bool_lit (CrVal.ltb (lit_val x tx) (lit_val y ty))
  | _, _ => SmtBoolLt a b
  end.

Lemma mk_blt_eval : forall a b v,
  eval_smt_bool (mk_blt a b) v = eval_smt_bool (SmtBoolLt a b) v.
Proof.
  intros a b v. destruct a; try reflexivity. destruct b; try reflexivity.
  cbn [mk_blt]. rewrite bool_lit_eval.
  cbn [eval_smt_bool]. rewrite !lit_val_eval. reflexivity.
Qed.

Definition err_tag : SmtArithExpr := cw 0.
Definition zero_w : SmtArithExpr := err_tag.

(* A compiled arith term is the PAIR (value, tag); [mk_cell] of the two is the
   [CrVal] the original denoted.  Note the value half is only constrained where
   the tag says [IntVal] -- [mk_cell _ 0] is [ErrorVal] whatever the value is --
   which is why the cases below can leave a masked value under an error tag
   rather than forcing it to zero. *)
Definition carith : Type := (SmtArithExpr * SmtArithExpr)%type.

(* [iv_binop_at] requires BOTH operands to already carry the operation's type,
   computes at 64 bits and masks into that width.  The value is computed
   unconditionally: under a mismatch the tag is [tag_err] and [mk_cell] discards
   the value, so there is nothing to guard.

   Takes the already-compiled operands rather than the source ones, so it is an
   ordinary definition -- a mutual fixpoint arm taking [e1 e2] would have no
   decreasing argument of its own. *)
Definition mk_binop (ty : CrIntType)
    (op : CrIntType -> SmtArithExpr -> SmtArithExpr -> SmtArithExpr)
    (p1 p2 : carith) : carith :=
  let (v1, t1) := p1 in
  let (v2, t2) := p2 in
  (cmask ty (op u64 v1 v2),
   mk_ite (mk_and (tag_is t1 ty) (tag_is t2 ty)) (ctag ty) err_tag).

(* The value half of a compiled pair, forced to zero where the tag says the
   term is not an integer.  [CrVal.val_of] is 0 on [UninitVal] and [ErrorVal],
   so a context that reads a compiled value directly -- rather than through
   [mk_cell], which discards it under a non-integer tag -- has to reproduce
   that.  Only [SmtStCell] below needs it. *)
Definition vguard (p : carith) : SmtArithExpr :=
  let (v, t) := p in mk_ite (mk_int_tag t) v zero_w.

(* ------------------------------------------------------------------ *)
(* The compiler.                                                        *)

(* The compiler, one layer at a time.

   [cstep_*] is the compiler for a SINGLE node, taking the compilers for its
   children as arguments.  Tying the knot purely gives [compile_*] below, which
   is what the correctness theorem is about; tying it in OCaml with a memo table
   gives the same function without re-traversing shared subterms.

   That split is not a nicety.  A query is a DAG -- a transformer chain merges
   at every rule, so a subterm is reachable by exponentially many paths -- and a
   structural Rocq [Fixpoint] visits it once per PATH.  Compiling [bpf_O0]
   against itself with the pure [compile_bool] did not finish in ten minutes,
   against 0.01s for the whole query before this change.  The OCaml knot is a
   fixpoint combinator with a physical-identity cache: its specification is "is
   the identity", which is a far smaller thing to audit than the 254 lines of
   semantics it replaced.  See [Z3Solver.compile_core]. *)
Section Step.
Variable rb : SmtBoolExpr -> SmtBoolExpr.
Variable ra : SmtArithExpr -> carith.
Variable rm : SmtArrExpr -> SmtArrExpr.

Definition cstep_bool (e : SmtBoolExpr) : SmtBoolExpr :=
  match e with
  | SmtTrue => SmtTrue
  | SmtFalse => SmtFalse
  | SmtBoolNot e1 => mk_not (rb e1)
  | SmtBoolAnd e1 e2 => mk_and (rb e1) (rb e2)
  | SmtBoolOr e1 e2 => mk_or (rb e1) (rb e2)
  (* [eqb] compares the type first and the bits second, and calls two
     non-integers equal when they are the same non-integer.  Comparing tags
     says both of those at once; the value comparison is then only reached
     when the shared tag is an [IntVal] one. *)
  | SmtBoolEq e1 e2 =>
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      mk_and (mk_beq t1 t2)
        (mk_or (mk_not (mk_int_tag t1)) (mk_beq v1 v2))
  (* [ltb] is false on every non-integer, in both directions. *)
  | SmtBoolLt e1 e2 =>
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      mk_and (mk_beq t1 t2)
        (mk_and (mk_int_tag t1) (mk_blt v1 v2))
  | SmtBoolVar name => SmtBoolVar name
  | SmtArrEq n a1 a2 => SmtArrEq n (rm a1) (rm a2)
  end
.

Definition cstep_arith (e : SmtArithExpr) : carith :=
  match e with
  | SmtArithConst val ty => (cmask ty (cw (unsigned val)), cw (tag_z ty))
  | SmtUninit => (zero_w, cw 1)
  (* BOTH halves are coerced, and the value half is why this needs saying.

     [eval_smt_arith]'s [SmtArithVar] arm turns a valuation's [UninitVal] into
     [ErrorVal], so the tag has to be forced to [tag_err] outside 2..5 -- that
     much mirrors the semantics directly.  The value is forced to zero on the
     same condition for a different reason: [CrVal.val_of] is 0 on a
     non-[IntVal], while the solver's variable is a free 64-bit constant that a
     model may set to anything.  Emitting the coercion into the TERM makes the
     two agree structurally, where the lowering used to make them agree by
     asserting a constraint about the model. *)
  | SmtArithVar name =>
      let ok := mk_int_tag (SmtVarTag name) in
      (mk_ite ok (SmtVarVal name) zero_w,
       mk_ite ok (SmtVarTag name) err_tag)
  | SmtBitsToInt bits =>
      (SmtBitsToInt (List.map rb bits),
       cw (tag_z u64))
  | SmtBitSlice lo hi e1 =>
      let (v1, t1) := ra e1 in
      let ok := mk_int_tag t1 in
      (mk_ite ok (SmtBitSlice lo hi v1) zero_w,
       mk_ite ok (ctag u64) err_tag)
  | SmtConditional c e1 e2 =>
      let cb := rb c in
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      (mk_ite cb v1 v2, mk_ite cb t1 t2)
  | SmtCast from to e1 =>
      let (v1, t1) := ra e1 in
      (cmask to v1,
       mk_ite (tag_is t1 from) (ctag to) err_tag)
  | SmtBitAdd ty e1 e2 => mk_binop ty SmtBitAdd (ra e1) (ra e2)
  | SmtBitSub ty e1 e2 => mk_binop ty SmtBitSub (ra e1) (ra e2)
  | SmtBitAnd ty e1 e2 => mk_binop ty SmtBitAnd (ra e1) (ra e2)
  | SmtBitOr  ty e1 e2 => mk_binop ty SmtBitOr (ra e1) (ra e2)
  | SmtBitXor ty e1 e2 => mk_binop ty SmtBitXor (ra e1) (ra e2)
  | SmtBitMul ty e1 e2 => mk_binop ty SmtBitMul (ra e1) (ra e2)
  | SmtBitDiv ty e1 e2 => mk_binop ty SmtBitDiv (ra e1) (ra e2)
  | SmtBitMod ty e1 e2 => mk_binop ty SmtBitMod (ra e1) (ra e2)
  (* [CrVal.not] masks at the operand's OWN type, which is a runtime value, so
     the width has to be selected by a conditional chain.  This is the case the
     OCaml lowering wrote by hand as a fold over the four widths. *)
  | SmtBitNot e1 =>
      let (v1, t1) := ra e1 in
      let nv := SmtBitNot v1 in
      (mk_ite (tag_is t1 u8) (cmask u8 nv)
        (mk_ite (tag_is t1 u16) (cmask u16 nv)
          (mk_ite (tag_is t1 u32) (cmask u32 nv)
            (mk_ite (tag_is t1 u64) (cmask u64 nv) zero_w))),
       mk_ite (mk_int_tag t1) t1 err_tag)
  (* The bounds guard [ld_arr] applies, made explicit.  [smt_arr_len] is the
     declared length of the region the expression is rooted at; it agrees with
     the denoted [arr_len] exactly when the merges are length-consistent, which
     is what [lc_arr] below checks. *)
  | SmtArrSel a idx =>
      let ca := rm a in
      let (vi, ti) := ra idx in
      let ok := mk_and (mk_int_tag ti)
                  (mk_blt vi (cw (unsigned (smt_arr_len a)))) in
      (mk_ite ok (SmtCellVal ca vi) zero_w,
       mk_ite ok (SmtCellTag ca vi) err_tag)
  (* Already core: a word, hence tag [u64]. *)
  | SmtVarVal name => (SmtVarVal name, ctag u64)
  | SmtVarTag name => (SmtVarTag name, ctag u64)
  (* The cell reads are core in their VALUE but not in their INDEX, and the
     index is why these two carry a guard.  [cell_at] is [ErrorVal] on an
     index that does not denote an integer, so the source term reads NO cell
     there, while the compiled index is a word and would read cell 0 -- a
     different cell's contents, under a [u64] tag either way, so nothing
     downstream catches it.  Nothing the checker builds takes this branch:
     [SmtCellVal]/[SmtCellTag]/[SmtStCell] are this compiler's own output and
     appear in no source query, where the index is always core and the guard
     always true.  The correctness theorem quantifies over every expression,
     so the branch still has to be right. *)
  | SmtCellVal a idx =>
      let ca := rm a in
      let (vi, ti) := ra idx in
      (mk_ite (mk_int_tag ti) (SmtCellVal ca vi) zero_w, ctag u64)
  | SmtCellTag a idx =>
      let ca := rm a in
      let (vi, ti) := ra idx in
      (mk_ite (mk_int_tag ti) (SmtCellTag ca vi) zero_w, ctag u64)
  end
.

Definition cstep_arr (a : SmtArrExpr) : SmtArrExpr :=
  match a with
  | SmtArrInit => SmtArrInit
  | SmtArrVar name len => SmtArrVar name len
  | SmtArrIte c a1 a2 => SmtArrIte (rb c) (rm a1) (rm a2)
  (* An out-of-bounds store is DROPPED by [st_arr] and kept by Z3's total
     [store], so the drop becomes a merge back to the unstored region. *)
  | SmtArrSt a1 idx val =>
      let ca := rm a1 in
      let (vi, ti) := ra idx in
      let (vv, tv) := ra val in
      let ok := mk_and (mk_int_tag ti)
                  (mk_blt vi (cw (unsigned (smt_arr_len a1)))) in
      SmtArrIte ok (SmtStCell ca vi vv tv) ca
  (* The same guard, on all three operands: [st_cell] drops a write whose
     index is not an integer, and reads its value and tag through [val_of],
     which is 0 on a non-integer.  Dead in practice, for the reason given on
     [SmtCellVal] above. *)
  | SmtStCell a1 idx value tag =>
      let ca := rm a1 in
      let (vi, ti) := ra idx in
      SmtArrIte (mk_int_tag ti)
        (SmtStCell ca vi (vguard (ra value)) (vguard (ra tag))) ca
  end.

End Step.

(* The pure knot.  [compile_bool_step] below says the OCaml one computes this. *)
Fixpoint compile_bool (e : SmtBoolExpr) : SmtBoolExpr :=
  cstep_bool compile_bool compile_arith compile_arr e
with compile_arith (e : SmtArithExpr) : carith :=
  cstep_arith compile_bool compile_arith compile_arr e
with compile_arr (a : SmtArrExpr) : SmtArrExpr :=
  cstep_arr compile_bool compile_arith compile_arr a.

(* [compile_*] IS its own one-layer step.  This is what licenses tying the knot
   in OCaml with a cache instead of in Rocq: any fixpoint satisfying these three
   equations is [compile_*], so a memoised knot computes the function the
   correctness theorem is about, and the only thing trusted about the OCaml is
   that its cache returns what it stored. *)
Lemma compile_bool_step : forall e,
  compile_bool e = cstep_bool compile_bool compile_arith compile_arr e.
Proof. destruct e; reflexivity. Qed.

Lemma compile_arith_step : forall e,
  compile_arith e = cstep_arith compile_bool compile_arith compile_arr e.
Proof. destruct e; reflexivity. Qed.

Lemma compile_arr_step : forall a,
  compile_arr a = cstep_arr compile_bool compile_arith compile_arr a.
Proof. destruct a; reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* A free region's cells are BYTES, as a QUERY CONJUNCT.

   The scalar case above could be handled by coercing inside the term, because
   [CrVal.val_of] and [tag_of] are total functions of one value.  A region
   cannot: [eval_smt_mem]'s [SmtArrVar] arm pushes the whole map through
   [CrVal.to_byte], and "map [to_byte] over an unbounded array" is not a term.
   So this is stated instead, over the declared length -- which is all that is
   ever read, and all the solver-side constraint it replaces ever covered.

   It says what [to_byte] does: every cell in [0, len) is a [u8] whose value
   fits in eight bits.  Both halves matter, and neither is hygiene.  Tag: a cell
   that is [ErrorVal], [UninitVal] or a wrong-width [IntVal] makes a whole
   multi-byte [ld_val] into [ErrorVal] -- it casts each cell with [cast u8 _] --
   and [CrVal.ltb] is false on [ErrorVal] in BOTH directions, so [x > 100] and
   [x < 101] both fail and two programs testing opposite ways come back
   [NotEquivalent] on a machine state no machine can be in.  Value: [IntVal]
   carries a raw 64-bit value beside its width, so [IntVal 69206016 u8] is a
   well-formed [CrVal] that [mk_int u8] cannot build, and [cast u8 u64] masks to
   the TARGET width rather than truncating -- so [ld_val]'s byte assembly would
   overlap neighbouring cells and a [u64] load would stop agreeing with eight
   [u8] loads recombined.

   This USED TO BE a side constraint in [Z3Solver.solve], asserted alongside the
   goal rather than being part of it.  That left a real gap:
   [SmtQuery.smt_query_sound_none] concludes about EVERY valuation, while an
   UNSAT of goal-and-side-constraints only rules out the valuations satisfying
   the constraints.  It was sound only because [to_byte] makes the constraint
   vacuous on the Rocq side -- [regions_wf_true] below -- which is exactly the
   coincidence between two definitions in two languages that this file exists to
   remove.  As a conjunct, [solve] asserts precisely the formula the axioms are
   stated about. *)
(* The VALUE half of this constraint used to be here too --
   [SmtBoolLt (SmtCellVal a (cw i)) (cw 256)] -- and it is now discharged by
   the encoding instead of being asserted.  [Z3Solver] gives a cell an
   eight-bit value field, because [CrVal.st_arr] and [CrVal.st_cell] put every
   stored value through [CrVal.to_cell]; no model of that encoding has a cell
   whose value exceeds a byte, so stating it bought nothing and cost a [select]
   term at every index in [0, len).  Dropping it weakens the asserted formula,
   which is the safe direction: a weaker constraint admits MORE models, so a
   query can only become satisfiable, never less so, and a false [Equivalent]
   is what a validator must never produce.

   The tag half stays, and has to: a free region variable's cells carry an
   arbitrary three-bit tag, while [CrVal.to_byte] -- the denotation of a region
   variable on the Rocq side -- makes every one of them a [u8]. *)
Definition cell_is_byte (a : SmtArrExpr) (i : Z) : SmtBoolExpr :=
  SmtBoolEq (SmtCellTag a (cw i)) (cw (tag_z u8)).

Fixpoint conj_upto (f : nat -> SmtBoolExpr) (n : nat) : SmtBoolExpr :=
  match n with
  | O => SmtTrue
  | S k => SmtBoolAnd (f k) (conj_upto f k)
  end.

Definition region_bytes_wf (name : string) (len : uint64) : SmtBoolExpr :=
  conj_upto (fun i => cell_is_byte (SmtArrVar name len) (Z.of_nat i))
            (Z.to_nat (unsigned len)).

Fixpoint regions_wf (rs : list (string * uint64)) : SmtBoolExpr :=
  match rs with
  | nil => SmtTrue
  | (n, l) :: rest => SmtBoolAnd (region_bytes_wf n l) (regions_wf rest)
  end.

(* The query [solve] actually asserts. *)
Definition compile_query (rs : list (string * uint64)) (e : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolAnd (regions_wf rs) (compile_bool e).

(* [regions_wf] is VACUOUS in Rocq: [eval_smt_mem]'s [SmtArrVar] arm already
   pushes every valuation through [CrVal.to_byte], so no valuation can fail it.
   That is exactly what makes conjoining it axiom-preserving --
   [eval_smt_bool (compile_query rs e) v = eval_smt_bool (compile_bool e) v] for
   every [v] -- while for the solver, whose array variables are free, it is the
   constraint that rules out models no [CrVal] can denote.

   Proving it is the point.  As a side constraint this fact was asserted in
   OCaml and relied on in Rocq, with nothing connecting the two. *)
Lemma cw_eval : forall z v, eval_smt_arith (cw z) v = IntVal (repr z) u64.
Proof.
  intros z v. unfold cw.
  cbn [eval_smt_arith eval_smt_bool eval_smt_mem].
  unfold mk_int. cbn [it_width]. f_equal. apply mask_width_W64_id.
Qed.

Lemma arrvar_cell_byte : forall n len i v,
  exists z, cell_at (eval_smt_mem (SmtArrVar n len) v) (eval_smt_arith (cw i) v)
            = IntVal (mask_width W8 z) u8.
Proof.
  intros n len i v.
  cbn [eval_smt_mem]. unfold region_of_bytes, cell_at.
  rewrite cw_eval. cbn [region_bytes arr_bytes].
  rewrite PMap.gmap. unfold to_byte.
  destruct ((region_bytes (sv_arrs v n)) !! (offset_to_key (repr i)))
    as [c |] eqn:E; [| exists 0%Z; reflexivity].
  destruct c as [b [w] | |]; try (exists 0%Z; reflexivity).
  destruct w; try (exists 0%Z; reflexivity).
  exists (unsigned b); reflexivity.
Qed.

Lemma cell_is_byte_true : forall n len i v,
  eval_smt_bool (cell_is_byte (SmtArrVar n len) i) v = true.
Proof.
  intros n len i v.
  destruct (arrvar_cell_byte n len i v) as [z Hz].
  unfold cell_is_byte. cbn [eval_smt_bool eval_smt_arith].
  rewrite Hz, cw_eval.
  unfold tag_z, tag_of, mk_int, u8, u64. cbn [it_width].
  rewrite (mask_width_W64_small 2) by lia.
  cbn [CrVal.eqb crinttype_eqb crwidth_eqb]. rewrite int_eq_refl. reflexivity.
Qed.

Lemma conj_upto_true : forall f n v,
  (forall k, eval_smt_bool (f k) v = true) -> eval_smt_bool (conj_upto f n) v = true.
Proof.
  intros f n v H. induction n as [| k IH]; [reflexivity |].
  cbn [conj_upto eval_smt_bool]. rewrite H, IH. reflexivity.
Qed.

Lemma regions_wf_true : forall rs v, eval_smt_bool (regions_wf rs) v = true.
Proof.
  induction rs as [| [n l] rest IH]; intros v; [reflexivity |].
  cbn [regions_wf eval_smt_bool]. rewrite IH, andb_true_r.
  unfold region_bytes_wf. apply conj_upto_true. intros k. apply cell_is_byte_true.
Qed.


(* ------------------------------------------------------------------ *)
(* Length consistency.

   [smt_arr_len] is a SYNTACTIC walk that reads one branch of a merge and
   discards the other, while [eval_smt_mem] takes whichever branch the
   condition selects.  The two agree exactly when every merge joins regions of
   equal declared length -- which is true of everything the checker builds
   (both branches of a merge are versions of the same region), and is what
   [SmtModuleQuery.eval_general_program_symbolic_arr_len_agrees] establishes.
   Making it a decidable predicate turns that from a prose caveat into a
   hypothesis the correctness proof discharges. *)
Fixpoint lc_arr (a : SmtArrExpr) : bool :=
  match a with
  | SmtArrInit | SmtArrVar _ _ => true
  | SmtArrSt a1 _ _ => lc_arr a1
  | SmtStCell a1 _ _ _ => lc_arr a1
  | SmtArrIte _ a1 a2 =>
      lc_arr a1 && lc_arr a2 && Integers.eq (smt_arr_len a1) (smt_arr_len a2)
  end.

Lemma lc_arr_len : forall a vv,
  lc_arr a = true -> arr_len_of (eval_smt_mem a vv) = smt_arr_len a.
Proof.
  induction a as [ | nm ln | a IH i sv | c a1 IH1 a2 IH2 | a IH i sv st ];
    intros vv H; simpl in *.
  - reflexivity.
  - reflexivity.
  - (* SmtArrSt: a legal store preserves the length, an illegal one is dropped *)
    destruct (CrVal.st_arr (eval_smt_mem a vv) (eval_smt_arith i vv)
                           (eval_smt_arith sv vv)) eqn:E.
    + unfold CrVal.st_arr in E.
      destruct (eval_smt_mem a vv) eqn:Em;
        [| destruct (eval_smt_arith i vv); discriminate].
      destruct (eval_smt_arith i vv); try discriminate.
      destruct (Integers.ltu val (arr_len arr)); [| discriminate].
      inversion E; subst; simpl.
      rewrite <- (IH vv H). rewrite Em. reflexivity.
    + rewrite <- (IH vv H). reflexivity.
  - (* SmtArrIte: the branch taken may be either, so the two must agree *)
    apply andb_prop in H as [H12 Hlen]. apply andb_prop in H12 as [H1 H2].
    destruct (eval_smt_bool c vv).
    + apply IH1; assumption.
    + rewrite (IH2 vv H2). symmetry. apply int_eq_true. exact Hlen.
  - (* SmtStCell: preserves [arr_len_of] whether or not it writes *)
    unfold CrVal.st_cell. rewrite <- (IH vv H).
    destruct (eval_smt_mem a vv); [| reflexivity].
    destruct (eval_smt_arith i vv); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* Well-formedness for the whole expression, not just an array spine.
   [lc_arr] above checks the merges on one region's spine; the correctness
   statement needs that for EVERY array subterm, including the ones buried in a
   store's index or value. *)
(* Split into one-layer steps for the same reason [cstep_*] is: a structural
   walk over a DAG is exponential in its sharing.  This one is a pure predicate
   that builds nothing, and it was still the entire cost of the query -- 52s of
   [lcb] against 0.13s for compiling, lowering and solving put together --
   until [Z3Solver] started tying its knot over a cache too.  The same trap
   memo-memo.txt records for [collect_arr_lens]: a walk that returns nothing
   still has to memoise. *)
Section LcStep.
Variable qb : SmtBoolExpr -> bool.
Variable qa : SmtArithExpr -> bool.
Variable qm : SmtArrExpr -> bool.

Definition lcstep_bool (e : SmtBoolExpr) : bool :=
  match e with
  | SmtTrue | SmtFalse | SmtBoolVar _ => true
  | SmtBoolNot e1 => qb e1
  | SmtBoolAnd e1 e2 | SmtBoolOr e1 e2 => qb e1 && qb e2
  | SmtBoolEq e1 e2 | SmtBoolLt e1 e2 => qa e1 && qa e2
  | SmtArrEq _ a1 a2 => qm a1 && qm a2
  end.

Definition lcstep_arith (e : SmtArithExpr) : bool :=
  match e with
  | SmtArithConst _ _ | SmtUninit | SmtArithVar _
  | SmtVarVal _ | SmtVarTag _ => true
  | SmtBitsToInt bits =>
      (fix go (bs : list SmtBoolExpr) : bool :=
         match bs with nil => true | b :: r => andb (qb b) (go r) end) bits
  | SmtBitSlice _ _ e1 | SmtCast _ _ e1 | SmtBitNot e1 => qa e1
  | SmtConditional c e1 e2 => qb c && qa e1 && qa e2
  | SmtBitAdd _ e1 e2 | SmtBitSub _ e1 e2 | SmtBitAnd _ e1 e2
  | SmtBitOr _ e1 e2 | SmtBitXor _ e1 e2 | SmtBitMul _ e1 e2
  | SmtBitDiv _ e1 e2 | SmtBitMod _ e1 e2 => qa e1 && qa e2
  | SmtArrSel a idx | SmtCellVal a idx | SmtCellTag a idx => qm a && qa idx
  end.

Definition lcstep_arr (a : SmtArrExpr) : bool :=
  match a with
  | SmtArrInit | SmtArrVar _ _ => true
  | SmtArrSt a1 i v => qm a1 && qa i && qa v
  | SmtStCell a1 i v t => qm a1 && qa i && qa v && qa t
  | SmtArrIte c a1 a2 =>
      qb c && qm a1 && qm a2 && Integers.eq (smt_arr_len a1) (smt_arr_len a2)
  end.

End LcStep.

Fixpoint lcb (e : SmtBoolExpr) : bool := lcstep_bool lcb lca lcm e
with lca (e : SmtArithExpr) : bool := lcstep_arith lcb lca lcm e
with lcm (a : SmtArrExpr) : bool := lcstep_arr lcb lca lcm a.

Lemma lcb_step : forall e, lcb e = lcstep_bool lcb lca lcm e.
Proof. destruct e; reflexivity. Qed.
Lemma lca_step : forall e, lca e = lcstep_arith lcb lca lcm e.
Proof. destruct e; reflexivity. Qed.
Lemma lcm_step : forall a, lcm a = lcstep_arr lcb lca lcm a.
Proof. destruct a; reflexivity. Qed.

Lemma lcm_lc_arr : forall a, lcm a = true -> lc_arr a = true.
Proof.
  induction a as [ | | a IH i sv | c a1 IH1 a2 IH2 | a IH i sv st ];
    intros H; simpl in *; try reflexivity.
  - apply andb_prop in H as [H1 _]. apply andb_prop in H1 as [H1 _]. auto.
  - apply andb_prop in H as [H1 Hlen]. apply andb_prop in H1 as [H1 H2].
    apply andb_prop in H1 as [_ H1].
    rewrite IH1, IH2, Hlen by assumption. reflexivity.
  - apply andb_prop in H as [H1 _]. apply andb_prop in H1 as [H1 _].
    apply andb_prop in H1 as [H1 _]. auto.
Qed.

(* ------------------------------------------------------------------ *)
(* Scaffolding for the correctness proof.

   Three small layers, in order: arithmetic facts about [uint64] that the
   [Integers] interface does not state at a fixed width; a calculus for
   [mk_cell], which is the only thing relating a compiled (value, tag) pair to
   the [CrVal] it stands for; and a mutual induction principle over the three
   expression types.  The last is hand-rolled because [SmtBitsToInt] holds a
   LIST of bool expressions and the derived scheme gives no hypothesis about
   its elements. *)

Local Ltac zr := vm_compute; split; congruence.

Lemma modulus64 : @modulus 64%positive = 2 ^ 64.
Proof. vm_compute; reflexivity. Qed.

Lemma unsigned_range64 : forall (a : uint64), 0 <= unsigned a < 2 ^ 64.
Proof. intros a. pose proof (unsigned_range a) as H. rewrite modulus64 in H. exact H. Qed.

Lemma unsigned_repr64 : forall z, 0 <= z < 2 ^ 64 -> unsigned (@repr 64%positive z) = z.
Proof. intros z Hz. apply unsigned_repr. unfold max_unsigned. rewrite modulus64. lia. Qed.

Lemma unsigned_mask_W64 : forall z, 0 <= z < 2 ^ 64 -> unsigned (mask_width W64 z) = z.
Proof. intros z Hz. rewrite mask_width_W64_small by exact Hz. apply unsigned_repr64. exact Hz. Qed.

Lemma ltu64_spec : forall (a b : uint64), Integers.ltu a b = (unsigned a <? unsigned b).
Proof.
  intros a b. unfold Integers.ltu.
  destruct (Rocqlib.zlt (unsigned a) (unsigned b)) as [H | H].
  - symmetry. apply Z.ltb_lt. exact H.
  - symmetry. apply Z.ltb_ge. lia.
Qed.

Lemma eq64_spec : forall (a b : uint64), Integers.eq a b = (unsigned a =? unsigned b).
Proof.
  intros a b. unfold Integers.eq.
  destruct (Rocqlib.zeq (unsigned a) (unsigned b)) as [H | H].
  - symmetry. apply Z.eqb_eq. exact H.
  - symmetry. apply Z.eqb_neq. exact H.
Qed.

(* [cmask] is [Integers.and] with a literal mask, which is [mask_width]. *)
Lemma and_ones_mask : forall (a : uint64) w,
  Integers.and a (repr (Z.ones (width_bits w))) = mask_width w (unsigned a).
Proof.
  intros a w. unfold Integers.and, mask_width. f_equal. f_equal.
  destruct w; apply unsigned_repr64; zr.
Qed.

(* ------------------------------------------------------------------ *)
(* The (value, tag) calculus. *)

Lemma tag_z_range : forall ty, 2 <= tag_z ty <= 5.
Proof. intros [w]; destruct w; cbn; lia. Qed.

Lemma tag_of_range : forall x, 0 <= tag_of x <= 5.
Proof. intros [a [w] | |]; try (cbn; lia). destruct w; cbn; lia. Qed.

Lemma val_of_range : forall x, 0 <= val_of x < 2 ^ 64.
Proof. intros [a ty | |]; cbn; try (split; [lia | vm_compute; reflexivity]). apply unsigned_range64. Qed.

Lemma mk_cell_tag_z : forall (a : uint64) ty, mk_cell (unsigned a) (tag_z ty) = IntVal a ty.
Proof.
  intros a [w]; destruct w; unfold mk_cell, tag_z, u8, u16, u32, u64; cbn [it_width];
    cbn [Z.eqb Pos.eqb]; rewrite repr_unsigned; reflexivity.
Qed.

Lemma mk_cell_int_inv : forall va tg (a : uint64) ty,
  mk_cell va tg = IntVal a ty -> tg = tag_z ty /\ a = repr va.
Proof.
  intros va tg a ty H. unfold mk_cell in H.
  destruct (Z.eqb tg 2) eqn:E2.
  { apply Z.eqb_eq in E2. subst tg. inversion H; subst. split; reflexivity. }
  destruct (Z.eqb tg 3) eqn:E3.
  { apply Z.eqb_eq in E3. subst tg. inversion H; subst. split; reflexivity. }
  destruct (Z.eqb tg 4) eqn:E4.
  { apply Z.eqb_eq in E4. subst tg. inversion H; subst. split; reflexivity. }
  destruct (Z.eqb tg 5) eqn:E5.
  { apply Z.eqb_eq in E5. subst tg. inversion H; subst. split; reflexivity. }
  destruct (Z.eqb tg 1); discriminate.
Qed.

(* A tag outside 2..5 cannot stand for an integer, and one that is not [ty]'s
   cannot stand for a [ty]: the two facts the compiled type tests need. *)
Lemma mk_cell_nonint : forall va tg (a : uint64) ty,
  tg <= 1 -> mk_cell va tg <> IntVal a ty.
Proof.
  intros va tg a ty Hle H. apply mk_cell_int_inv in H as [Ht _].
  pose proof (tag_z_range ty). lia.
Qed.

Lemma mk_cell_ne_ty : forall va tg (a : uint64) ty ty',
  tg <> tag_z ty -> mk_cell va tg = IntVal a ty' -> crinttype_eqb ty' ty = false.
Proof.
  intros va tg a ty ty' Hne H. apply mk_cell_int_inv in H as [Ht _]. subst tg.
  destruct (crinttype_eqb ty' ty) eqn:E; [| reflexivity].
  apply crinttype_eqb_true in E. subst ty'. contradiction.
Qed.

(* ------------------------------------------------------------------ *)
(* What a compiled pair MEANS.

   The relation the induction carries: the two halves both denote plain words,
   the tag half denotes one of the six tags, and [mk_cell] of the two is the
   source term's value.  The tag bound is not decoration -- [mk_cell] sends
   every tag outside 1..5 to [ErrorVal], so without it two DIFFERENT tags could
   stand for the same [CrVal] and the compiled [SmtBoolEq], which compares tags,
   would be wrong. *)
Definition reps (p : carith) (v : SmtValuation) (x : CrVal) : Prop :=
  exists av tv : uint64,
    eval_smt_arith (fst p) v = IntVal av u64
    /\ eval_smt_arith (snd p) v = IntVal tv u64
    /\ unsigned tv <= 5
    /\ x = mk_cell (unsigned av) (unsigned tv).

Lemma small64 : forall z, 0 <= z <= 5 -> 0 <= z < 2 ^ 64.
Proof. intros z Hz. assert (H : 5 < 2 ^ 64) by (vm_compute; reflexivity). lia. Qed.

Lemma eval_zero_w : forall v, eval_smt_arith zero_w v = IntVal (repr 0) u64.
Proof. intro v. apply cw_eval. Qed.

Lemma unsigned_repr_tag : forall ty, unsigned (@repr 64%positive (tag_z ty)) = tag_z ty.
Proof. intro ty. pose proof (tag_z_range ty). apply unsigned_repr64, small64. lia. Qed.

(* The three ways a case establishes [reps]: a masked integer of a known width,
   an arbitrary [CrVal] split by [val_of]/[tag_of], and the two non-integers. *)
Lemma reps_mask : forall V T v ty z,
  eval_smt_arith V v = IntVal (mask_width (it_width ty) z) u64 ->
  eval_smt_arith T v = IntVal (repr (tag_z ty)) u64 ->
  reps (V, T) v (mk_int ty z).
Proof.
  intros V T v ty z HV HT.
  exists (mask_width (it_width ty) z), (repr (tag_z ty)).
  pose proof (tag_z_range ty). rewrite unsigned_repr_tag.
  cbn [fst snd]. repeat split; try assumption; [lia |].
  unfold mk_int. rewrite mk_cell_tag_z. reflexivity.
Qed.

Lemma reps_cell : forall V T v x,
  eval_smt_arith V v = mk_int u64 (val_of x) ->
  eval_smt_arith T v = mk_int u64 (tag_of x) ->
  reps (V, T) v x.
Proof.
  intros V T v x HV HT.
  exists (mask_width W64 (val_of x)), (mask_width W64 (tag_of x)).
  pose proof (val_of_range x). pose proof (tag_of_range x).
  cbn [fst snd]. rewrite HV, HT. unfold mk_int, u64. cbn [it_width].
  rewrite (unsigned_mask_W64 (val_of x)) by assumption.
  rewrite (unsigned_mask_W64 (tag_of x)) by (apply small64; lia).
  repeat split; [lia | symmetry; apply mk_cell_val_tag].
Qed.

Lemma reps_err : forall V T v (av : uint64),
  eval_smt_arith V v = IntVal av u64 ->
  eval_smt_arith T v = IntVal (repr 0) u64 ->
  reps (V, T) v ErrorVal.
Proof.
  intros V T v av HV HT. exists av, (repr 0). cbn [fst snd].
  rewrite (unsigned_repr64 0) by (split; [lia | vm_compute; reflexivity]).
  refine (conj HV (conj HT (conj _ _))); [lia | reflexivity].
Qed.

Lemma reps_uninit : forall V T v (av : uint64),
  eval_smt_arith V v = IntVal av u64 ->
  eval_smt_arith T v = IntVal (repr 1) u64 ->
  reps (V, T) v UninitVal.
Proof.
  intros V T v av HV HT. exists av, (repr 1). cbn [fst snd].
  rewrite (unsigned_repr64 1) by (split; [lia | vm_compute; reflexivity]).
  refine (conj HV (conj HT (conj _ _))); [lia | reflexivity].
Qed.

(* ------------------------------------------------------------------ *)
(* Evaluating the compiled guards. *)

Lemma is_int_tag_val : forall t v,
  eval_smt_bool (is_int_tag t) v = itv (eval_smt_arith t v).
Proof.
  intros t v. unfold is_int_tag, itv, c_two, c_six.
  cbn [eval_smt_bool]. rewrite !cw_eval. reflexivity.
Qed.

Lemma tag_decide_sound : forall fuel t r v,
  tag_decide fuel t = Some r -> eval_smt_bool (is_int_tag t) v = r.
Proof.
  induction fuel as [| fuel IH]; intros t r v Hd; [discriminate |].
  destruct t as [ x ty | | nm | bits | lo hi e | c a1 a2 | fr to e
                | ty e1 e2 | ty e1 e2 | ty e1 e2 | ty e1 e2 | ty e1 e2 | e
                | ty e1 e2 | ty e1 e2 | ty e1 e2
                | ar ix | nm | nm | ar ix | ar ix ];
    cbn [tag_decide] in Hd; try discriminate.
  - (* SmtArithConst: the literal decides outright. *)
    injection Hd as <-. rewrite is_int_tag_val, lit_val_eval. reflexivity.
  - (* SmtConditional: both branches decided within the fuel, and agreed. *)
    destruct (tag_decide fuel a1) as [xa|] eqn:Ha; [| discriminate].
    destruct (tag_decide fuel a2) as [xb|] eqn:Hb; [| discriminate].
    rewrite is_int_tag_val. cbn [eval_smt_arith].
    destruct xa, xb; cbn in Hd; try discriminate; injection Hd as <-;
      destruct (eval_smt_bool c v); rewrite <- is_int_tag_val;
      solve [ apply (IH _ _ v Ha) | apply (IH _ _ v Hb) ].
Qed.

Lemma mk_int_tag_eval : forall t v,
  eval_smt_bool (mk_int_tag t) v = eval_smt_bool (is_int_tag t) v.
Proof.
  intros t v. unfold mk_int_tag. destruct (tag_decide tag_fuel t) as [b|] eqn:Hd;
    [| reflexivity].
  rewrite bool_lit_eval. symmetry. apply (tag_decide_sound tag_fuel t b v Hd).
Qed.

(* Rewrite every fold back to the raw node it stands for.  Each smart
   constructor is extensionally its raw counterpart, so a proof that used to
   [cbn] straight through [SmtBoolAnd] now runs [unfold_mk] first and is
   otherwise unchanged -- the folding is invisible to everything below. *)
Ltac unfold_mk :=
  repeat progress
    (rewrite ?ctag_cw, ?mk_not_eval, ?mk_and_eval, ?mk_or_eval,
             ?mk_beq_eval, ?mk_blt_eval, ?mk_ite_eval, ?mk_int_tag_eval).


Lemma eval_is_int_tag : forall t v (tv : uint64),
  eval_smt_arith t v = IntVal tv u64 ->
  eval_smt_bool (is_int_tag t) v = ((2 <=? unsigned tv) && (unsigned tv <? 6))%bool.
Proof.
  intros t v tv Ht. unfold is_int_tag, c_two, c_six. cbn [eval_smt_bool].
  rewrite Ht, !cw_eval. unfold CrVal.ltb, u64. cbn [crinttype_eqb crwidth_eqb it_width].
  rewrite !andb_true_l, !ltu64_spec.
  rewrite (unsigned_repr64 2) by (split; [lia | vm_compute; reflexivity]).
  rewrite (unsigned_repr64 6) by (split; [lia | vm_compute; reflexivity]).
  f_equal. rewrite Z.ltb_antisym. apply negb_involutive.
Qed.

Lemma eval_is_int_tag_true : forall t v (tv : uint64),
  eval_smt_arith t v = IntVal tv u64 -> 2 <= unsigned tv <= 5 ->
  eval_smt_bool (is_int_tag t) v = true.
Proof.
  intros t v tv Ht Hr. rewrite (eval_is_int_tag t v tv) by assumption.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma eval_is_int_tag_false : forall t v (tv : uint64),
  eval_smt_arith t v = IntVal tv u64 -> unsigned tv <= 1 ->
  eval_smt_bool (is_int_tag t) v = false.
Proof.
  intros t v tv Ht Hr. rewrite (eval_is_int_tag t v tv) by assumption.
  apply andb_false_intro1. apply Z.leb_gt. lia.
Qed.

Lemma eval_tag_is : forall t v (tv : uint64) ty,
  eval_smt_arith t v = IntVal tv u64 ->
  eval_smt_bool (tag_is t ty) v = (unsigned tv =? tag_z ty).
Proof.
  intros t v tv ty Ht. unfold tag_is. rewrite ctag_cw. cbn [eval_smt_bool].
  rewrite Ht, cw_eval. unfold CrVal.eqb, u64. cbn [crinttype_eqb crwidth_eqb it_width].
  rewrite andb_true_l, eq64_spec, unsigned_repr_tag.
  destruct (unsigned tv =? tag_z ty); reflexivity.
Qed.

Lemma eval_cmask : forall ty e v (a : uint64),
  eval_smt_arith e v = IntVal a u64 ->
  eval_smt_arith (cmask ty e) v = IntVal (mask_width (it_width ty) (unsigned a)) u64.
Proof.
  intros [w] e v a He. destruct w; cbn [cmask it_width];
    [ | | | rewrite He; f_equal; symmetry; apply mask_width_W64_id ];
    unfold c_ones8, c_ones16, c_ones32;
    cbn [eval_smt_arith]; rewrite He, cw_eval;
    unfold and_at, iv_binop_at, u64; cbn [crinttype_eqb crwidth_eqb it_width];
    rewrite and_ones_mask; unfold mk_int; cbn [it_width];
    rewrite mask_width_W64_id; reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* A type test that fails makes the whole operation [ErrorVal] -- on either
   operand, and whatever the other one is. *)
Lemma iv_binop_ne1 : forall f ty (x y : CrVal) va tg,
  x = mk_cell va tg -> tg <> tag_z ty -> iv_binop_at f ty x y = ErrorVal.
Proof.
  intros f ty x y va tg Hx Hne.
  destruct x as [a ta | | ]; try (destruct y; reflexivity).
  symmetry in Hx.
  assert (Hc : crinttype_eqb ta ty = false) by (eapply mk_cell_ne_ty; eassumption).
  destruct y as [b tb | |]; cbn [iv_binop_at]; try reflexivity.
  rewrite Hc. reflexivity.
Qed.

Lemma iv_binop_ne2 : forall f ty (x y : CrVal) va tg,
  y = mk_cell va tg -> tg <> tag_z ty -> iv_binop_at f ty x y = ErrorVal.
Proof.
  intros f ty x y va tg Hy Hne.
  destruct y as [b tb | | ]; try (destruct x; reflexivity).
  symmetry in Hy.
  assert (Hc : crinttype_eqb tb ty = false) by (eapply mk_cell_ne_ty; eassumption).
  destruct x as [a ta | |]; cbn [iv_binop_at]; try reflexivity.
  rewrite Hc, andb_false_r. reflexivity.
Qed.

(* [mk_binop] is right whenever both compiled operands are. *)
Lemma reps_binop : forall ty (op : CrIntType -> SmtArithExpr -> SmtArithExpr -> SmtArithExpr)
    (f : uint64 -> uint64 -> uint64) p1 p2 v x y,
  (forall t e1 e2 vv, eval_smt_arith (op t e1 e2) vv
      = iv_binop_at f t (eval_smt_arith e1 vv) (eval_smt_arith e2 vv)) ->
  reps p1 v x -> reps p2 v y ->
  reps (mk_binop ty op p1 p2) v (iv_binop_at f ty x y).
Proof.
  intros ty op f [V1 T1] [V2 T2] v x y Hop H1 H2.
  destruct H1 as [av1 [tv1 [HV1 [HT1 [Hle1 Hx]]]]].
  destruct H2 as [av2 [tv2 [HV2 [HT2 [Hle2 Hy]]]]].
  cbn [fst snd] in *.
  unfold mk_binop.
  assert (Hv : eval_smt_arith (cmask ty (op u64 V1 V2)) v
               = IntVal (mask_width (it_width ty) (unsigned (f av1 av2))) u64).
  { rewrite (eval_cmask ty _ v (mask_width W64 (unsigned (f av1 av2)))).
    - rewrite mask_width_unsigned_mask_W64. reflexivity.
    - rewrite Hop, HV1, HV2. unfold iv_binop_at, u64.
      cbn [crinttype_eqb crwidth_eqb it_width]. unfold mk_int. cbn [it_width]. reflexivity. }
  assert (Hcond : (eval_smt_bool (tag_is T1 ty) v && eval_smt_bool (tag_is T2 ty) v)%bool
                  = ((unsigned tv1 =? tag_z ty) && (unsigned tv2 =? tag_z ty))%bool).
  { rewrite (eval_tag_is T1 v tv1 ty) by assumption.
    rewrite (eval_tag_is T2 v tv2 ty) by assumption. reflexivity. }
  destruct (unsigned tv1 =? tag_z ty) eqn:E1b.
  - assert (E1 : unsigned tv1 = tag_z ty) by (apply Z.eqb_eq; exact E1b).
    destruct (unsigned tv2 =? tag_z ty) eqn:E2b.
    + (* both typed [ty]: the operation runs *)
      assert (E2 : unsigned tv2 = tag_z ty) by (apply Z.eqb_eq; exact E2b).
      cbn [andb] in Hcond.
      assert (Hxi : x = IntVal av1 ty) by (rewrite Hx, E1; apply mk_cell_tag_z).
      assert (Hyi : y = IntVal av2 ty) by (rewrite Hy, E2; apply mk_cell_tag_z).
      rewrite Hxi, Hyi. unfold iv_binop_at. rewrite !crinttype_eqb_refl. cbn [andb].
      apply (reps_mask _ _ _ ty _ Hv).
      unfold_mk. rewrite Hcond. apply cw_eval.
    + assert (E2 : unsigned tv2 <> tag_z ty) by (apply Z.eqb_neq; exact E2b).
      cbn [andb] in Hcond.
      rewrite (iv_binop_ne2 f ty x y (unsigned av2) (unsigned tv2)) by assumption.
      apply (reps_err _ _ _ _ Hv).
      unfold_mk. rewrite Hcond. unfold err_tag. apply cw_eval.
  - assert (E1 : unsigned tv1 <> tag_z ty) by (apply Z.eqb_neq; exact E1b).
    cbn [andb] in Hcond.
    rewrite (iv_binop_ne1 f ty x y (unsigned av1) (unsigned tv1)) by assumption.
    apply (reps_err _ _ _ _ Hv).
    unfold_mk. rewrite Hcond. unfold err_tag. apply cw_eval.
Qed.

(* ------------------------------------------------------------------ *)
(* Mutual induction over the three expression types.

   The derived scheme is not enough: [SmtBitsToInt] holds a LIST of bool
   expressions, and Rocq's generated principle offers no hypothesis about its
   elements.  This one asks for [Forall Pb bits] instead, built by a nested
   fixpoint over the list -- the standard nested-inductive workaround, and the
   only reason this is written by hand rather than by [Scheme]. *)
Section SmtMutInd.
Variable Pb : SmtBoolExpr -> Prop.
Variable Pa : SmtArithExpr -> Prop.
Variable Pm : SmtArrExpr -> Prop.

Hypothesis HTrue   : Pb SmtTrue.
Hypothesis HFalse  : Pb SmtFalse.
Hypothesis HNot    : forall e, Pb e -> Pb (SmtBoolNot e).
Hypothesis HAnd    : forall e1 e2, Pb e1 -> Pb e2 -> Pb (SmtBoolAnd e1 e2).
Hypothesis HOr     : forall e1 e2, Pb e1 -> Pb e2 -> Pb (SmtBoolOr e1 e2).
Hypothesis HEq     : forall e1 e2, Pa e1 -> Pa e2 -> Pb (SmtBoolEq e1 e2).
Hypothesis HLt     : forall e1 e2, Pa e1 -> Pa e2 -> Pb (SmtBoolLt e1 e2).
Hypothesis HBVar   : forall n, Pb (SmtBoolVar n).
Hypothesis HArrEq  : forall n a1 a2, Pm a1 -> Pm a2 -> Pb (SmtArrEq n a1 a2).

Hypothesis HConst  : forall val ty, Pa (SmtArithConst val ty).
Hypothesis HUninit : Pa SmtUninit.
Hypothesis HAVar   : forall n, Pa (SmtArithVar n).
Hypothesis HBits   : forall bits, Forall Pb bits -> Pa (SmtBitsToInt bits).
Hypothesis HSlice  : forall lo hi e, Pa e -> Pa (SmtBitSlice lo hi e).
Hypothesis HCond   : forall c e1 e2, Pb c -> Pa e1 -> Pa e2 -> Pa (SmtConditional c e1 e2).
Hypothesis HCast   : forall fr to e, Pa e -> Pa (SmtCast fr to e).
Hypothesis HAdd    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitAdd ty e1 e2).
Hypothesis HSub    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitSub ty e1 e2).
Hypothesis HAndB   : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitAnd ty e1 e2).
Hypothesis HOrB    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitOr ty e1 e2).
Hypothesis HXor    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitXor ty e1 e2).
Hypothesis HBNot   : forall e, Pa e -> Pa (SmtBitNot e).
Hypothesis HMul    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitMul ty e1 e2).
Hypothesis HDiv    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitDiv ty e1 e2).
Hypothesis HMod    : forall ty e1 e2, Pa e1 -> Pa e2 -> Pa (SmtBitMod ty e1 e2).
Hypothesis HSel    : forall a idx, Pm a -> Pa idx -> Pa (SmtArrSel a idx).
Hypothesis HVarVal : forall n, Pa (SmtVarVal n).
Hypothesis HVarTag : forall n, Pa (SmtVarTag n).
Hypothesis HCellV  : forall a idx, Pm a -> Pa idx -> Pa (SmtCellVal a idx).
Hypothesis HCellT  : forall a idx, Pm a -> Pa idx -> Pa (SmtCellTag a idx).

Hypothesis HArrInit : Pm SmtArrInit.
Hypothesis HArrVar  : forall n l, Pm (SmtArrVar n l).
Hypothesis HArrSt   : forall a i sv, Pm a -> Pa i -> Pa sv -> Pm (SmtArrSt a i sv).
Hypothesis HArrIte  : forall c a1 a2, Pb c -> Pm a1 -> Pm a2 -> Pm (SmtArrIte c a1 a2).
Hypothesis HStCell  : forall a i sv st, Pm a -> Pa i -> Pa sv -> Pa st -> Pm (SmtStCell a i sv st).

Fixpoint smt_bool_mutind (e : SmtBoolExpr) {struct e} : Pb e :=
  match e with
  | SmtTrue => HTrue
  | SmtFalse => HFalse
  | SmtBoolNot e1 => HNot e1 (smt_bool_mutind e1)
  | SmtBoolAnd e1 e2 => HAnd e1 e2 (smt_bool_mutind e1) (smt_bool_mutind e2)
  | SmtBoolOr e1 e2 => HOr e1 e2 (smt_bool_mutind e1) (smt_bool_mutind e2)
  | SmtBoolEq e1 e2 => HEq e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBoolLt e1 e2 => HLt e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBoolVar n => HBVar n
  | SmtArrEq n a1 a2 => HArrEq n a1 a2 (smt_arr_mutind a1) (smt_arr_mutind a2)
  end
with smt_arith_mutind (e : SmtArithExpr) {struct e} : Pa e :=
  match e with
  | SmtArithConst val ty => HConst val ty
  | SmtUninit => HUninit
  | SmtArithVar n => HAVar n
  | SmtBitsToInt bits =>
      HBits bits
        ((fix gol (l : list SmtBoolExpr) : Forall Pb l :=
            match l with
            | nil => Forall_nil Pb
            | b :: r => Forall_cons b (smt_bool_mutind b) (gol r)
            end) bits)
  | SmtBitSlice lo hi e1 => HSlice lo hi e1 (smt_arith_mutind e1)
  | SmtConditional c e1 e2 =>
      HCond c e1 e2 (smt_bool_mutind c) (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtCast fr to e1 => HCast fr to e1 (smt_arith_mutind e1)
  | SmtBitAdd ty e1 e2 => HAdd ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitSub ty e1 e2 => HSub ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitAnd ty e1 e2 => HAndB ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitOr ty e1 e2 => HOrB ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitXor ty e1 e2 => HXor ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitNot e1 => HBNot e1 (smt_arith_mutind e1)
  | SmtBitMul ty e1 e2 => HMul ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitDiv ty e1 e2 => HDiv ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtBitMod ty e1 e2 => HMod ty e1 e2 (smt_arith_mutind e1) (smt_arith_mutind e2)
  | SmtArrSel a idx => HSel a idx (smt_arr_mutind a) (smt_arith_mutind idx)
  | SmtVarVal n => HVarVal n
  | SmtVarTag n => HVarTag n
  | SmtCellVal a idx => HCellV a idx (smt_arr_mutind a) (smt_arith_mutind idx)
  | SmtCellTag a idx => HCellT a idx (smt_arr_mutind a) (smt_arith_mutind idx)
  end
with smt_arr_mutind (a : SmtArrExpr) {struct a} : Pm a :=
  match a with
  | SmtArrInit => HArrInit
  | SmtArrVar n l => HArrVar n l
  | SmtArrSt a1 i sv => HArrSt a1 i sv (smt_arr_mutind a1) (smt_arith_mutind i) (smt_arith_mutind sv)
  | SmtArrIte c a1 a2 => HArrIte c a1 a2 (smt_bool_mutind c) (smt_arr_mutind a1) (smt_arr_mutind a2)
  | SmtStCell a1 i sv st =>
      HStCell a1 i sv st (smt_arr_mutind a1) (smt_arith_mutind i)
        (smt_arith_mutind sv) (smt_arith_mutind st)
  end.

Lemma smt_mutind :
  (forall e, Pb e) /\ (forall e, Pa e) /\ (forall a, Pm a).
Proof. split; [| split]; [exact smt_bool_mutind | exact smt_arith_mutind | exact smt_arr_mutind]. Qed.

End SmtMutInd.

(* ------------------------------------------------------------------ *)
(* Reading a compiled pair back.                                        *)

Lemma if_id : forall b : bool, (if b then true else false) = b.
Proof. destruct b; reflexivity. Qed.

Lemma eqb_same_ty : forall (a b : uint64) ty,
  CrVal.eqb (IntVal a ty) (IntVal b ty) = (unsigned a =? unsigned b).
Proof.
  intros a b ty. unfold CrVal.eqb. rewrite crinttype_eqb_refl, andb_true_l.
  apply eq64_spec.
Qed.

Lemma ltb_same_ty : forall (a b : uint64) ty,
  CrVal.ltb (IntVal a ty) (IntVal b ty) = (unsigned a <? unsigned b).
Proof.
  intros a b ty. unfold CrVal.ltb. rewrite crinttype_eqb_refl, andb_true_l.
  apply ltu64_spec.
Qed.

Lemma eqb_words : forall (a b : uint64),
  CrVal.eqb (IntVal a u64) (IntVal b u64) = (unsigned a =? unsigned b).
Proof. intros a b. apply eqb_same_ty. Qed.

Lemma ltb_words : forall (a b : uint64),
  CrVal.ltb (IntVal a u64) (IntVal b u64) = (unsigned a <? unsigned b).
Proof. intros a b. apply ltb_same_ty. Qed.

Lemma mk_cell_int_ex : forall (av : uint64) tg, 2 <= tg <= 5 ->
  exists ty, tag_z ty = tg /\ mk_cell (unsigned av) tg = IntVal av ty.
Proof.
  intros av tg Hr.
  assert (D : tg = 2 \/ tg = 3 \/ tg = 4 \/ tg = 5) by lia.
  destruct D as [-> | [-> | [-> | ->]]].
  - exists u8.  split; [reflexivity | exact (mk_cell_tag_z av u8)].
  - exists u16. split; [reflexivity | exact (mk_cell_tag_z av u16)].
  - exists u32. split; [reflexivity | exact (mk_cell_tag_z av u32)].
  - exists u64. split; [reflexivity | exact (mk_cell_tag_z av u64)].
Qed.

Lemma mk_cell_low : forall va tg, 0 <= tg <= 1 ->
  mk_cell va tg = UninitVal \/ mk_cell va tg = ErrorVal.
Proof.
  intros va tg Hr. assert (D : tg = 0 \/ tg = 1) by lia.
  destruct D as [-> | ->]; [right | left]; reflexivity.
Qed.

(* The interface every arith case uses: a compiled pair either stands for an
   integer of a definite width, with the guard true, or for a non-integer,
   with the guard false. *)
Lemma reps_dec : forall p v x, reps p v x ->
  (exists (av : uint64) ty,
      eval_smt_arith (fst p) v = IntVal av u64
      /\ eval_smt_arith (snd p) v = IntVal (repr (tag_z ty)) u64
      /\ eval_smt_bool (is_int_tag (snd p)) v = true
      /\ x = IntVal av ty)
  \/ (exists (av tv : uint64),
      eval_smt_arith (fst p) v = IntVal av u64
      /\ eval_smt_arith (snd p) v = IntVal tv u64
      /\ unsigned tv <= 1
      /\ eval_smt_bool (is_int_tag (snd p)) v = false
      /\ (x = UninitVal \/ x = ErrorVal)).
Proof.
  intros p v x [av [tv [HV [HT [Hle Hx]]]]].
  pose proof (unsigned_range64 tv) as Rt.
  destruct (Z_le_gt_dec 2 (unsigned tv)) as [Hge | Hlt].
  - left. destruct (mk_cell_int_ex av (unsigned tv) ltac:(lia)) as [ty [Htz Hmk]].
    exists av, ty. split; [exact HV | split; [| split]].
    + rewrite Htz, repr_unsigned. exact HT.
    + eapply eval_is_int_tag_true; [exact HT | lia].
    + rewrite Hx. exact Hmk.
  - right. exists av, tv. split; [exact HV | split; [exact HT | split; [lia | split]]].
    + eapply eval_is_int_tag_false; [exact HT | lia].
    + destruct (mk_cell_low (unsigned av) (unsigned tv) ltac:(lia)) as [Hm | Hm];
        rewrite Hx, Hm; [left | right]; reflexivity.
Qed.

(* Two tags are equal exactly when the types they stand for are. *)
Lemma tag_z_eqb : forall ty1 ty2, (tag_z ty1 =? tag_z ty2) = crinttype_eqb ty1 ty2.
Proof. intros [w1] [w2]; destruct w1, w2; reflexivity. Qed.

Lemma ltb_ltu : forall (a b : uint64) ty,
  CrVal.ltb (IntVal a ty) (IntVal b ty) = Integers.ltu a b.
Proof. intros a b ty. unfold CrVal.ltb. rewrite crinttype_eqb_refl. apply andb_true_l. Qed.

Lemma val_of_vguard : forall p v x,
  reps p v x -> val_of (eval_smt_arith (vguard p) v) = val_of x.
Proof.
  intros [V T] v x Hr. unfold vguard.
  destruct (reps_dec _ _ _ Hr) as [[av [ty [HV [HT [Hg Hx]]]]] | [av [tv [HV [_ [_ [Hg Hx]]]]]]];
    cbn [fst snd] in *; unfold_mk; rewrite Hg.
  - rewrite HV, Hx. reflexivity.
  - rewrite eval_zero_w. destruct Hx as [-> | ->]; reflexivity.
Qed.

(* [eqb] and [ltb] on two decoded cells, as the compiled comparisons compute
   them.  Brute force over the six tags each side can carry: the tags are what
   the type test is, and there are thirty-six of them. *)
Lemma mk_cell_eqb : forall (av1 tv1 av2 tv2 : uint64),
  unsigned tv1 <= 5 -> unsigned tv2 <= 5 ->
  CrVal.eqb (mk_cell (unsigned av1) (unsigned tv1)) (mk_cell (unsigned av2) (unsigned tv2))
  = ((unsigned tv1 =? unsigned tv2)
     && (negb ((2 <=? unsigned tv1) && (unsigned tv1 <? 6))
         || (unsigned av1 =? unsigned av2)))%bool.
Proof.
  intros av1 tv1 av2 tv2 H1 H2.
  pose proof (unsigned_range64 tv1). pose proof (unsigned_range64 tv2).
  assert (D1 : unsigned tv1 = 0 \/ unsigned tv1 = 1 \/ unsigned tv1 = 2
               \/ unsigned tv1 = 3 \/ unsigned tv1 = 4 \/ unsigned tv1 = 5) by lia.
  assert (D2 : unsigned tv2 = 0 \/ unsigned tv2 = 1 \/ unsigned tv2 = 2
               \/ unsigned tv2 = 3 \/ unsigned tv2 = 4 \/ unsigned tv2 = 5) by lia.
  destruct D1 as [E1 | [E1 | [E1 | [E1 | [E1 | E1]]]]];
  destruct D2 as [E2 | [E2 | [E2 | [E2 | [E2 | E2]]]]];
    rewrite E1, E2; unfold mk_cell; cbn [Z.eqb Pos.eqb];
    try reflexivity;
    rewrite !repr_unsigned, eqb_same_ty;
    destruct (unsigned av1 =? unsigned av2); reflexivity.
Qed.

Lemma mk_cell_ltb : forall (av1 tv1 av2 tv2 : uint64),
  unsigned tv1 <= 5 -> unsigned tv2 <= 5 ->
  CrVal.ltb (mk_cell (unsigned av1) (unsigned tv1)) (mk_cell (unsigned av2) (unsigned tv2))
  = ((unsigned tv1 =? unsigned tv2)
     && ((2 <=? unsigned tv1) && (unsigned tv1 <? 6) && (unsigned av1 <? unsigned av2)))%bool.
Proof.
  intros av1 tv1 av2 tv2 H1 H2.
  pose proof (unsigned_range64 tv1). pose proof (unsigned_range64 tv2).
  assert (D1 : unsigned tv1 = 0 \/ unsigned tv1 = 1 \/ unsigned tv1 = 2
               \/ unsigned tv1 = 3 \/ unsigned tv1 = 4 \/ unsigned tv1 = 5) by lia.
  assert (D2 : unsigned tv2 = 0 \/ unsigned tv2 = 1 \/ unsigned tv2 = 2
               \/ unsigned tv2 = 3 \/ unsigned tv2 = 4 \/ unsigned tv2 = 5) by lia.
  destruct D1 as [E1 | [E1 | [E1 | [E1 | [E1 | E1]]]]];
  destruct D2 as [E2 | [E2 | [E2 | [E2 | [E2 | E2]]]]];
    rewrite E1, E2; unfold mk_cell; cbn [Z.eqb Pos.eqb];
    try reflexivity;
    rewrite !repr_unsigned, ltb_same_ty;
    destruct (unsigned av1 <? unsigned av2); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The correctness statement, one constructor at a time.

   Each case is its own lemma so that the whole thing does not have to be
   replayed to check one of them; [compile_correct] at the bottom is the
   mutual induction with these as its hypotheses. *)

Definition CPb (e : SmtBoolExpr) : Prop :=
  forall v, lcb e = true -> eval_smt_bool (compile_bool e) v = eval_smt_bool e v.
Definition CPa (e : SmtArithExpr) : Prop :=
  forall v, lca e = true -> reps (compile_arith e) v (eval_smt_arith e v).
Definition CPm (a : SmtArrExpr) : Prop :=
  forall v, lcm a = true -> eval_smt_mem (compile_arr a) v = eval_smt_mem a v.

(* ---- booleans ---- *)

Lemma cc_true : CPb SmtTrue.
Proof. intros v _; reflexivity. Qed.

Lemma cc_false : CPb SmtFalse.
Proof. intros v _; reflexivity. Qed.

Lemma cc_bvar : forall n, CPb (SmtBoolVar n).
Proof. intros n v _; reflexivity. Qed.

Lemma cc_not : forall e, CPb e -> CPb (SmtBoolNot e).
Proof.
  unfold CPb in *. intros e IH v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H.
  rewrite compile_bool_step. cbn [cstep_bool]. unfold_mk. cbn [eval_smt_bool].
  rewrite (IH v H). reflexivity.
Qed.

Lemma cc_and : forall e1 e2, CPb e1 -> CPb e2 -> CPb (SmtBoolAnd e1 e2).
Proof.
  unfold CPb in *. intros e1 e2 IH1 IH2 v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_bool_step. cbn [cstep_bool]. unfold_mk. cbn [eval_smt_bool].
  rewrite (IH1 v H1), (IH2 v H2). reflexivity.
Qed.

Lemma cc_or : forall e1 e2, CPb e1 -> CPb e2 -> CPb (SmtBoolOr e1 e2).
Proof.
  unfold CPb in *. intros e1 e2 IH1 IH2 v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_bool_step. cbn [cstep_bool]. unfold_mk. cbn [eval_smt_bool].
  rewrite (IH1 v H1), (IH2 v H2). reflexivity.
Qed.

Lemma cc_arreq : forall n a1 a2, CPm a1 -> CPm a2 -> CPb (SmtArrEq n a1 a2).
Proof.
  unfold CPb, CPm in *. intros n a1 a2 IH1 IH2 v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_bool_step. cbn [cstep_bool]. unfold_mk. cbn [eval_smt_bool].
  rewrite (IH1 v H1), (IH2 v H2). reflexivity.
Qed.

(* [eqb] compares the type first and the bits second; comparing tags says both
   of those at once, and the value comparison is reached only under a shared
   integer tag. *)
Lemma cc_eq : forall e1 e2, CPa e1 -> CPa e2 -> CPb (SmtBoolEq e1 e2).
Proof.
  unfold CPa, CPb in *. intros e1 e2 IH1 IH2 v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H. apply andb_prop in H as [H1 H2].
  specialize (IH1 v H1). specialize (IH2 v H2).
  destruct (compile_arith e1) as [V1 T1] eqn:C1.
  destruct (compile_arith e2) as [V2 T2] eqn:C2.
  destruct IH1 as [av1 [tv1 [HV1 [HT1 [Hle1 Hx1]]]]].
  destruct IH2 as [av2 [tv2 [HV2 [HT2 [Hle2 Hx2]]]]].
  cbn [fst snd] in HV1, HT1, HV2, HT2.
  rewrite compile_bool_step. cbn [cstep_bool]. rewrite C1, C2. unfold_mk.
  rewrite (eval_is_int_tag T1 v tv1 HT1).
  cbn [eval_smt_bool]. rewrite HV1, HV2, HT1, HT2, Hx1, Hx2.
  rewrite !eqb_words, !if_id.
  symmetry. apply mk_cell_eqb; assumption.
Qed.

(* [ltb] is false on every non-integer, in both directions. *)
Lemma cc_lt : forall e1 e2, CPa e1 -> CPa e2 -> CPb (SmtBoolLt e1 e2).
Proof.
  unfold CPa, CPb in *. intros e1 e2 IH1 IH2 v H.
  rewrite lcb_step in H. cbn [lcstep_bool] in H. apply andb_prop in H as [H1 H2].
  specialize (IH1 v H1). specialize (IH2 v H2).
  destruct (compile_arith e1) as [V1 T1] eqn:C1.
  destruct (compile_arith e2) as [V2 T2] eqn:C2.
  destruct IH1 as [av1 [tv1 [HV1 [HT1 [Hle1 Hx1]]]]].
  destruct IH2 as [av2 [tv2 [HV2 [HT2 [Hle2 Hx2]]]]].
  cbn [fst snd] in HV1, HT1, HV2, HT2.
  rewrite compile_bool_step. cbn [cstep_bool]. rewrite C1, C2. unfold_mk.
  rewrite (eval_is_int_tag T1 v tv1 HT1).
  cbn [eval_smt_bool]. rewrite HV1, HV2, HT1, HT2, Hx1, Hx2.
  rewrite eqb_words, ltb_words, !if_id.
  symmetry. apply mk_cell_ltb; assumption.
Qed.

(* ---- regions ---- *)

Lemma cc_arrinit : CPm SmtArrInit.
Proof. intros v _; reflexivity. Qed.

Lemma cc_arrvar : forall n l, CPm (SmtArrVar n l).
Proof. intros n l v _; reflexivity. Qed.

Lemma cc_arrite : forall c a1 a2, CPb c -> CPm a1 -> CPm a2 -> CPm (SmtArrIte c a1 a2).
Proof.
  unfold CPb, CPm in *. intros c a1 a2 IHc IH1 IH2 v H.
  rewrite lcm_step in H. cbn [lcstep_arr] in H.
  apply andb_prop in H as [H' _]. apply andb_prop in H' as [H' H2].
  apply andb_prop in H' as [Hc H1].
  rewrite compile_arr_step. cbn [cstep_arr]. cbn [eval_smt_mem].
  rewrite (IHc v Hc), (IH1 v H1), (IH2 v H2). reflexivity.
Qed.

(* An out-of-bounds store is dropped by [st_arr] and kept by the total
   [SmtStCell], so the drop becomes a merge back to the unstored region. *)
Lemma cc_arrst : forall a i sv, CPm a -> CPa i -> CPa sv -> CPm (SmtArrSt a i sv).
Proof.
  unfold CPa, CPm in *. intros a i sv IHa IHi IHs v H.
  rewrite lcm_step in H. cbn [lcstep_arr] in H.
  apply andb_prop in H as [H' Hs]. apply andb_prop in H' as [Ha Hi].
  assert (Hlen : arr_len_of (eval_smt_mem a v) = smt_arr_len a)
    by (apply lc_arr_len, lcm_lc_arr, Ha).
  specialize (IHa v Ha). specialize (IHi v Hi). specialize (IHs v Hs).
  assert (Hval : mk_cell (val_of (eval_smt_arith (fst (compile_arith sv)) v))
                         (val_of (eval_smt_arith (snd (compile_arith sv)) v))
                 = eval_smt_arith sv v).
  { destruct IHs as [avv [atv [Hvv [Htv [_ Hsv]]]]].
    rewrite Hvv, Htv. cbn [val_of]. symmetry. exact Hsv. }
  rewrite compile_arr_step. cbn [cstep_arr].
  destruct (compile_arith i) as [vi ti] eqn:Ci.
  destruct (compile_arith sv) as [vv tv] eqn:Cv. cbn [fst snd] in Hval.
  cbn [eval_smt_mem]. unfold_mk. cbn [eval_smt_bool eval_smt_arith].
  rewrite IHa, Hval.
  destruct (reps_dec _ _ _ IHi) as [[avi [ty [HVi [_ [Hg Hi']]]]] | [avi [tvi [HVi [_ [_ [Hg Hi']]]]]]];
    cbn [fst snd] in HVi, Hg; rewrite Hg, HVi.
  - (* an integer index: both sides test it against the declared length *)
    rewrite cw_eval, repr_unsigned, ltb_words, andb_true_l, Hi'.
    unfold CrVal.st_arr.
    destruct (eval_smt_mem a v) as [b |] eqn:Ea; cbn [arr_len_of] in Hlen.
    + rewrite <- Hlen, <- ltu64_spec.
      destruct (Integers.ltu avi (arr_len b)); reflexivity.
    + rewrite <- Hlen. rewrite (unsigned_repr64 0) by (split; [lia | vm_compute; reflexivity]).
      pose proof (unsigned_range64 avi).
      replace (unsigned avi <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      reflexivity.
  - (* a non-integer index: the store is dropped *)
    cbn [andb]. unfold CrVal.st_arr.
    destruct Hi' as [-> | ->]; destruct (eval_smt_mem a v); reflexivity.
Qed.

(* The same drop, on the total cell store, and the same guard on its value and
   tag operands: [st_cell] reads both through [val_of]. *)
Lemma cc_stcell : forall a i sv st,
  CPm a -> CPa i -> CPa sv -> CPa st -> CPm (SmtStCell a i sv st).
Proof.
  unfold CPa, CPm in *. intros a i sv st IHa IHi IHs IHt v H.
  rewrite lcm_step in H. cbn [lcstep_arr] in H.
  apply andb_prop in H as [H' Ht]. apply andb_prop in H' as [H' Hs].
  apply andb_prop in H' as [Ha Hi].
  specialize (IHa v Ha). specialize (IHi v Hi).
  specialize (IHs v Hs). specialize (IHt v Ht).
  rewrite compile_arr_step. cbn [cstep_arr].
  destruct (compile_arith i) as [vi ti] eqn:Ci.
  cbn [eval_smt_mem]. unfold_mk.
  rewrite (val_of_vguard _ _ _ IHs), (val_of_vguard _ _ _ IHt), IHa.
  destruct (reps_dec _ _ _ IHi) as [[avi [ty [HVi [_ [Hg Hi']]]]] | [avi [tvi [HVi [_ [_ [Hg Hi']]]]]]];
    cbn [fst snd] in HVi, Hg; rewrite Hg.
  - rewrite HVi, Hi'. unfold CrVal.st_cell. destruct (eval_smt_mem a v); reflexivity.
  - unfold CrVal.st_cell. destruct Hi' as [-> | ->]; destruct (eval_smt_mem a v); reflexivity.
Qed.

(* ---- arithmetic ---- *)

Lemma cc_const : forall val ty, CPa (SmtArithConst val ty).
Proof.
  unfold CPa in *. intros val ty v _.
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  apply reps_mask.
  - rewrite (eval_cmask ty _ v (repr (unsigned val))) by apply cw_eval.
    rewrite repr_unsigned. reflexivity.
  - apply cw_eval.
Qed.

Lemma cc_uninit : CPa SmtUninit.
Proof.
  unfold CPa in *. intros v _.
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  apply (reps_uninit _ _ _ (repr 0)); apply cw_eval.
Qed.

(* [eval_smt_arith] folds a valuation's [UninitVal] into [ErrorVal], and the
   solver's variable is free, so BOTH halves are coerced: the tag outside 2..5
   to [tag_err], and the value -- which [CrVal.val_of] makes 0 on a
   non-integer -- to zero. *)
Lemma cc_avar : forall n, CPa (SmtArithVar n).
Proof.
  unfold CPa in *. intros n v _.
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  destruct (sv_ints v n) as [a ty | | ] eqn:Es.
  - assert (HT : eval_smt_arith (SmtVarTag n) v = IntVal (mask_width W64 (tag_z ty)) u64)
      by (cbn [eval_smt_arith]; rewrite Es; reflexivity).
    assert (HTu : unsigned (mask_width W64 (tag_z ty)) = tag_z ty)
      by (apply unsigned_mask_W64, small64; pose proof (tag_z_range ty); lia).
    assert (Hg : eval_smt_bool (is_int_tag (SmtVarTag n)) v = true)
      by (eapply eval_is_int_tag_true; [exact HT | rewrite HTu; apply tag_z_range]).
    apply reps_cell; unfold_mk; cbn [eval_smt_arith]; rewrite Hg; cbn [eval_smt_arith];
      rewrite Es; reflexivity.
  - assert (HT : eval_smt_arith (SmtVarTag n) v = IntVal (mask_width W64 1) u64)
      by (cbn [eval_smt_arith]; rewrite Es; reflexivity).
    assert (Hg : eval_smt_bool (is_int_tag (SmtVarTag n)) v = false).
    { eapply eval_is_int_tag_false; [exact HT |].
      rewrite unsigned_mask_W64 by (split; [lia | vm_compute; reflexivity]). lia. }
    apply (reps_err _ _ _ (repr 0));
      unfold_mk; cbn [eval_smt_arith]; rewrite Hg; [unfold zero_w | unfold err_tag]; apply cw_eval.
  - assert (HT : eval_smt_arith (SmtVarTag n) v = IntVal (mask_width W64 0) u64)
      by (cbn [eval_smt_arith]; rewrite Es; reflexivity).
    assert (Hg : eval_smt_bool (is_int_tag (SmtVarTag n)) v = false).
    { eapply eval_is_int_tag_false; [exact HT |].
      rewrite unsigned_mask_W64 by (split; [lia | vm_compute; reflexivity]). lia. }
    apply (reps_err _ _ _ (repr 0));
      unfold_mk; cbn [eval_smt_arith]; rewrite Hg; [unfold zero_w | unfold err_tag]; apply cw_eval.
Qed.

Lemma cc_bits : forall bits, Forall CPb bits -> CPa (SmtBitsToInt bits).
Proof.
  unfold CPa, CPb in *. intros bits Hall v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H.
  (* every bit is length-consistent, hence compiled faithfully *)
  assert (Hall2 : Forall (fun b => eval_smt_bool (compile_bool b) v = eval_smt_bool b v) bits).
  { revert H. induction Hall as [| b r Hb Hr IHr]; intros Hl; [constructor |].
    cbn in Hl. apply andb_prop in Hl as [Hb' Hr'].
    constructor; [apply Hb; exact Hb' | apply IHr; exact Hr']. }
  clear H Hall.
  (* the fold reads the bits only through [eval_smt_bool] *)
  assert (Hfold : forall l acc,
    Forall (fun b => eval_smt_bool (compile_bool b) v = eval_smt_bool b v) l ->
    (fix go (bs : list SmtBoolExpr) (acc0 : Z) {struct bs} : Z :=
       match bs with
       | nil => acc0
       | b :: rest => go rest (Z.add (Z.mul 2 acc0) (if eval_smt_bool b v then 1%Z else 0%Z))
       end) (List.map compile_bool l) acc
    = (fix go (bs : list SmtBoolExpr) (acc0 : Z) {struct bs} : Z :=
       match bs with
       | nil => acc0
       | b :: rest => go rest (Z.add (Z.mul 2 acc0) (if eval_smt_bool b v then 1%Z else 0%Z))
       end) l acc).
  { induction l as [| b r IHl]; intros acc Hl; [reflexivity |].
    inversion Hl as [| ? ? Hb Hr]; subst.
    cbn [List.map]. simpl. rewrite Hb. apply IHl. exact Hr. }
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  apply reps_mask.
  - cbn [eval_smt_arith]. rewrite Hfold by exact Hall2. reflexivity.
  - apply cw_eval.
Qed.

Lemma cc_slice : forall lo hi e, CPa e -> CPa (SmtBitSlice lo hi e).
Proof.
  unfold CPa in *. intros lo hi e IH v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. specialize (IH v H).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith e) as [V1 T1] eqn:C1.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IH)
    as [[av [ty [HV [HT [Hg Hx]]]]] | [av [tv [HV [HT [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HV, HT, Hg.
  - rewrite Hx. cbn [slice_val]. apply reps_mask.
    + unfold_mk. cbn [eval_smt_arith]. rewrite Hg, HV. reflexivity.
    + unfold_mk. cbn [eval_smt_arith]. rewrite Hg. apply cw_eval.
  - destruct Hx as [-> | ->]; cbn [slice_val]; apply (reps_err _ _ _ (repr 0));
      unfold_mk; cbn [eval_smt_arith]; rewrite Hg; [unfold zero_w | unfold err_tag
                                        | unfold zero_w | unfold err_tag]; apply cw_eval.
Qed.

Lemma reps_cond : forall c V1 T1 V2 T2 v x1 x2,
  reps (V1, T1) v x1 -> reps (V2, T2) v x2 ->
  reps (SmtConditional c V1 V2, SmtConditional c T1 T2) v
       (if eval_smt_bool c v then x1 else x2).
Proof.
  intros c V1 T1 V2 T2 v x1 x2 H1 H2. unfold reps in *. cbn [fst snd] in *.
  destruct (eval_smt_bool c v) eqn:Ec.
  - destruct H1 as [av [tv [HV [HT [Hle Hx]]]]]. exists av, tv.
    cbn [eval_smt_arith]. rewrite Ec. exact (conj HV (conj HT (conj Hle Hx))).
  - destruct H2 as [av [tv [HV [HT [Hle Hx]]]]]. exists av, tv.
    cbn [eval_smt_arith]. rewrite Ec. exact (conj HV (conj HT (conj Hle Hx))).
Qed.

(* The same, for the folding [mk_ite] the compiler actually emits. *)
Lemma reps_mk_ite : forall c V1 T1 V2 T2 v x1 x2,
  reps (V1, T1) v x1 -> reps (V2, T2) v x2 ->
  reps (mk_ite c V1 V2, mk_ite c T1 T2) v
       (if eval_smt_bool c v then x1 else x2).
Proof.
  intros c V1 T1 V2 T2 v x1 x2 H1 H2. unfold reps in *. cbn [fst snd] in *.
  destruct (eval_smt_bool c v) eqn:Ec.
  - destruct H1 as [av [tv [HV [HT [Hle Hx]]]]]. exists av, tv.
    rewrite !mk_ite_eval, Ec. exact (conj HV (conj HT (conj Hle Hx))).
  - destruct H2 as [av [tv [HV [HT [Hle Hx]]]]]. exists av, tv.
    rewrite !mk_ite_eval, Ec. exact (conj HV (conj HT (conj Hle Hx))).
Qed.

Lemma cc_cond : forall c e1 e2, CPb c -> CPa e1 -> CPa e2 -> CPa (SmtConditional c e1 e2).
Proof.
  unfold CPa, CPb in *. intros c e1 e2 IHc IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H.
  apply andb_prop in H as [H' H2]. apply andb_prop in H' as [Hc H1].
  specialize (IHc v Hc). specialize (IH1 v H1). specialize (IH2 v H2).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith e1) as [V1 T1] eqn:C1.
  destruct (compile_arith e2) as [V2 T2] eqn:C2.
  cbn [eval_smt_arith]. rewrite <- IHc.
  apply reps_mk_ite; assumption.
Qed.

(* The operand must already carry [from]; the result is its bits masked into
   [to].  The value is computed unconditionally -- under a mismatch the tag is
   [tag_err] and [mk_cell] discards it. *)
Lemma cc_cast : forall fr to e, CPa e -> CPa (SmtCast fr to e).
Proof.
  unfold CPa in *. intros fr to e IH v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. specialize (IH v H).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith e) as [V1 T1] eqn:C1.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IH)
    as [[av [ty [HV [HT [Hg Hx]]]]] | [av [tv [HV [HT [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HV, HT, Hg.
  - rewrite Hx. cbn [cast].
    assert (Hti : eval_smt_bool (tag_is T1 fr) v = crinttype_eqb ty fr).
    { rewrite (eval_tag_is T1 v (repr (tag_z ty)) fr HT), unsigned_repr_tag.
      apply tag_z_eqb. }
    destruct (crinttype_eqb ty fr) eqn:Ety.
    + apply reps_mask.
      * rewrite (eval_cmask to _ v av HV). reflexivity.
      * unfold_mk. cbn [eval_smt_arith]. rewrite Hti. apply cw_eval.
    + apply (reps_err _ _ _ (mask_width (it_width to) (unsigned av))).
      * rewrite (eval_cmask to _ v av HV). reflexivity.
      * unfold_mk. cbn [eval_smt_arith]. rewrite Hti. unfold err_tag. apply cw_eval.
  - assert (Hti : eval_smt_bool (tag_is T1 fr) v = false).
    { rewrite (eval_tag_is T1 v tv fr HT). apply Z.eqb_neq.
      pose proof (tag_z_range fr). lia. }
    destruct Hx as [-> | ->]; cbn [cast];
      apply (reps_err _ _ _ (mask_width (it_width to) (unsigned av)));
      solve [ rewrite (eval_cmask to _ v av HV); reflexivity
            | unfold_mk; cbn [eval_smt_arith]; rewrite Hti; unfold err_tag; apply cw_eval ].
Qed.

(* The eight binary operations, all [iv_binop_at] of their own [Integers]
   function, all compiled by [mk_binop]. *)
Lemma cc_add : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitAdd ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold add_at.
  apply (reps_binop ty SmtBitAdd Integers.add);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_sub : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitSub ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold sub_at.
  apply (reps_binop ty SmtBitSub Integers.sub);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_andb : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitAnd ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold and_at.
  apply (reps_binop ty SmtBitAnd Integers.and);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_orb : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitOr ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold or_at.
  apply (reps_binop ty SmtBitOr Integers.or);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_xor : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitXor ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold xor_at.
  apply (reps_binop ty SmtBitXor Integers.xor);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_mul : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitMul ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold mul_at.
  apply (reps_binop ty SmtBitMul Integers.mul);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_div : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitDiv ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold divu_at.
  apply (reps_binop ty SmtBitDiv Integers.divu);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

Lemma cc_mod : forall ty e1 e2, CPa e1 -> CPa e2 -> CPa (SmtBitMod ty e1 e2).
Proof.
  unfold CPa in *. intros ty e1 e2 IH1 IH2 v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [H1 H2].
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith]. unfold modu_at.
  apply (reps_binop ty SmtBitMod Integers.modu);
    [intros; reflexivity | apply IH1; exact H1 | apply IH2; exact H2].
Qed.

(* [CrVal.not] masks at the operand's OWN type, which is a runtime value, so
   the width is selected by a conditional chain. *)
Lemma cc_bnot : forall e, CPa e -> CPa (SmtBitNot e).
Proof.
  unfold CPa in *. intros e IH v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. specialize (IH v H).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith e) as [V1 T1] eqn:C1.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IH)
    as [[av [ty [HV [HT [Hg Hx]]]]] | [av [tv [HV [HT [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HV, HT, Hg.
  - assert (Hnv : eval_smt_arith (SmtBitNot V1) v = IntVal (Integers.not av) u64).
    { cbn [eval_smt_arith]. rewrite HV. unfold CrVal.not, mk_int, u64. cbn [it_width].
      rewrite mask_width_W64_id. reflexivity. }
    assert (Hti : forall tyi, eval_smt_bool (tag_is T1 tyi) v = crinttype_eqb ty tyi).
    { intro tyi. rewrite (eval_tag_is T1 v (repr (tag_z ty)) tyi HT), unsigned_repr_tag.
      apply tag_z_eqb. }
    rewrite Hx. cbn [CrVal.not]. apply reps_mask.
    + unfold_mk. cbn [eval_smt_arith]. rewrite !Hti.
      destruct ty as [w]; destruct w;
        cbn [crinttype_eqb crwidth_eqb it_width u8 u16 u32 u64];
        [ exact (eval_cmask u8 _ v _ Hnv)  | exact (eval_cmask u16 _ v _ Hnv)
        | exact (eval_cmask u32 _ v _ Hnv) | exact (eval_cmask u64 _ v _ Hnv) ].
    + unfold_mk. cbn [eval_smt_arith]. rewrite Hg. exact HT.
  - assert (Hti : forall tyi, eval_smt_bool (tag_is T1 tyi) v = false).
    { intro tyi. rewrite (eval_tag_is T1 v tv tyi HT). apply Z.eqb_neq.
      pose proof (tag_z_range tyi). lia. }
    destruct Hx as [-> | ->]; cbn [CrVal.not]; apply (reps_err _ _ _ (repr 0));
      solve [ unfold_mk; cbn [eval_smt_arith]; rewrite !Hti; unfold zero_w; apply cw_eval
            | unfold_mk; cbn [eval_smt_arith]; rewrite Hg; unfold err_tag; apply cw_eval ].
Qed.

(* The bounds guard [ld_arr] applies, made explicit: Z3's [select] is total
   and [ld_arr] is not. *)
Lemma cc_sel : forall a idx, CPm a -> CPa idx -> CPa (SmtArrSel a idx).
Proof.
  unfold CPa, CPm in *. intros a idx IHa IHi v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [Ha Hi].
  assert (Hlen : arr_len_of (eval_smt_mem a v) = smt_arr_len a)
    by (apply lc_arr_len, lcm_lc_arr, Ha).
  specialize (IHa v Ha). specialize (IHi v Hi).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith idx) as [vi ti] eqn:Ci.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IHi)
    as [[avi [ty [HVi [HTi [Hg Hx]]]]] | [avi [tvi [HVi [HTi [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HVi, HTi, Hg.
  - assert (Hok : (eval_smt_bool (is_int_tag ti) v
                   && eval_smt_bool (SmtBoolLt vi (cw (unsigned (smt_arr_len a)))) v)%bool
                  = Integers.ltu avi (smt_arr_len a)).
    { rewrite Hg, andb_true_l. cbn [eval_smt_bool].
      rewrite HVi, cw_eval, repr_unsigned. apply ltb_ltu. }
    rewrite Hx. unfold CrVal.ld_arr.
    destruct (eval_smt_mem a v) as [b |] eqn:Ea; cbn [arr_len_of] in Hlen.
    + (* in bounds or not, the guard and [ld_arr] test the same thing *)
      rewrite Hlen, <- Hok.
      destruct (eval_smt_bool (is_int_tag ti) v
                && eval_smt_bool (SmtBoolLt vi (cw (unsigned (smt_arr_len a)))) v)%bool
        eqn:Eok.
      * apply reps_cell;
          unfold_mk; cbn [eval_smt_arith]; rewrite Eok, IHa, HVi; rewrite ?Ea;
          cbn [cell_at region_bytes];
          destruct ((arr_bytes b) !! (offset_to_key avi)); reflexivity.
      * apply (reps_err _ _ _ (repr 0));
          unfold_mk; cbn [eval_smt_arith]; rewrite Eok;
          [unfold zero_w | unfold err_tag]; apply cw_eval.
    + assert (Hz : Integers.ltu avi (smt_arr_len a) = false).
      { rewrite <- Hlen, ltu64_spec.
        rewrite (unsigned_repr64 0) by (split; [lia | vm_compute; reflexivity]).
        pose proof (unsigned_range64 avi). apply Z.ltb_ge. lia. }
      rewrite Hz in Hok.
      apply (reps_err _ _ _ (repr 0));
        unfold_mk; cbn [eval_smt_arith]; rewrite Hok;
        [unfold zero_w | unfold err_tag]; apply cw_eval.
  - assert (Hok : (eval_smt_bool (is_int_tag ti) v
                   && eval_smt_bool (SmtBoolLt vi (cw (unsigned (smt_arr_len a)))) v)%bool
                  = false)
      by (rewrite Hg; reflexivity).
    destruct Hx as [-> | ->]; unfold CrVal.ld_arr;
      destruct (eval_smt_mem a v) as [b |] eqn:Ea;
      apply (reps_err _ _ _ (repr 0));
      unfold_mk; cbn [eval_smt_arith]; rewrite Hok;
      solve [ unfold zero_w; apply cw_eval | unfold err_tag; apply cw_eval ].
Qed.

(* Already core: a word, hence tag [u64]. *)
Lemma cc_varval : forall n, CPa (SmtVarVal n).
Proof.
  unfold CPa in *. intros n v _.
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  apply reps_mask; [reflexivity | apply cw_eval].
Qed.

Lemma cc_vartag : forall n, CPa (SmtVarTag n).
Proof.
  unfold CPa in *. intros n v _.
  rewrite compile_arith_step. cbn [cstep_arith]. cbn [eval_smt_arith].
  apply reps_mask; [reflexivity | apply cw_eval].
Qed.

Lemma cc_cellval : forall a idx, CPm a -> CPa idx -> CPa (SmtCellVal a idx).
Proof.
  unfold CPa, CPm in *. intros a idx IHa IHi v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [Ha Hi].
  specialize (IHa v Ha). specialize (IHi v Hi).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith idx) as [vi ti] eqn:Ci.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IHi)
    as [[avi [ty [HVi [HTi [Hg Hx]]]]] | [avi [tvi [HVi [HTi [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HVi, HTi, Hg.
  - rewrite Hx. apply reps_mask.
    + unfold_mk. cbn [eval_smt_arith]. rewrite Hg, IHa, HVi. reflexivity.
    + apply cw_eval.
  - destruct Hx as [-> | ->]; cbn [cell_at val_of]; apply reps_mask;
      solve [ unfold_mk; cbn [eval_smt_arith]; rewrite Hg; unfold zero_w; apply cw_eval
            | apply cw_eval ].
Qed.

Lemma cc_celltag : forall a idx, CPm a -> CPa idx -> CPa (SmtCellTag a idx).
Proof.
  unfold CPa, CPm in *. intros a idx IHa IHi v H.
  rewrite lca_step in H. cbn [lcstep_arith] in H. apply andb_prop in H as [Ha Hi].
  specialize (IHa v Ha). specialize (IHi v Hi).
  rewrite compile_arith_step. cbn [cstep_arith].
  destruct (compile_arith idx) as [vi ti] eqn:Ci.
  cbn [eval_smt_arith].
  destruct (reps_dec _ _ _ IHi)
    as [[avi [ty [HVi [HTi [Hg Hx]]]]] | [avi [tvi [HVi [HTi [Hle [Hg Hx]]]]]]];
    cbn [fst snd] in HVi, HTi, Hg.
  - rewrite Hx. apply reps_mask.
    + unfold_mk. cbn [eval_smt_arith]. rewrite Hg, IHa, HVi. reflexivity.
    + apply cw_eval.
  - destruct Hx as [-> | ->]; cbn [cell_at tag_of]; apply reps_mask;
      solve [ unfold_mk; cbn [eval_smt_arith]; rewrite Hg; unfold zero_w; apply cw_eval
            | apply cw_eval ].
Qed.

(* A core arith term denotes a plain 64-bit word.  This is the invariant that
   makes the fragment lower structurally: at [u64] every rich operation IS its
   bitvector counterpart. *)
Definition is_word (x : CrVal) : Prop := exists z, x = IntVal z u64.

(* ------------------------------------------------------------------ *)
(* Correctness.

   The value and tag halves are related to the source by [mk_cell], NOT by
   componentwise equality -- deliberately.  [mk_cell _ 0] is [ErrorVal]
   whatever the value is, so a case whose tag says "not an integer" is free to
   leave whatever the masked arithmetic produced in the value half.  That is
   what lets [SmtCast] and [mk_binop] compute their value unconditionally
   instead of wrapping it in a guard, which matters: a guard per operand would
   double the size of every compiled arithmetic node.

   The proof is the mutual induction above with the [cc_*] case lemmas as its
   hypotheses.  Two things in it are worth knowing.  The induction carries a
   STRONGER statement than this one ([reps]): the tag half denotes not merely
   a word but one of the six tags, without which two different tags could
   stand for the same [CrVal] and the compiled [SmtBoolEq], which compares
   tags, would be wrong.  And the [SmtCellVal]/[SmtCellTag]/[SmtStCell] cases
   of the compiler acquired a guard on their index to make this true -- see
   the comment there. *)
Theorem compile_correct :
  (forall e v, lcb e = true ->
     eval_smt_bool (compile_bool e) v = eval_smt_bool e v)
  /\ (forall e v, lca e = true ->
       mk_cell (val_of (eval_smt_arith (fst (compile_arith e)) v))
               (val_of (eval_smt_arith (snd (compile_arith e)) v))
       = eval_smt_arith e v
       /\ is_word (eval_smt_arith (fst (compile_arith e)) v)
       /\ is_word (eval_smt_arith (snd (compile_arith e)) v))
  /\ (forall a v, lcm a = true ->
       eval_smt_mem (compile_arr a) v = eval_smt_mem a v).
Proof.
  destruct (smt_mutind CPb CPa CPm
    cc_true cc_false cc_not cc_and cc_or cc_eq cc_lt cc_bvar cc_arreq
    cc_const cc_uninit cc_avar cc_bits cc_slice cc_cond cc_cast
    cc_add cc_sub cc_andb cc_orb cc_xor cc_bnot cc_mul cc_div cc_mod
    cc_sel cc_varval cc_vartag cc_cellval cc_celltag
    cc_arrinit cc_arrvar cc_arrst cc_arrite cc_stcell) as [Hb [Ha Hm]].
  split; [exact Hb | split; [| exact Hm]].
  intros e v Hlc. destruct (Ha e v Hlc) as [av [tv [HV [HT [_ Hx]]]]].
  rewrite HV, HT. cbn [val_of].
  split; [symmetry; exact Hx |].
  split; [exists av | exists tv]; reflexivity.
Qed.

Corollary compile_bool_correct : forall e v,
  lcb e = true -> eval_smt_bool (compile_bool e) v = eval_smt_bool e v.
Proof. apply compile_correct. Qed.

(* So the conjunct changes nothing about what the query MEANS. *)
Theorem compile_query_correct : forall rs e v,
  lcb e = true -> eval_smt_bool (compile_query rs e) v = eval_smt_bool e v.
Proof.
  intros rs e v H. unfold compile_query. cbn [eval_smt_bool].
  rewrite regions_wf_true. cbn [andb]. apply compile_bool_correct. exact H.
Qed.
