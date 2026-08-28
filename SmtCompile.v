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

(* Mask a word into [ty]'s width.  [W64] is the identity rather than an
   [and] with all-ones so the compiled term does not grow for the common case. *)
Definition cmask (ty : CrIntType) (e : SmtArithExpr) : SmtArithExpr :=
  match it_width ty with
  | W64 => e
  | w => SmtBitAnd u64 e (cw (Z.ones (width_bits w)))
  end.

(* [2 <= t <= 5]: the tag says [IntVal].  Written with [<] alone because that
   is the one comparison the fragment has. *)
Definition is_int_tag (t : SmtArithExpr) : SmtBoolExpr :=
  SmtBoolAnd (SmtBoolNot (SmtBoolLt t (cw 2))) (SmtBoolLt t (cw 6)).

Definition tag_is (t : SmtArithExpr) (ty : CrIntType) : SmtBoolExpr :=
  SmtBoolEq t (cw (tag_z ty)).

Definition err_tag : SmtArithExpr := cw 0.
Definition zero_w : SmtArithExpr := cw 0.

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
   SmtConditional (SmtBoolAnd (tag_is t1 ty) (tag_is t2 ty))
     (cw (tag_z ty)) err_tag).

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
  | SmtBoolNot e1 => SmtBoolNot (rb e1)
  | SmtBoolAnd e1 e2 => SmtBoolAnd (rb e1) (rb e2)
  | SmtBoolOr e1 e2 => SmtBoolOr (rb e1) (rb e2)
  (* [eqb] compares the type first and the bits second, and calls two
     non-integers equal when they are the same non-integer.  Comparing tags
     says both of those at once; the value comparison is then only reached
     when the shared tag is an [IntVal] one. *)
  | SmtBoolEq e1 e2 =>
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      SmtBoolAnd (SmtBoolEq t1 t2)
        (SmtBoolOr (SmtBoolNot (is_int_tag t1)) (SmtBoolEq v1 v2))
  (* [ltb] is false on every non-integer, in both directions. *)
  | SmtBoolLt e1 e2 =>
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      SmtBoolAnd (SmtBoolEq t1 t2)
        (SmtBoolAnd (is_int_tag t1) (SmtBoolLt v1 v2))
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
      let ok := is_int_tag (SmtVarTag name) in
      (SmtConditional ok (SmtVarVal name) zero_w,
       SmtConditional ok (SmtVarTag name) err_tag)
  | SmtBitsToInt bits =>
      (SmtBitsToInt (List.map rb bits),
       cw (tag_z u64))
  | SmtBitSlice lo hi e1 =>
      let (v1, t1) := ra e1 in
      (SmtConditional (is_int_tag t1) (SmtBitSlice lo hi v1) zero_w,
       SmtConditional (is_int_tag t1) (cw (tag_z u64)) err_tag)
  | SmtConditional c e1 e2 =>
      let cb := rb c in
      let (v1, t1) := ra e1 in
      let (v2, t2) := ra e2 in
      (SmtConditional cb v1 v2, SmtConditional cb t1 t2)
  | SmtCast from to e1 =>
      let (v1, t1) := ra e1 in
      (cmask to v1,
       SmtConditional (tag_is t1 from) (cw (tag_z to)) err_tag)
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
      (SmtConditional (tag_is t1 u8) (cmask u8 nv)
        (SmtConditional (tag_is t1 u16) (cmask u16 nv)
          (SmtConditional (tag_is t1 u32) (cmask u32 nv)
            (SmtConditional (tag_is t1 u64) (cmask u64 nv) zero_w))),
       SmtConditional (is_int_tag t1) t1 err_tag)
  (* The bounds guard [ld_arr] applies, made explicit.  [smt_arr_len] is the
     declared length of the region the expression is rooted at; it agrees with
     the denoted [arr_len] exactly when the merges are length-consistent, which
     is what [lc_arr] below checks. *)
  | SmtArrSel a idx =>
      let ca := rm a in
      let (vi, ti) := ra idx in
      let ok := SmtBoolAnd (is_int_tag ti)
                  (SmtBoolLt vi (cw (unsigned (smt_arr_len a)))) in
      (SmtConditional ok (SmtCellVal ca vi) zero_w,
       SmtConditional ok (SmtCellTag ca vi) err_tag)
  (* Already core: a word, hence tag [u64]. *)
  | SmtVarVal name => (SmtVarVal name, cw (tag_z u64))
  | SmtVarTag name => (SmtVarTag name, cw (tag_z u64))
  | SmtCellVal a idx =>
      let (vi, _) := ra idx in
      (SmtCellVal (rm a) vi, cw (tag_z u64))
  | SmtCellTag a idx =>
      let (vi, _) := ra idx in
      (SmtCellTag (rm a) vi, cw (tag_z u64))
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
      let ok := SmtBoolAnd (is_int_tag ti)
                  (SmtBoolLt vi (cw (unsigned (smt_arr_len a1)))) in
      SmtArrIte ok (SmtStCell ca vi vv tv) ca
  | SmtStCell a1 idx val tag =>
      let (vi, _) := ra idx in
      let (vv, _) := ra val in
      let (vt, _) := ra tag in
      SmtStCell (rm a1) vi vv vt
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
Definition cell_is_byte (a : SmtArrExpr) (i : Z) : SmtBoolExpr :=
  SmtBoolAnd
    (SmtBoolEq (SmtCellTag a (cw i)) (cw (tag_z u8)))
    (SmtBoolLt (SmtCellVal a (cw i)) (cw 256)).

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
  unfold cell_is_byte. cbn [eval_smt_bool]. apply andb_true_intro. split.
  - cbn [eval_smt_arith]. rewrite Hz, cw_eval.
    unfold tag_z, tag_of, mk_int, u8, u64. cbn [it_width].
    rewrite (mask_width_W64_small 2) by lia.
    cbn [CrVal.eqb crinttype_eqb crwidth_eqb]. rewrite int_eq_refl. reflexivity.
  - cbn [eval_smt_arith]. rewrite Hz, cw_eval. cbn [val_of].
    unfold mk_int. cbn [it_width]. rewrite mask_width_W64_id.
    cbn [CrVal.ltb crinttype_eqb crwidth_eqb]. cbn [andb].
    unfold Integers.ltu.
    assert (H256 : unsigned (repr 256 : uint64) = 256).
    { rewrite unsigned_repr_eq.
      assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
      rewrite Hmod. apply Zmod_small. lia. }
    rewrite H256. rewrite Coqlib.zlt_true by apply mask_W8_lt_256. reflexivity.
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

   STATUS: ADMITTED.  The statement is what the extracted lowering is trusted
   against, and it is not yet discharged.  Each arith case needs its own
   [Integers] lemma relating [mask_width] to [Z.land ... (Z.ones _)] and the
   [iv_binop_at] type test to the tag comparison; the [SmtBitNot] and
   [SmtArrSel] cases additionally need the conditional chain flattened.  Until
   these close, this file MOVES the trust rather than discharging it: out of
   254 lines of untyped OCaml and into one Rocq statement that can be read,
   tested by computation, and eventually proved.  Do not describe the lowering
   as verified while this says [Admitted]. *)
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
Admitted.

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
