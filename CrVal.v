From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From MyProject Require Import Maps.
From MyProject Require Import Rocqlib.

Inductive Check_T (T : Type) :=
| Legal (v : T)
| Illegal.
Arguments Legal {T} _.
Arguments Illegal {T}.

(* The width an operation acts at, analogous to the b/w/l/q suffix on x86 mov. *)
Inductive CrWidth : Type :=
| W8 | W16 | W32 | W64.

(* The integer "type" carried by a value and required by an operation.  Today
   this is just a width; it is the extension point for signedness (add
   [it_signed : bool] here). *)
Record CrIntType : Type := mkCrIntType {
  it_width : CrWidth;
}.

Definition u8  : CrIntType := mkCrIntType W8.
Definition u16 : CrIntType := mkCrIntType W16.
Definition u32 : CrIntType := mkCrIntType W32.
Definition u64 : CrIntType := mkCrIntType W64.

Definition width_bits (w : CrWidth) : Z :=
  match w with W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64 end.

Definition crwidth_eqb (a b : CrWidth) : bool :=
  match a, b with W8,W8 | W16,W16 | W32,W32 | W64,W64 => true | _,_ => false end.
Definition crinttype_eqb (a b : CrIntType) : bool := crwidth_eqb (it_width a) (it_width b).

(* A value is uniform 64-bit storage [val] tagged with its integer type [ity].
   Operations require their operands to already carry the matching type and
   produce ErrorVal otherwise; the uninitialized / nil integer is [UninitVal].

   There is deliberately no pointer constructor.  Memory is addressed by a
   statically named [CrIdentifiers.MemRegion] plus a runtime offset, so a
   pointer never needs to be a first-class value; see the memory section
   below and [CrTransformer.LoadOp]. *)
Inductive CrVal : Type :=
| IntVal (val : uint64) (ity : CrIntType)
| UninitVal
| ErrorVal.

(* ------------------------------------------------------------------ *)
(* Memory.  A single region is a bounded byte array: [arr_len] is the
   declared length and [arr_bytes] maps an offset to its contents.  The
   *outer* index (which region) is a [MemRegion] and lives in the program
   state ([CrGeneralProgramState.sh_mem]), not here -- this file only knows
   about one region at a time. *)
Inductive MemVal (T : Type) :=
| Init (v : T)
| Uninit.
Arguments Init {T} _.
Arguments Uninit {T}.
Record MemBlock (T : Type) := {
  arr_len : uint64;
  arr_bytes : PMap.t (MemVal T);
}.
Arguments arr_len {T} _.
Arguments arr_bytes {T} _.
Inductive Array {T : Type} :=
| Allocated (arr : MemBlock T)
| Unallocated.
Arguments Unallocated {T}.

(* Offsets index the inner map; requires S to prevent collision @ 0 *)
Definition offset_to_key {w} (p : @bit_int w) : positive :=
  Pos.of_nat (S (Z.to_nat (unsigned p))).

(* A freshly declared region of [len] bytes, all uninitialized.  This replaces
   the old [alloc]: regions are declared statically on the program and exist
   for its whole run, so there is no runtime allocation to model. *)
Definition mk_region {T : Type} (len : uint64) : @Array T :=
  Allocated {| arr_len := len; arr_bytes := PMap.init Uninit |}.

Definition region_bytes {T : Type} (a : @Array T) : PMap.t (MemVal T) :=
  match a with
  | Allocated b => arr_bytes b
  | Unallocated => PMap.init Uninit
  end.

(* Re-bound a region to its declared length.  A region's contents can come from
   a solver model, which knows nothing about the declaration; the length is
   always the declared one. *)
Definition region_with_len {T : Type} (len : uint64) (a : @Array T) : @Array T :=
  Allocated {| arr_len := len; arr_bytes := region_bytes a |}.

(* Mask a raw integer into the low [width_bits w] bits of the 64-bit container. *)
Definition mask_width (w : CrWidth) (z : Z) : uint64 :=
  repr (Z.land z (Z.ones (width_bits w))).

(* Build a typed integer value, masking its bits to the type's width. *)
Definition mk_int (ty : CrIntType) (z : Z) : CrVal :=
  IntVal (mask_width (it_width ty) z) ty.

(* ------------------------------------------------------------------ *)
(* A region cell is a BYTE.

   [ld_val] reads a cell with [cast u8 _], which checks the source type, so a
   cell that is [UninitVal], [ErrorVal], or an [IntVal] of any width other
   than [u8] makes the whole multi-byte load [ErrorVal].  [st_val] only ever
   writes [u8]s ([byte_of_val] ends in [cast u64 u8]), so [u8] is the only
   width a load can hope to see.

   That matters for what a region's contents on ENTRY are allowed to be.  They
   are an input -- a solver model supplies them -- and a model that hands back
   a non-byte cell describes a machine state that does not exist, while making
   every comparison against the loaded value false in BOTH directions
   ([CrVal.ltb] is false on [ErrorVal] either way round).  Two programs that
   test [x > 100] and [x < 101] then disagree on an input no machine produces.
   [to_byte] is what rules those models out: it is applied to a region
   variable's denotation, so a free region denotes an array of bytes and
   nothing else.

   The VALUE is masked as well as the tag checked, and that is not tidiness.
   [IntVal] pairs a raw [uint64] with a width, so [IntVal 69206016 u8] is a
   well-formed [CrVal] that [mk_int u8] can never build -- a "byte" holding
   more than a byte.  [cast u8 u64] does not truncate (it masks to the TARGET
   width), so [ld_val]'s assembly
   [or (cast u8 u64 cell_i * 2^(8i))] would overlap neighbouring cells and stop
   being a byte decomposition at all: a [u64] load and eight [u8] loads
   recombined would disagree, which is exactly the pair an -O0/-O2 comparison
   puts side by side.  [st_val] already writes masked bytes
   ([byte_of_val] ends in [slice_val] then [cast u64 u8]), so this only brings
   the free variable into line with what a store produces.

   Note where this does NOT apply.  A cell can still become [ErrorVal] during
   a run -- [byte_of_val] sends every non-[IntVal] there, so storing an
   unwritten header fills its cells with it -- and that is real behaviour, not
   an artefact.  Only the initial contents are constrained. *)
Definition to_byte (c : MemVal CrVal) : MemVal CrVal :=
  match c with
  | Init (IntVal b {| it_width := W8 |}) => Init (mk_int u8 (unsigned b))
  | _ => Init (mk_int u8 0)
  end.

(* A region variable's denotation: the declared length, and byte contents. *)
Definition region_of_bytes (len : uint64) (a : @Array CrVal) : @Array CrVal :=
  Allocated {| arr_len := len; arr_bytes := PMap.map to_byte (region_bytes a) |}.

(* A freshly declared region as a real machine would present it: [len] bytes,
   zero.  The counterpart of [to_byte] on the concrete side -- [mk_region]
   leaves every cell [Uninit], which loads as [ErrorVal] and so is not a state
   [concrete_gp_state_is_valid] admits. *)
Definition mk_region_zero (len : uint64) : @Array CrVal :=
  Allocated {| arr_len := len; arr_bytes := PMap.init (Init (mk_int u8 0)) |}.

(* Extract bits [lo, hi) of [v]'s value, LSB-indexed (bit 0 is least
   significant, so this is P4's [field[hi-1 : lo]]), returned right-aligned in a
   fresh [u64].  A non-integer operand yields ErrorVal. *)
Definition slice_val (lo hi : nat) (v : CrVal) : CrVal :=
  match v with
  | IntVal a _ =>
      mk_int u64 (Z.land (Z.shiftr (unsigned a) (Z.of_nat lo))
                         (Z.ones (Z.of_nat (hi - lo))))
  | _ => ErrorVal
  end.

(* Equality and unsigned-less-than require the operands to share a type. *)
Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | IntVal a ta, IntVal b tb => crinttype_eqb ta tb && Integers.eq a b
  | UninitVal, UninitVal
  | ErrorVal, ErrorVal => true
  | _, _ => false
  end.

Definition ltb (x y : CrVal) : bool :=
  match x, y with
  | IntVal a ta, IntVal b tb => crinttype_eqb ta tb && Integers.ltu a b
  | _, _ => false
  end.

(* Apply [f] at type [ty]: both operands must already be typed [ty]; the result
   is computed at 64 bits, masked into [ty]'s width and typed [ty].  A type
   mismatch (or a non-integer operand) yields ErrorVal. *)
Definition iv_binop_at (f : uint64 -> uint64 -> uint64) (ty : CrIntType) (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal a ta, IntVal b tb =>
      if crinttype_eqb ta ty && crinttype_eqb tb ty
      then mk_int ty (unsigned (f a b))
      else ErrorVal
  | _, _ => ErrorVal
  end.

Definition add_at  (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.add ty.
Definition sub_at  (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.sub ty.
Definition and_at  (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.and ty.
Definition or_at   (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.or ty.
Definition xor_at  (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.xor ty.
Definition mul_at  (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.mul ty.
Definition divu_at (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.divu ty.
Definition modu_at (ty : CrIntType) : CrVal -> CrVal -> CrVal := iv_binop_at Integers.modu ty.

(* Bitwise complement at the value's own type (no separate op-type to check). *)
Definition not (x : CrVal) : CrVal :=
  match x with
  | IntVal a ta => mk_int ta (unsigned (Integers.not a))
  | _ => ErrorVal
  end.

(* Cast: the operand must be typed [from]; the result is its bits masked into
   [to] and typed [to]. *)
Definition cast (from to : CrIntType) (x : CrVal) : CrVal :=
  match x with
  | IntVal a ta => if crinttype_eqb ta from then mk_int to (unsigned a) else ErrorVal
  | _ => ErrorVal
  end.

(* Read offset [i] of region [a].  [Illegal] on an out-of-bounds offset, a
   non-integer offset, or an undeclared region; the callers in
   [CrConcreteSemanticsTransformer] / [SmtExpr] turn that into [ErrorVal]
   rather than into a rejection -- see the totality argument on
   [CrTransformer.LoadOp]. *)
Definition ld_arr (a : Array) (i : CrVal) : Check_T CrVal :=
  match a, i with
  | Allocated array, IntVal idx _ =>
    if (Integers.ltu idx (arr_len array)) then
      match (arr_bytes array) !! (offset_to_key idx) with
      | Init v => Legal v
      | Uninit => Legal UninitVal
      end
    else
      Illegal
  | _, _ => Illegal
  end.

Definition st_arr (a : Array) (i : CrVal) (v : CrVal) : Check_T Array :=
  match a, i with
  | Allocated array, IntVal idx _ =>
    if (Integers.ltu idx (arr_len array)) then
      Legal (Allocated {|
        arr_len := arr_len array;
        arr_bytes := PMap.set (offset_to_key idx) (Init v) (arr_bytes array);
      |})
    else
      Illegal
  | _, _ => Illegal
  end.

(* ------------------------------------------------------------------ *)
(* Multi-byte access.

   A region is an array of BYTES: every cell holds a [u8] (or [UninitVal] if it
   was never written), and a width-[ty] access covers [it_bytes ty] consecutive
   cells, little-endian -- the order eBPF uses.  [ld_arr]/[st_arr] above stay
   single-cell primitives; the decomposition lives here and is what
   [CrTransformer.LoadOp]/[StoreOp] are defined in terms of.

   A width-w store must therefore be indistinguishable from the w/8 byte
   stores an optimiser coalesces it from; [TestEquality]'s "a u16 store is the
   two u8 stores it coalesces from" is the regression test. *)

Definition it_bytes (ty : CrIntType) : nat :=
  match it_width ty with W8 => 1 | W16 => 2 | W32 => 4 | W64 => 8 end.

(* A cell read, with the partiality already collapsed the way every caller
   wants it: out of bounds, undeclared, or a non-integer offset all read
   [ErrorVal], exactly as [SmtExpr.eval_smt_arith] does for [SmtArrSel]. *)
Definition ld_cell (a : Array) (i : CrVal) : CrVal :=
  match ld_arr a i with Legal v => v | Illegal => ErrorVal end.

(* Byte [i] of [base]: the address of the i'th cell of the access. *)
Definition byte_addr (base : CrVal) (i : nat) : CrVal :=
  add_at u64 base (mk_int u64 (Z.of_nat i)).

(* Byte [i] of a value being stored, as a [u8] cell.  [slice_val] yields
   ErrorVal on a non-integer, so storing a poisoned value poisons every cell it
   covers -- which is what the symbolic side does too. *)
Definition byte_of_val (v : CrVal) (i : nat) : CrVal :=
  cast u64 u8 (slice_val (8 * i) (8 * i + 8) v).

(* Contribution of cell [i] to an assembled value: widen the byte and shift it
   into place.  A bad cell (out of bounds, never written, not a u8) is
   ErrorVal, and [or_at]/[mul_at] propagate that to the whole result. *)
Definition byte_into_val (b : CrVal) (i : nat) : CrVal :=
  mul_at u64 (cast u8 u64 b) (mk_int u64 (2 ^ (8 * Z.of_nat i))).

(* Read a width-[ty] value at [base], little-endian. *)
Definition ld_val (ty : CrIntType) (a : Array) (base : CrVal) : CrVal :=
  cast u64 ty
    (List.fold_left
      (fun acc i => or_at u64 acc (byte_into_val (ld_cell a (byte_addr base i)) i))
      (List.seq 0 (it_bytes ty)) (mk_int u64 0)).

(* Write a width-[ty] value at [base], little-endian.  A byte that falls
   outside the region is dropped and the rest are still written; the store is
   NOT atomic.  That is what the symbolic side gives -- [SmtArrSt] is guarded
   per cell and there is no way to express "all of these are in bounds" as an
   [SmtBoolExpr] -- and the two have to agree. *)
Definition st_val (ty : CrIntType) (a : Array) (base v : CrVal) : Array :=
  List.fold_left
    (fun acc i =>
      match st_arr acc (byte_addr base i) (byte_of_val v i) with
      | Legal a' => a'
      | Illegal => acc
      end)
    (List.seq 0 (it_bytes ty)) a.

(* ------------------------------------------------------------------ *)
(* The (value, tag) view of a [CrVal].

   A solver has no [CrVal]; it has bitvectors.  The encoding every lowering has
   ever used is a 64-bit value beside a small tag, and these are that encoding
   written down ONCE, in Rocq, so that [SmtCompile] can target it and the
   extracted lowering can stay a structural transliteration.  It used to live
   only in [Z3Solver.ml], where nothing checked it against the semantics below
   -- and where getting it wrong made [smt_query_sound_some] false for the real
   solver rather than merely imprecise.

   Tag 0 is [ErrorVal] and 1 is [UninitVal]; 2..5 are the [IntVal] widths in
   [CrWidth] order.  [val_of] is 0 on a non-[IntVal], which is not a free
   choice: it is what makes the encoding INJECTIVE, so a model can be decoded
   back to a [CrVal] without losing anything.  The solver side has to pin the
   same thing (a non-int tag forces a zero value), or the round trip drops
   information and the two disagree on a term no guard happens to discard. *)
Definition tag_of (v : CrVal) : Z :=
  match v with
  | ErrorVal => 0
  | UninitVal => 1
  | IntVal _ ty => match it_width ty with W8 => 2 | W16 => 3 | W32 => 4 | W64 => 5 end
  end.

Definition val_of (v : CrVal) : Z :=
  match v with IntVal a _ => unsigned a | _ => 0 end.

(* The inverse.  Tags outside 0..5 decode to [ErrorVal]; the solver side pins
   the tag into range so that case does not arise, and decoding it to the tag-0
   value keeps [mk_cell] total without inventing a [CrVal]. *)
Definition mk_cell (value tag : Z) : CrVal :=
  if Z.eqb tag 2 then IntVal (repr value) u8
  else if Z.eqb tag 3 then IntVal (repr value) u16
  else if Z.eqb tag 4 then IntVal (repr value) u32
  else if Z.eqb tag 5 then IntVal (repr value) u64
  else if Z.eqb tag 1 then UninitVal
  else ErrorVal.

Lemma mk_cell_val_tag : forall v, mk_cell (val_of v) (tag_of v) = v.
Proof.
  intros [a [w]| |]; try reflexivity.
  destruct w; unfold mk_cell, val_of, tag_of, it_width;
    cbn [Z.eqb Pos.eqb]; f_equal; apply repr_unsigned.
Qed.

(* ------------------------------------------------------------------ *)
(* Total array primitives.

   [ld_arr] and [st_arr] are partial: out of bounds is [Illegal].  Z3's [select]
   and [store] are total, and that mismatch is exactly what the extracted
   lowering used to paper over with a hand-written guard.  These are the total
   operations Z3 actually has, so [SmtCompile] can emit the guard as an
   ordinary conditional and the lowering can stop reasoning. *)
Definition arr_len_of {T : Type} (a : @Array T) : uint64 :=
  match a with Allocated b => arr_len b | Unallocated => repr 0 end.

Definition cell_at (a : @Array CrVal) (i : CrVal) : CrVal :=
  match i with
  | IntVal idx _ =>
      match (region_bytes a) !! (offset_to_key idx) with
      | Init v => v
      | Uninit => UninitVal
      end
  | _ => ErrorVal
  end.

(* Total in the INDEX -- no bounds check, which is the whole point -- but still
   refuses an undeclared region, exactly as [st_arr] does.  Z3's [store] would
   happily produce an array there; keeping [Unallocated] is what preserves
   [SmtModuleQuery.eval_smt_mem_rooted], and it costs nothing because every
   access to an undeclared region is guarded off by [smt_arr_len] being 0. *)
Definition st_cell (a : @Array CrVal) (i : CrVal) (v : CrVal) : @Array CrVal :=
  match a, i with
  | Allocated b, IntVal idx _ =>
      Allocated {| arr_len := arr_len b;
                   arr_bytes := PMap.set (offset_to_key idx) (Init v) (arr_bytes b) |}
  | _, _ => a
  end.

Lemma crwidth_eqb_true : forall a b, crwidth_eqb a b = true -> a = b.
Proof. intros a b H; destruct a, b; simpl in H; try discriminate; reflexivity. Qed.

Lemma crinttype_eqb_true : forall a b, crinttype_eqb a b = true -> a = b.
Proof.
  intros [wa] [wb] H. unfold crinttype_eqb in H. simpl in H.
  apply crwidth_eqb_true in H. subst. reflexivity.
Qed.

Lemma int_eq_true : forall (a b : uint64), Integers.eq a b = true -> a = b.
Proof.
  intros a b H. unfold Integers.eq in H.
  destruct (zeq (unsigned a) (unsigned b)) as [e|]; [| discriminate].
  apply uintw_eq_from_unsigned. exact e.
Qed.

Lemma crwidth_eqb_refl : forall w, crwidth_eqb w w = true.
Proof. destruct w; reflexivity. Qed.

Lemma crinttype_eqb_refl : forall t, crinttype_eqb t t = true.
Proof. intros [w]; apply crwidth_eqb_refl. Qed.

Lemma int_eq_refl : forall (a : uint64), Integers.eq a a = true.
Proof.
  intros a. unfold Integers.eq.
  destruct (zeq (unsigned a) (unsigned a)); [reflexivity | congruence].
Qed.

Lemma eqb_refl : forall v, eqb v v = true.
Proof.
  intros v; destruct v as [a ta| |]; simpl.
  - rewrite crinttype_eqb_refl, int_eq_refl. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma crval_concrete_if_else : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct (eqb v1 v2) eqn:He; [| discriminate]. clear H.
  destruct v1 as [a ta| |]; destruct v2 as [b tb| |];
    simpl in He; try discriminate; try reflexivity.
  apply Bool.andb_true_iff in He as [Ht Hb].
  apply crinttype_eqb_true in Ht. apply int_eq_true in Hb. subst. reflexivity.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct (eqb v1 v2) eqn:He; [discriminate|]. clear H.
  intro Heq. subst v2. rewrite eqb_refl in He. discriminate.
Qed.

(* Round-tripping a [u64]-masked value through [unsigned] then re-masking is the
   identity: masking to the full 64-bit width is idempotent. *)
Lemma mask_width_W64_unsigned_idem : forall z,
  mask_width W64 (unsigned (mask_width W64 z)) = mask_width W64 z.
Proof.
  intro z. unfold mask_width, width_bits.
  set (a := repr (Z.land z (Z.ones 64))).
  rewrite Z.land_ones by lia.
  rewrite Z.mod_small.
  - apply repr_unsigned.
  - pose proof (unsigned_range a) as Hr.
    assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
    lia.
Qed.

(* Masking a value that is already 64 bits wide is the identity.  This is what
   makes the core fragment collapse onto plain bitvectors: [mk_int u64] of an
   existing [uint64]'s bits is that [uint64]. *)
Lemma mask_width_W64_id : forall (a : uint64), mask_width W64 (unsigned a) = a.
Proof.
  intros a. unfold mask_width, width_bits.
  rewrite Z.land_ones by lia.
  assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
  pose proof (unsigned_range a) as [Hlo Hhi]. rewrite Hmod in Hhi.
  rewrite Zmod_small by lia. apply repr_unsigned.
Qed.

Lemma mask_width_W64_small : forall z, 0 <= z < 2 ^ 64 -> mask_width W64 z = repr z.
Proof.
  intros z Hz. unfold mask_width, width_bits.
  rewrite Z.land_ones by lia. rewrite Zmod_small by lia. reflexivity.
Qed.

(* A [u8]-masked value fits in a byte -- the bound the solver side has to be
   told about a free region's cells, and the reason it is true. *)
Lemma mask_W8_lt_256 : forall z, unsigned (mask_width W8 z) < 256.
Proof.
  intros z. unfold mask_width, width_bits.
  rewrite Z.land_ones by lia.
  assert (Hb : 0 <= z mod 2 ^ 8 < 2 ^ 8) by (apply Z.mod_pos_bound; lia).
  assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
  rewrite unsigned_repr_eq, Hmod, Zmod_small by lia. lia.
Qed.

(* The same round trip at any width, not just [W64].  Masking to 64 bits and
   back loses nothing a narrower mask would have kept, because every
   [CrWidth] divides 64. *)
Lemma mask_width_unsigned_mask_W64 : forall w z,
  mask_width w (unsigned (mask_width W64 z)) = mask_width w z.
Proof.
  intros w z.
  assert (Hmod : @modulus 64%positive = (2 ^ 64)%Z) by (vm_compute; reflexivity).
  assert (Hu : unsigned (mask_width W64 z) = (z mod 2 ^ 64)%Z).
  { unfold mask_width, width_bits. rewrite unsigned_repr_eq, Hmod.
    rewrite Z.land_ones by lia.
    apply Z.mod_mod_divide. exists 1%Z; ring. }
  rewrite Hu. unfold mask_width.
  destruct w; unfold width_bits; f_equal;
    rewrite !Z.land_ones by lia;
    apply Z.mod_mod_divide;
    [ exists (2 ^ 56)%Z | exists (2 ^ 48)%Z | exists (2 ^ 32)%Z | exists 1%Z ];
    vm_compute; reflexivity.
Qed.

(* A [u64] value cast to [ty] is the same value built at [ty] directly.  This
   is what makes the symbolic parser's [SmtCast u64 of (SmtBitsToInt ...)]
   denote the concrete [mk_int of (bits_to_Z ...)] -- see the comment on
   [CrSymbolicSemanticsParser.apply_extract_symbolic], which asserts exactly
   this and until now had nothing backing it. *)
Lemma cast_u64_mk_int : forall ty z, cast u64 ty (mk_int u64 z) = mk_int ty z.
Proof.
  intros ty z. unfold cast, mk_int.
  cbn [u64 it_width crinttype_eqb crwidth_eqb].
  f_equal. apply mask_width_unsigned_mask_W64.
Qed.
