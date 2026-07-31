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
