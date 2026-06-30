From Stdlib Require Import ZArith.
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

Inductive CrPtr_T : Type :=
| CrPtr (addr : uintbptr)
| CrNilPtr.

(* A value is uniform 64-bit storage [val] tagged with its integer type [ity].
   Operations require their operands to already carry the matching type and
   produce ErrorVal otherwise; the uninitialized / nil integer is [UninitVal]. *)
Inductive CrVal : Type :=
| IntVal (val : uint64) (ity : CrIntType)
| PtrVal (val : CrPtr_T)
| UninitVal
| ErrorVal.

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
Inductive Memory (T : Type) :=
| Mem (m : PMap.t (@Array T))
| Invalid.
Arguments Mem {T} _.
Arguments Invalid {T}.

(* requires S to prevent collision @ 0 *)
Definition pkey_to_mkey {w} (p : @bit_int w) : positive :=
  Pos.of_nat (S (Z.to_nat (unsigned p))).

(* Mask a raw integer into the low [width_bits w] bits of the 64-bit container. *)
Definition mask_width (w : CrWidth) (z : Z) : uint64 :=
  repr (Z.land z (Z.ones (width_bits w))).

(* Build a typed integer value, masking its bits to the type's width. *)
Definition mk_int (ty : CrIntType) (z : Z) : CrVal :=
  IntVal (mask_width (it_width ty) z) ty.

(* Equality and unsigned-less-than require the operands to share a type. *)
Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | IntVal a ta, IntVal b tb => crinttype_eqb ta tb && Integers.eq a b
  | PtrVal (CrPtr a), PtrVal (CrPtr b) => Integers.eq a b
  | PtrVal CrNilPtr, PtrVal CrNilPtr => true
  | UninitVal, UninitVal
  | ErrorVal, ErrorVal => true
  | _, _ => false
  end.

Definition ltb (x y : CrVal) : bool :=
  match x, y with
  | IntVal a ta, IntVal b tb => crinttype_eqb ta tb && Integers.ltu a b
  | PtrVal (CrPtr a), PtrVal (CrPtr b) => Integers.lt a b
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

Definition ld_arr (a : Array) (i : CrVal) : Check_T CrVal :=
  match a, i with
  | Allocated array, IntVal idx _ =>
    if (Integers.ltu idx (arr_len array)) then
      match (arr_bytes array) !! (pkey_to_mkey idx) with
      | Init v => Legal v
      | Uninit => Legal UninitVal
      end
    else
      Illegal
  | _, _ => Illegal
  end.

Definition ld (m : Memory CrVal) (p : CrVal) (i : CrVal) : Check_T CrVal :=
  match m with
  | Mem m' =>
    match p with
    | PtrVal (CrPtr addr) =>
      ld_arr (m' !! (pkey_to_mkey addr)) i
    | _ => Illegal
    end
  | Invalid => Illegal
  end.

Definition st_arr (a : Array) (i : CrVal) (v : CrVal) : Check_T Array :=
  match a, i with
  | Allocated array, IntVal idx _ =>
    if (Integers.ltu idx (arr_len array)) then
      Legal (Allocated {|
        arr_len := arr_len array;
        arr_bytes := PMap.set (pkey_to_mkey idx) (Init v) (arr_bytes array);
      |})
    else
      Illegal
  | _, _ => Illegal
  end.

Definition st (m : Memory CrVal) (p : CrVal) (i : CrVal) (v : CrVal) : Memory CrVal :=
  match m with
  | Mem m' =>
    match p with
    | PtrVal (CrPtr addr) =>
      match st_arr (m' !! (pkey_to_mkey addr)) i v with
      | Legal arr => Mem (PMap.set (pkey_to_mkey addr) arr m')
      | Illegal => Invalid
      end
    | _ => Invalid
    end
  | Invalid => Invalid
  end.

Definition tabula_rasa {T : Type} : Memory T :=
  Mem (PMap.init Unallocated).

(* TODO: Handle allocation collisions i.e. set mem to Invalid *)
Definition alloc {T : Type} (m : Memory T) (arg1 : CrVal) (arg2 : CrVal) : Memory T :=
  match m with
  | Mem m' =>
    match arg1, arg2 with
    | PtrVal (CrPtr addr), IntVal idx _ => Mem
        (PMap.set (pkey_to_mkey addr) (Allocated {|
          arr_len := idx;
          arr_bytes := PMap.init Uninit;
      |}) m')
    | _, _ => Invalid
    end
  | Invalid => Invalid
  end.

(* TODO: Handle double free *)
Definition free {T : Type} (m : Memory T) (arg1 : CrVal) : Memory T :=
  match m with
  | Mem m' =>
    match arg1 with
    | PtrVal (CrPtr b) => Mem
        (PMap.set (pkey_to_mkey b) Unallocated m')
    | _ => Invalid
    end
  | Invalid => Invalid
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
  intros v; destruct v as [a ta| p | |]; simpl.
  - rewrite crinttype_eqb_refl, int_eq_refl. reflexivity.
  - destruct p; [apply int_eq_refl | reflexivity].
  - reflexivity.
  - reflexivity.
Qed.

Lemma crval_concrete_if_else : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct (eqb v1 v2) eqn:He; [| discriminate]. clear H.
  destruct v1 as [a ta| [a1|] | |]; destruct v2 as [b tb| [b1|] | |];
    simpl in He; try discriminate; try reflexivity.
  - apply Bool.andb_true_iff in He as [Ht Hb].
    apply crinttype_eqb_true in Ht. apply int_eq_true in Hb. subst. reflexivity.
  - apply int_eq_true in He. subst. reflexivity.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct (eqb v1 v2) eqn:He; [discriminate|]. clear H.
  intro Heq. subst v2. rewrite eqb_refl in He. discriminate.
Qed.
