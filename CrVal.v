From Stdlib Require Import ZArith.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From MyProject Require Import Maps.

Inductive Check_T (T : Type) :=
| Legal (v : T)
| Illegal.
Arguments Legal {T} _.
Arguments Illegal {T}.

(* The width an operation acts at, analogous to the b/w/l/q suffix on x86
   mov: the operand storage is uniform, the *operation* picks the width. *)
Inductive CrWidth : Type :=
| W8 | W16 | W32 | W64.

(* The integer "type" an operation reads/writes at. Today this is just a width;
   it is the extension point for signedness (add [it_signed : bool] here and
   teach [coerce_to_type] to pick sign- vs zero-extension). Carrying a named
   record rather than a bare [CrWidth] means that future field is a definition
   change, not a re-threading of every operation. *)
Record CrIntType : Type := mkCrIntType {
  it_width : CrWidth;
}.

Definition u8  : CrIntType := mkCrIntType W8.
Definition u16 : CrIntType := mkCrIntType W16.
Definition u32 : CrIntType := mkCrIntType W32.
Definition u64 : CrIntType := mkCrIntType W64.

(* Integer storage is uniform 64-bit: a value is just bits, and the width an
   operation reads/writes at lives on the operation ([CrIntType]). Reads
   normalize through [coerce_to_type]. *)
Inductive CrInt_T : Type :=
| CrInt (val : uint64)
| CrNilInt.
Inductive CrPtr_T : Type :=
| CrPtr (addr : uintbptr)
| CrNilPtr.
Inductive CrVal : Type :=
| IntVal (val : CrInt_T)
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

Definition iveqb (x y : CrInt_T) : bool :=
  match x, y with
  | CrInt x', CrInt y' => Integers.eq x' y'
  | CrNilInt, CrNilInt => true
  | _, _ => false
  end.
Transparent iveqb.
Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | IntVal x', IntVal y' => iveqb x' y'
  | PtrVal (CrPtr x'), PtrVal (CrPtr y') => Integers.eq x' y'
  | PtrVal (CrNilPtr), PtrVal (CrNilPtr) => true
  | UninitVal, UninitVal
  | ErrorVal, ErrorVal => true
  | _, _ => false
  end.

Definition ivltb (x y : CrInt_T) : bool :=
  match x, y with
  | CrInt x', CrInt y' => Integers.ltu x' y'
  | _, _ => false
  end.
Transparent ivltb.
Definition ltb (x y : CrVal) : bool :=
  match x, y with
  | IntVal x', IntVal y'
    => ivltb x' y'
  | PtrVal (CrPtr x'), PtrVal (CrPtr y')
    => Integers.lt x' y'
  | _, _ => false
  end.

(* The unsigned Z held by an integer value. *)
Definition iv_unsigned (i : CrInt_T) : Z :=
  match i with
  | CrInt v  => unsigned v
  | CrNilInt => 0%Z
  end.

Definition width_bits (w : CrWidth) : Z :=
  match w with W8 => 8 | W16 => 16 | W32 => 32 | W64 => 64 end.

(* Reinterpret a raw integer [z] at width [w]: keep its low [width_bits w] bits
   in the uniform 64-bit container (truncate / zero-extend). This is what makes
   an operation's width meaningful — storage is uniform, the op picks the width. *)
Definition coerce_int_width (w : CrWidth) (z : Z) : CrInt_T :=
  CrInt (repr (Z.land z (Z.ones (width_bits w)))).

(* Read a value at type [t]. Only integers carry a width; everything else is
   passed through unchanged (a type mismatch surfaces later in the operation).
   This is the single chokepoint where signedness will branch (zero- vs
   sign-extension) once [CrIntType] grows an [it_signed] field. *)
Definition coerce_to_type (t : CrIntType) (v : CrVal) : CrVal :=
  match v with
  | IntVal i => IntVal (coerce_int_width (it_width t) (iv_unsigned i))
  | _ => v
  end.

Definition apply_iv_binop
  (f : uint64 -> uint64 -> uint64)
  (x y : CrInt_T) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' => IntVal (CrInt (f x' y'))
  | _, _ => ErrorVal
  end.
Transparent apply_iv_binop.

Definition add (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.add x' y'
  | _, _ => ErrorVal
  end.

Definition sub (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.sub x' y'
  | _, _ => ErrorVal
  end.

Definition and (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.and x' y'
  | _, _ => ErrorVal
  end.

Definition or (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.or x' y'
  | _, _ => ErrorVal
  end.

Definition xor (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.xor x' y'
  | _, _ => ErrorVal
  end.

Definition not (x : CrVal) : CrVal :=
  match x with
  | IntVal (CrInt x') => IntVal (CrInt (Integers.not x'))
  | _ => ErrorVal
  end.

Definition mul (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.mul x' y'
  | _, _ => ErrorVal
  end.

Definition divu (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.divu x' y'
  | _, _ => ErrorVal
  end.

Definition modu (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop Integers.modu x' y'
  | _, _ => ErrorVal
  end.

Definition ld_arr (a : Array) (i : CrVal) : Check_T CrVal :=
  match a, i with
  | Allocated array, IntVal (CrInt idx) =>
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
  | Allocated array, IntVal (CrInt idx) =>
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
    | PtrVal (CrPtr addr), IntVal (CrInt idx) => Mem
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

Lemma crval_concrete_if_else : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  unfold eqb, eq, Rocqlib.zeq in H.
  destruct v1, v2; try reflexivity; try discriminate;
  try (destruct val; exfalso; congruence);
  destruct val; destruct val0; try discriminate; try reflexivity; simpl in *; unfold eq in *;
  try destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)); try discriminate;
  try destruct (BinInt.Z.eq_dec (unsigned addr) (unsigned addr0)); try discriminate;
  try apply uintw_eq_from_unsigned in e; try rewrite e; try reflexivity;
  destruct (Rocqlib.zeq (unsigned val) (unsigned val0)); try congruence.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct v1, v2; try discriminate;
  unfold eqb in H;
  unfold iveqb in H;
  unfold eq in H;
  unfold Rocqlib.zeq in H;
  injection;
  destruct val, val0; try congruence;
  try destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)); try discriminate;
  try destruct (BinInt.Z.eq_dec (unsigned addr) (unsigned addr0)); try discriminate;
  apply uintw_neq_from_unsigned in n; congruence.
Qed.
