Require Import ZArith.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From MyProject Require Import Maps.

Inductive Check_T (T : Type) :=
| Legal (v : T)
| Illegal.
Arguments Legal {T} _.
Arguments Illegal {T}.

Inductive CrInt_T : Type :=
| CrUInt8 (val : uint8)
| CrUInt16 (val : uint16)
| CrUInt32 (val : uint32)
| CrUInt64 (val : uint64)
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
  arr_len : uint32;
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
  | CrUInt8 x', CrUInt8 y'
  | CrUInt16 x', CrUInt16 y'
  | CrUInt32 x', CrUInt32 y'
  | CrUInt64 x', CrUInt64 y' => Integers.eq x' y'
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
  | CrUInt8 x', CrUInt8 y'
  | CrUInt16 x', CrUInt16 y'
  | CrUInt32 x', CrUInt32 y'
  | CrUInt64 x', CrUInt64 y' => Integers.lt x' y'
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

Definition apply_iv_binop
  (f :forall (w : positive), @bit_int w -> @bit_int w -> @bit_int w)
  (x y : CrInt_T) : CrVal :=
  match x, y with
  | CrUInt8 x', CrUInt8 y'
    => IntVal (CrUInt8 (@f _ x' y'))
  | CrUInt16 x', CrUInt16 y'
    => IntVal (CrUInt16 (@f _ x' y'))
  | CrUInt32 x', CrUInt32 y'
    => IntVal (CrUInt32 (@f _ x' y'))
  | CrUInt64 x', CrUInt64 y'
    => IntVal (CrUInt64 (@f _ x' y'))
  | _, _ => ErrorVal
  end.
Transparent apply_iv_binop.

Definition add (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.add w) x' y'
  | _, _ => ErrorVal
  end.

Definition sub (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.sub w) x' y'
  | _, _ => ErrorVal
  end.

Definition and (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.and w) x' y'
  | _, _ => ErrorVal
  end.

Definition or (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.or w) x' y'
  | _, _ => ErrorVal
  end.

Definition xor (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.xor w) x' y'
  | _, _ => ErrorVal
  end.

Definition not (x : CrVal) : CrVal :=
  match x with
  | IntVal (CrUInt8 x')
    => IntVal (CrUInt8 (Integers.not x'))
  | IntVal (CrUInt16 x')
    => IntVal (CrUInt16 (Integers.not x'))
  | IntVal (CrUInt32 x')
    => IntVal (CrUInt32 (Integers.not x'))
  | IntVal (CrUInt64 x')
    => IntVal (CrUInt64 (Integers.not x'))
  | _ => ErrorVal
  end.

Definition mul (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.mul w) x' y'
  | _, _ => ErrorVal
  end.

Definition divu (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.divu w) x' y'
  | _, _ => ErrorVal
  end.

Definition modu (x y : CrVal) : CrVal :=
  match x, y with
  | IntVal x', IntVal y' => apply_iv_binop (fun w => @Integers.modu w) x' y'
  | _, _ => ErrorVal
  end.

Definition ld_arr (a : Array) (i : CrVal) : Check_T CrVal :=
  match a, i with
  | Allocated array, IntVal (CrUInt32 idx) =>
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
  | Allocated array, IntVal (CrUInt32 idx) =>
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
    | PtrVal (CrPtr addr), IntVal (CrUInt32 idx) => Mem
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
