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
| CrUInt32 (val : uint32)
| CrNilInt.
Inductive CrPtr_T : Type :=
| CrPtr (addr : uintptr)
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

Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
  | PtrVal (CrPtr x'), PtrVal (CrPtr y') => Integers.eq x' y'
  | UninitVal, UninitVal
  | ErrorVal, ErrorVal
  | IntVal (CrNilInt), IntVal (CrNilInt)
  | PtrVal (CrNilPtr), PtrVal (CrNilPtr) => true
  | _, _ => false
  end.

Definition ltb (x y : CrVal) : bool :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
  | PtrVal (CrPtr x'), PtrVal (CrPtr y')
    => Integers.lt x' y'
  | IntVal (CrNilInt), IntVal (CrNilInt)
  | PtrVal (CrNilPtr), PtrVal (CrNilPtr)
    => true
  | _, _ => false
  end.

Definition add (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.add x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.add x' y')))
  | _, _ => Illegal
  end.

Definition sub (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.sub x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.sub x' y')))
  | _, _ => Illegal
  end.

Definition and (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.and x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.and x' y')))
  | _, _ => Illegal
  end.

Definition or (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.or x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.or x' y')))
  | _, _ => Illegal
  end.

Definition xor (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.xor x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.xor x' y')))
  | _, _ => Illegal
  end.

Definition not (x : CrVal) : Check_T CrVal :=
  match x with
  | IntVal (CrUInt8 x')
    => Legal (IntVal (CrUInt8 (Integers.not x')))
  | IntVal (CrUInt32 x')
    => Legal (IntVal (CrUInt32 (Integers.not x')))
  | _ => Illegal
  end.

Definition mul (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.mul x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.mul x' y')))
  | _, _ => Illegal
  end.

Definition divu (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.divu x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.divu x' y')))
  | _, _ => Illegal
  end.

Definition modu (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.modu x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.modu x' y')))
  | _, _ => Illegal
  end.

Definition ld_arr (a : Array) (i : CrVal) : Check_T CrVal :=
  match a, i with
  | Allocated array, IntVal (CrUInt32 idx) =>
    if (Integers.ltu idx (arr_len array)) then
      match (arr_bytes array) !! (pkey_to_mkey idx) with
      | Init v => Legal v
      | Uninit => Illegal
      end
    else
      Illegal
  | _, _ => Illegal
  end.

Definition ld (m : Memory CrVal) (p : CrVal) (i : CrVal) : Check_T CrVal :=
  match m with
  | Mem m' =>
    match p, i with
    | PtrVal (CrPtr addr), IntVal (CrUInt32 idx) =>
      match m' !! (pkey_to_mkey addr) with
      | Allocated array =>
        if (Integers.ltu idx (arr_len array)) then
          match (arr_bytes array) !! (pkey_to_mkey idx) with
          | Init v => Legal v
          | Uninit => Illegal
          end
        else
          Illegal
      | Unallocated => Illegal
      end
    | _, _ => Illegal
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

Definition st (m : Memory CrVal) (p : CrVal) (i : CrVal) (v : CrVal) : Check_T (Memory CrVal) :=
  match m with
  | Mem m' =>
    match p, i with
    | PtrVal (CrPtr addr), IntVal (CrUInt32 idx) =>
      match m' !! (pkey_to_mkey addr) with
      | Allocated array =>
        if (Integers.ltu idx (arr_len array)) then
          Legal (Mem (PMap.set (pkey_to_mkey addr) (Allocated {|
            arr_len := arr_len array;
            arr_bytes := PMap.set (pkey_to_mkey idx) (Init v) (arr_bytes array);
          |}) m'))
        else
          Illegal
      | Unallocated => Illegal
      end
    | _, _ => Illegal
    end
  | Invalid => Illegal
  end.

Definition tabula_rasa {T : Type} : Memory T :=
  Mem (PMap.init Unallocated).

(* TODO: Handle allocation collisions i.e. set mem to Invalid *)
Definition alloc {T : Type} (m : Memory T) (arg1 : CrVal) (arg2 : CrVal) : Check_T (Memory T) :=
  match m with
  | Mem m' =>
    match arg1, arg2 with
    | PtrVal (CrPtr addr), IntVal (CrUInt32 idx) => Legal (Mem
        (PMap.set (pkey_to_mkey addr) (Allocated {|
          arr_len := idx;
          arr_bytes := PMap.init Uninit;
      |}) m'))
    | _, _ => Illegal
    end
  | Invalid => Illegal
  end.

(* TODO: Handle double free *)
Definition free {T : Type} (m : Memory T) (arg1 : CrVal) : Check_T (Memory T) :=
  match m with
  | Mem m' =>
    match arg1 with
    | PtrVal (CrPtr b) => Legal (Mem
        (PMap.set (pkey_to_mkey b) Unallocated m'))
    | _ => Illegal
    end
  | Invalid => Illegal
  end.

Lemma crval_concrete_if_else : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  unfold eqb, eq, Rocqlib.zeq in H.
  destruct v1, v2; try reflexivity; try discriminate;
  try (destruct val; exfalso; congruence);
  destruct val; destruct val0; try discriminate; try reflexivity;
  try destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)); try discriminate;
  try destruct (BinInt.Z.eq_dec (unsigned addr) (unsigned addr0)); try discriminate;
  apply uintw_eq_from_unsigned in e; rewrite e; reflexivity.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof.
  intros v1 v2 H.
  destruct v1, v2; try discriminate;
  unfold eqb in H;
  unfold eq in H;
  unfold Rocqlib.zeq in H;
  injection;
  destruct val, val0; try congruence;
  try destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)); try discriminate;
  try destruct (BinInt.Z.eq_dec (unsigned addr) (unsigned addr0)); try discriminate;
  intros;
  apply uintw_neq_from_unsigned in n; congruence.
Qed.
