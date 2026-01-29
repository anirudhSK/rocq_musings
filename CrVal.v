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
| CrPtr (base : uintptr) (idx : uintptr)
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
Definition pkey_to_mkey (p : uintptr) : positive :=
  Pos.of_nat (S (Z.to_nat (unsigned p))).

Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y') => Integers.eq x' y'
  | PtrVal (CrPtr b1 o1), PtrVal (CrPtr b2 o2) =>
    (Integers.eq b1 b2) &&
    (Integers.eq o1 o2)
  | UninitVal, UninitVal
  | ErrorVal, ErrorVal
  | IntVal (CrNilInt), IntVal (CrNilInt)
  | PtrVal (CrNilPtr), PtrVal (CrNilPtr) => true
  | _, _ => false
  end.

Definition add (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.add x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.add x' y')))
  | PtrVal (CrPtr b' o'), IntVal (CrUInt32 y_)
    => let y' : uintptr := repr (intval y_) in
       Legal (PtrVal (CrPtr b' (Integers.add o' y')))
  | _, _ => Illegal
  end.

Definition sub (x y : CrVal) : Check_T CrVal :=
  match x, y with
  | IntVal (CrUInt8 x'), IntVal (CrUInt8 y')
    => Legal (IntVal (CrUInt8 (Integers.sub x' y')))
  | IntVal (CrUInt32 x'), IntVal (CrUInt32 y')
    => Legal (IntVal (CrUInt32 (Integers.sub x' y')))
  (* | PtrVal (CrPtr b' o'), IntVal (CrUInt32 y_)
    => let y' : uintptr := repr (intval y_) in
       Legal (PtrVal (CrPtr b' (Integers.sub o' y'))) *)
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

Definition ld (m : Memory CrVal) (p : CrVal) : Check_T CrVal :=
  match m with
  | Mem m' => 
    match p with
    | PtrVal (CrPtr base idx) =>
      match m' !! (pkey_to_mkey base) with
      | Allocated array => if (Integers.ltu idx (arr_len array)) then
          match (arr_bytes array) !! (pkey_to_mkey idx) with
          | Init v => Legal v
          | Uninit => Legal UninitVal
          end
        else
          Illegal
      | Unallocated => Illegal
      end
    | _ => Illegal
    end
  | Invalid => Illegal
  end.

Definition st (m : Memory CrVal) (p : CrVal) (v : CrVal) : Check_T (Memory CrVal) :=
  match m with
  | Mem m' =>
    match p with
    | PtrVal (CrPtr base idx) =>
      match m' !! (pkey_to_mkey base) with
      | Allocated array => if (Integers.ltu idx (arr_len array)) then
          Legal (Mem (PMap.set (pkey_to_mkey base) (Allocated {|
            arr_len := arr_len array;
            arr_bytes := PMap.set (pkey_to_mkey idx) (Init v) (arr_bytes array);
          |}) m'))
        else
          Illegal
      | Unallocated => Illegal
      end
    | _ => Illegal
    end
  | Invalid => Illegal
  end.

Definition tabula_rasa {T : Type} : Memory T :=
  Mem (PMap.init Unallocated).

(* TODO: Handle allocation collisions i.e. set mem to Invalid *)
Definition alloc {T : Type} (m : Memory T) (arg1 : CrVal) : Check_T (Memory T) :=
  match m with
  | Mem m' =>
    match arg1 with
    | PtrVal (CrPtr b l) => Legal (Mem
        (PMap.set (pkey_to_mkey b) (Allocated {|
          arr_len := l;
          arr_bytes := PMap.init Uninit;
      |}) m'))
    | _ => Illegal
    end
  | Invalid => Illegal
  end.

(* TODO: Handle double free *)
Definition free {T : Type} (m : Memory T) (arg1 : CrVal) : Check_T (Memory T) :=
  match m with
  | Mem m' =>
    match arg1 with
    | PtrVal (CrPtr b _) => Legal (Mem
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
  try (destruct val; exfalso; congruence).
  - destruct val; destruct val0; try discriminate; try reflexivity;
    destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)); try discriminate;
    apply uintw_eq_from_unsigned in e; rewrite e; reflexivity.
  - destruct val, val0; try discriminate; try reflexivity.
    destruct (BinInt.Z.eq_dec (unsigned base) (unsigned base0)); try discriminate.
    destruct (BinInt.Z.eq_dec (unsigned idx) (unsigned idx0)); try discriminate.
    apply uintw_eq_from_unsigned in e, e0.
    rewrite e, e0; reflexivity.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof with try injection; try congruence; intros.
  intros v1 v2 H.
  destruct v1, v2; try discriminate;
  unfold eqb in H;
  unfold eq in H;
  unfold Rocqlib.zeq in H;
  try injection; try congruence; intros.
  - destruct val, val0; try congruence;
    destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0))...
  - destruct val, val0; try congruence.
    destruct (BinInt.Z.eq_dec (unsigned base) (unsigned base0));
    destruct (BinInt.Z.eq_dec (unsigned idx) (unsigned idx0)); try discriminate;
    simpl in *.
    + apply uintw_eq_from_unsigned in e.
      apply uintw_neq_from_unsigned in n.
      rewrite e in H1.
      inversion H1. congruence.
    + apply uintw_neq_from_unsigned in n.
      apply uintw_eq_from_unsigned in e.
      rewrite e in H1.
      inversion H1. congruence.
    + apply uintw_neq_from_unsigned in n, n0.
      inversion H0. congruence.
Qed.
