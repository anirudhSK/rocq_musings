From MyProject Require Import MyInts.
From MyProject Require Import Integers.

Inductive CrVal : Type :=
| CrInt (val : uint8)
| CrPtr (base : uintptr) (offset : uintptr)
| CrNil.

Definition eqb (x y : CrVal) : bool :=
  match x, y with
  | CrInt x', CrInt y' => Integers.eq x' y'
  | CrPtr b1 o1, CrPtr b2 o2 =>
    (Integers.eq b1 b2) &&
    (Integers.eq o1 o2)
  | CrNil, CrNil => true
  | _, _ => false
  end.

Definition add (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.add x' y'))
  | CrPtr b' o', CrInt y_ =>
    let y' : uintptr := repr (intval y_) in
    (CrPtr b' (Integers.add o' y'))
  | _, _ => CrNil
  end.

Definition sub (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.sub x' y'))
  | CrPtr b' o', CrInt y_ =>
    let y' : uintptr := repr (intval y_) in
    (CrPtr b' (Integers.sub o' y'))
  | _, _ => CrNil
  end.

Definition and (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.and x' y'))
  | _, _ => CrNil
  end.

Definition or (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.or x' y'))
  | _, _ => CrNil
  end.

Definition xor (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.xor x' y'))
  | _, _ => CrNil
  end.

Definition not (x : CrVal) : CrVal :=
  match x with
  | CrInt x' =>
    (CrInt (Integers.not x'))
  | _ => CrNil
  end.

Definition mul (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.mul x' y'))
  | _, _ => CrNil
  end.

Definition divu (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.divu x' y'))
  | _, _ => CrNil
  end.

Definition modu (x y : CrVal) : CrVal :=
  match x, y with
  | CrInt x', CrInt y' =>
    (CrInt (Integers.modu x' y'))
  | _, _ => CrNil
  end.

Lemma crval_concrete_if_else : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = true)->
  v1 = v2.
Proof.
  intros v1 v2 H.
  destruct v1, v2; try discriminate.
  - unfold eqb in H.
    unfold eq in H.
    unfold Rocqlib.zeq in H.
    destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0)).
    + apply uintw_eq_from_unsigned in e.
      rewrite e.
      reflexivity.
    + exfalso. congruence.
  - unfold eqb in H.
    unfold eq in H.
    unfold Rocqlib.zeq in H.
    destruct (BinInt.Z.eq_dec (unsigned base) (unsigned base0));
    destruct (BinInt.Z.eq_dec (unsigned offset) (unsigned offset0));
    simpl in *.
    + apply uintw_eq_from_unsigned in e.
      apply uintw_eq_from_unsigned in e0.
      rewrite e. rewrite e0. reflexivity.
    + exfalso. congruence.
    + exfalso. congruence.
    + exfalso. congruence.
  - reflexivity.
Qed.

Lemma crval_concrete_if_else2 : forall (v1 v2 : CrVal),
  ((if eqb v1 v2 then true else false) = false)->
  v1 <> v2.
Proof with congruence.
  intros v1 v2 H.
  destruct v1, v2; try discriminate;
  unfold eqb in H;
  unfold eq in H;
  unfold Rocqlib.zeq in H.
  - destruct (BinInt.Z.eq_dec (unsigned val) (unsigned val0));
    try injection...
  - destruct (BinInt.Z.eq_dec (unsigned base) (unsigned base0));
    destruct (BinInt.Z.eq_dec (unsigned offset) (unsigned offset0));
    simpl in *; try injection...        
Qed.
