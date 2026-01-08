Require Import ZArith.
Require Import List.
Import ListNotations.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From MyProject Require Import Maps.
From MyProject Require Import ListUtils.
From MyProject Require Import CrVarLike.

(*
In essence, I'm representing memory as a set of arrays.
Each array boils down to a starting address, a length, and the bytes themselves.
*)
Record Array := {
  base : nat;
  len : nat;
  bytes : PMap.t (option uint8)
}.
Definition Memory := PMap.t (option Array).

(*
Because bytes are stored as a PMap.t, each byte is associated with
a positive number. I'm doing 0-indexing, so that means that index i
is a natural number (incl. 0), but the key in the PMap associated
with it is i + 1 (since 0 \notin positive).
*)
Definition keys_from_map {T : Type} (m : PMap.t T) : list positive :=
  List.map fst (PTree.elements (snd m)).
Definition key_to_idx (k: positive) : nat :=
  (Pos.to_nat k) - 1.
Definition idx_to_key (i: nat) : positive :=
  (Pos.of_nat (i + 1)).

(* more map accessor helpers since I'm storing an option type *)
Definition vals_from_map {T : Type} (m : PMap.t T) : list T :=
  List.map snd (PTree.elements (snd m)).
Fixpoint unnone {T : Type} (l : list (option T)) : list T :=
  match l with
  | [] => []
  | x :: xs => match x with
    | Some x' => x' :: (unnone xs)
    | None => unnone xs
    end
  end.
Definition vals_from_map' {T : Type} (m : PMap.t (option T)) : list T :=
  unnone (vals_from_map m).

(* checks that two arrays don't overlap *)
Definition arrays_disjoint (a1 a2 : Array) : bool :=
  let start1 := base a1 in
  let end1 := (base a1) + (len a1) in
  let start2 := base a2 in
  let end2 := (base a2) + (len a2) in
  (negb (start1 =? start2)) && (
    ((start1 <? start2) && (end1 <? start2)) ||
    ((start2 <? start1) && (end2 <? start1))).
(* checks that an array doesn't overlap with any other arrays *)
Definition array_unique (x : Array) (xs : list Array) :=
  List.forallb (fun x' => arrays_disjoint x x') xs.
Fixpoint mem_disjoint_helper (A : list Array) :=
  match A with
  | [] => true
  | x :: xs => if (array_unique x xs) then
      mem_disjoint_helper xs
    else
      false
  end.
(* checks that all arrays are unique *)
Definition memory_disjoint (mem : Memory) : bool :=
  mem_disjoint_helper (vals_from_map' mem).

Fixpoint valid_offset_helper (off : list nat) (len : nat) :=
  match off with
  | [] => true
  | x :: xs => andb (x <? len) (valid_offset_helper xs len)
  end.
(* checks that an array has no out-of-bounds stores *)
Definition has_valid_offsets (a : Array) : bool :=
  let l := len a in
  let mem := bytes a in
  let idxs := List.map key_to_idx (keys_from_map mem) in
  valid_offset_helper idxs l.
(* checks that all arrays have no OoB stores *)
Definition all_array_offsets_valid (mem : Memory) : bool :=
  List.forallb has_valid_offsets (vals_from_map' mem).

(* what I'm initially assuming to be a sane understanding of valid memory *)
Definition valid_memory (mem : Memory) : Prop :=
  (* arrays have different address ranges *)
  ((memory_disjoint mem) = true) /\
  (* arrays stay within their address ranges *)
  ((all_array_offsets_valid mem) = true).

(* a pointer is an offset into an array *)
Inductive Ptr : Type :=
| Address (base: nat) (offset : nat).
Definition ptr_base (p : Ptr) : positive :=
  idx_to_key match p with
  | Address x _ => x
  end.
Definition ptr_off (p : Ptr) : positive :=
  idx_to_key match p with
  | Address _ x => x
  end.

(* check if a pointer's array is in memory *)
Definition find_array (mem : Memory) (p : Ptr) : option Array :=
  mem !! (ptr_base p).

(* load the value that a pointer points to *)
Definition ld_arr (a : Array) (p : Ptr) : option uint8 :=
  (bytes a) !! (ptr_off p).
Definition ld_mem (mem : Memory) (p : Ptr) : option uint8 :=
  match (find_array mem p) with
  | Some a => ld_arr a p
  | None => None
  end.

(* store a value into a pointer *)
Definition st_arr (a : Array) (p : Ptr) (v : uint8) : option Array :=
  let off := ptr_off p in
  if (Pos.ltb off (Pos.of_nat (len a))) then
    Some {|
      base := base a;
      len := len a;
      bytes := PMap.set off (Some v) (bytes a)
    |}
  else
    None.
Definition st_mem' (mem : Memory) (p : Ptr) (v : uint8) : option Memory :=
  match (find_array mem p) with
  | Some a => match (st_arr a p v) with
    | Some a' => Some (PMap.set (ptr_base p) (Some a') mem)
    | None => None
    end
  | None => None
  end.
Definition st_mem (mem : Memory) (p : Ptr) (v : uint8) : Memory :=
  match (st_mem' mem p v) with
  | Some mem' => mem'
  | None => mem
  end.

(* accessing a pointer is valid if...
  - there exists an associated array in memory
  - the pointer's access into that array is in-bounds *)
Definition mem_access_valid (mem: Memory) (p : Ptr) : Prop :=
  let a := find_array mem p in
  let l := match a with
  | Some a' => (Pos.of_nat (len a'))
  | None => 1%positive
  end in
  (a <> None) /\ ((Pos.ltb (ptr_off p) l) = true).

(* random lemma I felt like proving *)
Lemma valid_st_lemma:
  forall (mem : Memory) (p : Ptr) (v : uint8),
  mem_access_valid mem p ->
  (st_mem' mem p v) <> None.
Proof.
  intros.
  destruct H as [H0 H1].
  destruct (find_array mem p) eqn:Harray; try congruence.
  unfold st_mem'.
  rewrite Harray.
  unfold st_arr.
  rewrite H1.
  discriminate.
Qed.

(* read after write lemmas *)
Lemma raw_same_address:
  forall (mem : Memory) (p : Ptr) (v : uint8),
  mem_access_valid mem p ->
  ld_mem (st_mem mem p v) p = Some v.
Proof.
  intros.
  unfold st_mem.
  assert (st_mem' mem p v <> None) as Hvsl. { apply valid_st_lemma. assumption. }
  destruct (st_mem' mem p v) eqn:Hm'; try congruence.
  unfold st_mem' in Hm'.
  destruct (find_array mem p) eqn:Harray; try congruence.
  destruct (st_arr a p v) eqn:Hstore; try congruence.
  injection Hm' as Hm.

  unfold ld_mem.
  rewrite <- Hm.
  unfold find_array.
  rewrite PMap.gss.

  unfold ld_arr.
  unfold st_arr in Hstore.
  destruct (Pos.ltb (ptr_off p) (Pos.of_nat (len a))) eqn:Hoffset; try congruence.
  injection Hstore as Hstore.
  rewrite <- Hstore. simpl.
  rewrite PMap.gss.

  reflexivity.
Qed.
Lemma raw_different_address:
  forall (mem : Memory) (p1 p2 : Ptr) (v : uint8),
  p1 <> p2 ->
  ld_mem mem p1 = ld_mem (st_mem mem p2 v) p1.
Proof.
  intros.
  unfold st_mem. unfold st_mem'.
  destruct (find_array mem p2) eqn:Hp2; try congruence.
  destruct (st_arr a p2 v) eqn:Ha2'; try congruence.

  unfold ld_mem.
  unfold find_array.
  destruct (Pos.eqb (ptr_base p1) (ptr_base p2)) eqn:Heq.
  - rewrite Pos.eqb_eq in Heq.
    rewrite Heq.
    rewrite PMap.gss.
    unfold ld_arr.
    unfold st_arr in Ha2'.
    unfold find_array in Hp2. rewrite Hp2.
    destruct (Pos.ltb (ptr_off p2) (Pos.of_nat (len a))) eqn:Hp2l; try congruence.
    injection Ha2' as Ha2'.
    rewrite <- Ha2'. simpl.
    rewrite PMap.gso.
    + reflexivity.
    + destruct p1. destruct p2. simpl in *.
      unfold ptr_off. unfold ptr_base in Heq.
      unfold idx_to_key. unfold idx_to_key in Heq.
      apply Nat2Pos.inj in Heq; try rewrite Nat.add_1_r; try discriminate.
      apply Nat.add_cancel_r in Heq.
      rewrite Heq in H.
      destruct (offset =? offset0) eqn:Hoff.
      * apply Nat.eqb_eq in Hoff.
        rewrite Hoff.
        congruence.
      * apply Nat.eqb_neq in Hoff.
        intro Hcontra.
        apply Nat2Pos.inj in Hcontra; try rewrite Nat.add_1_r; try discriminate.
        rewrite Nat.add_1_r in Hcontra. injection Hcontra as Hcontra.
        contradiction.
  - rewrite Pos.eqb_neq in Heq.
    rewrite PMap.gso.
    + reflexivity.
    + assumption.
Qed.

(* Case 2 Example *)
Inductive Value : Type :=
| Numeric (val: uint8)
| Pointer (val : Ptr)
| NilVal.
Definition Registers : Type := PMap.t Value.
Record Machine := {
  registers: Registers;
  memory: Memory
}.

Definition TabulaRasa : Machine := {|
  registers := PMap.init NilVal;
  memory := PMap.init None
|}.

Definition alloc (m : Machine) (base nbyte : nat) : Machine := {|
  registers := registers m;
  memory := PMap.set (Pos.of_nat (base+1)) (Some {|
    base := base;
    len := nbyte;
    bytes := PMap.init None
  |}) (memory m)
|}.
Definition get_reg (m : Machine) (i : positive) : Value :=
  (registers m) !! i.
Definition x_reg (m : Machine) (i : positive) : Value :=
  match get_reg m i with
  | Pointer p => match ld_mem (memory m) p with
    | Some v => Numeric v
    | None => NilVal
    end
  | _ => NilVal
  end.
Definition set_reg (m : Machine) (i : positive) (v : Value) : Machine := {|
  registers := PMap.set i v (registers m);
  memory := memory m
|}.

(* t = *f *)
Definition ld_reg (m : Machine) (f t : positive) : Machine :=
  match get_reg m f with
  | Pointer p =>
    match ld_mem (memory m) p with
    | Some res => set_reg m t (Numeric res)
    | None => m
    end
  | _ => m
  end.
(* *t = f *)
Definition st_reg (m : Machine) (f t : positive) : Machine :=
  match (get_reg m t), (get_reg m f) with
  | Pointer p, Numeric v => {|
      registers := registers m;
      memory := st_mem (memory m) p v
    |}
  | _, _ => m
  end.
  
Definition add_ (v1 v2 : Value) : Value :=
  match v1, v2 with
  | Numeric x, Numeric y => Numeric (Integers.add x y)
  | _, _ => NilVal
  end.

Definition m' :=
  (* initialize *)
  let m0 := TabulaRasa in
  (* alloc 128 bytes @ 0 *)
  let m1 := alloc m0 0 128 in
  (* u8* r1 = 0x0 *)
  let m2 := set_reg m1 1 (Pointer (Address 0 0)) in
  (* *0x0 = 67 *)
  let m3 := {|
    registers := registers m2;
    memory := st_mem (memory m2) (Address 0 0) (repr 67)
  |} in
  m3.

Definition prog_1 :=
  (* Example Program *)
  (* r3 = *r1 *)
  let m4 := ld_reg m' 1 3 in
  (* r6 = 10 *)
  let m5 := set_reg m4 6 (Numeric (repr 10)) in
  (* r7 = r1 *)
  let m6 := set_reg m5 7 (get_reg m5 1) in
  (* *r7 = r6 *)
  let m7 := st_reg m6 6 7 in
  (* r5 = r1 *)
  let m8 := set_reg m7 5 (get_reg m7 1) in
  (* r4 = *r5 *)
  let m9 := ld_reg m8 5 4 in
  (* r2 = r3 + r4 *)
  let ma := set_reg m9 2 (add_
    (get_reg m9 3)
    (get_reg m9 4)) in
  get_reg ma 2.

Definition prog_2 :=
  (* r3 = *r1 *)
  let m4 := ld_reg m' 1 3 in
  (* r6 = 10 *)
  let m5 := set_reg m4 6 (Numeric (repr 10)) in
  (* r2 = r3 + r6 *)
  let m6 := set_reg m5 2 (add_
    (get_reg m5 6)
    (get_reg m5 3)) in
  get_reg m6 2.

Example p1_p2_eq:
  prog_1 = prog_2.
Proof.
  unfold prog_1. unfold prog_2.
  unfold get_reg. simpl.
  repeat rewrite PMap.gss.
  unfold add.
  simpl.
  reflexivity.
Qed.
