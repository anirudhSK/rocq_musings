Require Import ZArith.
Require Import List.
Import ListNotations.
From MyProject Require Import MyInts.
From MyProject Require Import Integers.
From MyProject Require Import Maps.
From MyProject Require Import ListUtils.
(* From MyProject Require Import CrVarLike.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import SmtQuery. *)

Inductive Check_T (T : Type) :=
| Legal (v : T)
| Illegal.
Arguments Legal {T} _.
Arguments Illegal {T}.

(*
In essence, I'm representing memory as a set of arrays.
Each array boils down to a starting address, a length, and the bytes themselves.
*)

Inductive MemVal (T : Type) :=
| Init (v : T)
| Uninit.
Arguments Uninit {T}.
Record MemBlock (T : Type) := {
  arr_len : positive;
  arr_bytes : PMap.t (MemVal T);
}.
Arguments arr_len {T} _.
Arguments arr_bytes {T} _.

Inductive Array {T : Type} :=
| Allocated (arr : MemBlock T)
| Unallocated.
Arguments Unallocated {T}.
Definition Memory (T : Type) := PMap.t (@Array T).

Record MachineState (T : Type) := {
  reg_state : PMap.t T;
  mem_state : Memory T;
}.
Arguments reg_state {T} _.
Arguments mem_state {T} _.

(* Values in the array can either be initialized or not *)

Definition keys_from_map {T : Type} (m : PMap.t T) : list positive :=
  List.map fst (PTree.elements (snd m)).
Transparent keys_from_map.
Definition vals_from_map {T : Type} (m : PMap.t T) : list T :=
  List.map snd (PTree.elements (snd m)).
Transparent vals_from_map.

Definition block_is_valid {T : Type} (block : MemBlock T) : Prop :=
  forall (idx : positive),
  PTree.get idx (snd (arr_bytes block)) <> None -> (Pos.le idx (arr_len block)).

Definition Mt {T : Type} (len : positive) : MemBlock T := {|
  arr_len := len;
  arr_bytes := PMap.init Uninit;
|}.
Definition TabulaRasa {T : Type} : Memory T :=
  PMap.init Unallocated.

Lemma mt_is_valid:
  forall (T: Type) (len : positive),
  @block_is_valid T (Mt len).
Proof.
  unfold block_is_valid.
  intros.
  unfold Mt. simpl in *.
  unfold PTree.get in H. simpl in H.
  exfalso. congruence.
Qed.

Definition get_array {T : Type} (mem : Memory T) (base : positive) : Array :=
  mem !! base.
Transparent get_array.

(* possibly change to <> *)
Definition mem_disjoint {T : Type} (mem : Memory T) : Prop :=
  forall (base base' : positive),
  Pos.lt base base' ->
  match get_array mem base, get_array mem base' with
  | Allocated block, Allocated block' =>
    let len := arr_len block in
    let len' := arr_len block' in
    Pos.le (Pos.add base len) base'
  | _, _ => True
  end.

Definition mem_is_valid {T : Type} (mem : Memory T) : Prop :=
  mem_disjoint mem /\ (
    forall (base : positive),
    match get_array mem base with
    | Allocated block => block_is_valid block
    | Unallocated => True
    end
  ).

Lemma tab_rasa_is_valid:
  forall (T : Type),
  mem_is_valid (@TabulaRasa T).
Proof.
  unfold mem_is_valid, mem_disjoint. split;
  intros; simpl;
  apply I.
Qed.

(* load the value that a pointer points to *)
Definition ld_block {T : Type} (block : MemBlock T) (idx : positive) : @MemVal T :=
  (arr_bytes block) !! idx.
Definition ld_mem {T : Type} (mem : Memory T) (base : positive) (idx : positive)
  : Check_T MemVal :=
  match (get_array mem base) with
  | Allocated block => Legal (ld_block block idx)
  | Unallocated => Illegal
  end.

(* store a value into a pointer *)
Definition st_block {T : Type} (block : MemBlock T) (idx : positive) (v : T) : MemBlock T := {|
  arr_len := arr_len block;
  arr_bytes := PMap.set idx (Init v) (arr_bytes block);
|}.
Definition st_mem {T : Type} (mem : Memory T) (base : positive) (idx : positive) (v : T) : Check_T (Memory T) :=
  match (get_array mem base) with
  | Allocated block =>
    let block_len := arr_len block in
    if (Pos.leb idx block_len) then
      let block' := st_block block idx v in
      Legal (PMap.set base (Allocated block') mem)
    else
      Illegal
  | Unallocated => Illegal
  end.

Lemma ltb_neq:
  forall (x y : positive),
  Pos.lt x y -> x <> y.
Proof.
  intros.
  intro Hc. rewrite Hc in H.
  specialize Pos.lt_irrefl with (x := y).
  intros. congruence.
Qed.

Ltac b_to_props :=
  repeat match goal with
  | H : (?x =? ?y)%positive = true |- _ =>
    apply Pos.eqb_eq in H
  | H : (?x =? ?y)%positive = false |- _ =>
    apply Pos.eqb_neq in H
  end.

Lemma st_mem_preserves_validity:
  forall (T : Type) (mem : Memory T) (base : positive) (idx : positive) (v : T),
  mem_is_valid mem -> match (st_mem mem base idx v) with
  | Legal mem' => mem_is_valid mem'
  | Illegal => True
  end.
Proof with try assumption; try apply I.
  intros. unfold mem_is_valid in *.
  destruct (st_mem mem base idx v) eqn:Hst...
  split.
  admit.
Admitted.

(* Memory-capable IR *)
Inductive FnArg {T : Type} : Type :=
| PosArg (p : positive)
| RegArg (r : positive)
| ValArg (v : T).

Inductive Op {T : Type} : Type :=
| Alloc (arg1 arg2 : @FnArg T)
| Assign (arg1 arg2 : @FnArg T)
| Ld (arg1 arg2 : @FnArg T)
| St (arg1 arg2 : @FnArg T)
| Add (arg1 arg2 : @FnArg T).

Definition Program {T : Type} : Type := list (@Op T).

Definition ConcreteMState := MachineState CrVal.
Definition SymbolicMState := MachineState SmtArithExpr.

Definition alloc {T : Type} (m : MachineState T) (arg1 arg2 : @FnArg T) : Check_T (MachineState T) :=
  match arg1, arg2 with
  | PosArg b, PosArg l => Legal {|
    reg_state := reg_state m;
    mem_state := PMap.set b (Allocated {|
      arr_len := l;
      arr_bytes := PMap.init Uninit;
    |}) (mem_state m);
  |}
  | _, _ => Illegal
  end.

Definition set_reg {T : Type} (m : MachineState T) (arg1 arg2 : @FnArg T) : Check_T (MachineState T) :=
  match arg1, arg2 with
  | RegArg dst, RegArg src => Legal {|
    reg_state := PMap.set dst ((reg_state m) !! src) (reg_state m);
    mem_state := mem_state m;
  |}
  | RegArg dst, ValArg v => Legal {|
    reg_state := PMap.set dst v (reg_state m);
    mem_state := mem_state m;
  |}
  | _, _ => Illegal
  end.

Definition uint_to_pos (u : uintptr) : positive :=
  Pos.of_nat ((Z.to_nat (unsigned u)) + 1).

Definition ld_reg' (m : ConcreteMState) (arg1 arg2 : @FnArg CrVal) : Check_T (ConcreteMState) :=
  match arg1, arg2 with
  | RegArg dst, RegArg src =>
    match (reg_state m) !! src with
    | CrPtr b o =>
      match ld_mem (mem_state m) (uint_to_pos b) (uint_to_pos o) with
      | Legal (Init v) => Legal {|
        reg_state := PMap.set dst v (reg_state m);
        mem_state := mem_state m;
      |}
      | _ => Illegal
      end
    | _ => Illegal
    end
  | RegArg dst, ValArg (CrPtr b o) =>
    match ld_mem (mem_state m) (uint_to_pos b) (uint_to_pos o) with
    | Legal (Init v) => Legal {|
      reg_state := PMap.set dst v (reg_state m);
      mem_state := mem_state m;
    |}
    | _ => Illegal
    end
  | _, _ => Illegal
  end.

Definition st_reg' (m : ConcreteMState) (arg1 arg2 : @FnArg CrVal) : Check_T (ConcreteMState) :=
  match arg1, arg2 with
  | RegArg dst, RegArg src =>
    match (reg_state m) !! dst, (reg_state m) !! src with
    | CrPtr b o, v =>
      match st_mem (mem_state m) (uint_to_pos b) (uint_to_pos o) v with
      | Legal mem' => Legal {|
        reg_state := reg_state m;
        mem_state := mem';
      |}
      | _ => Illegal
      end
    | _, _ => Illegal
    end
  | RegArg dst, ValArg v =>
    match (reg_state m) !! dst with
    | CrPtr b o =>
      match st_mem (mem_state m) (uint_to_pos b) (uint_to_pos o) v with
      | Legal mem' => Legal {|
        reg_state := reg_state m;
        mem_state := mem';
      |}
      | _ => Illegal
      end
    | _ => Illegal
    end
  | _, _ => Illegal
  end.

Definition add_reg' (m : ConcreteMState) (arg1 arg2 : @FnArg CrVal) : Check_T (ConcreteMState) :=
  match arg1, arg2 with
  | RegArg dst, RegArg src =>
    match (reg_state m) !! dst, (reg_state m) !! src with
    | CrInt x, CrInt y => Legal {|
        reg_state := PMap.set dst (CrInt (Integers.add x y)) (reg_state m);
        mem_state := mem_state m;
      |}
    | CrPtr b o, CrInt y =>
      let y' : uintptr := repr (intval y) in
      Legal {|
        reg_state := PMap.set dst (CrPtr b (Integers.add o y')) (reg_state m);
        mem_state := mem_state m;
      |}
    | _, _ => Illegal
    end
  | RegArg dst, ValArg v =>
    match (reg_state m) !! dst, v with
    | CrInt x, CrInt y => Legal {|
        reg_state := PMap.set dst (CrInt (Integers.add x y)) (reg_state m);
        mem_state := mem_state m;
      |}
    | CrPtr b o, CrInt y =>
      let y' : uintptr := repr (intval y) in
      Legal {|
        reg_state := PMap.set dst (CrPtr b (Integers.add o y')) (reg_state m);
        mem_state := mem_state m;
      |}
    | _, _ => Illegal
    end
  | _, _ => Illegal
  end.

Definition example_program : Program := [
  Alloc  (PosArg 1) (PosArg 1024); (* allocate 1024 bytes at base 1 *)
  Assign (RegArg 2) (ValArg (CrPtr (repr 1) (repr 0))); (* r2 = ptr to base 1, offset 0 *)
  St     (RegArg 2) (ValArg (CrInt (repr 42))); (* *r2 = 42 *)
  Ld     (RegArg 3) (RegArg 2); (* r3 = *r2 *)
  Add    (RegArg 4) (RegArg 3) (* r4 = r3 + r3 *)
].

Definition apply_concrete (op : Op) (m : ConcreteMState) : Check_T ConcreteMState :=
  match op with
  | Alloc arg1 arg2 => alloc m arg1 arg2
  | Assign arg1 arg2 => set_reg m arg1 arg2
  | Ld arg1 arg2 => ld_reg' m arg1 arg2
  | St arg1 arg2 => st_reg' m arg1 arg2
  | Add arg1 arg2 => add_reg' m arg1 arg2
  end.

Fixpoint compile_concrete (p : Program) (m : ConcreteMState) : Check_T ConcreteMState :=
  match p with
  | [] => Legal m
  | x :: xs =>
    match apply_concrete x m with
    | Legal m' => compile_concrete xs m'
    | Illegal => Illegal
    end
  end.

Definition initial_state : ConcreteMState := {|
  reg_state := PMap.init CrNil;
  mem_state := @TabulaRasa CrVal;
|}.
