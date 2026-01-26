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

Definition uint_to_pos (u : uintptr) : positive :=
  Pos.of_nat ((Z.to_nat (unsigned u)) + 1).

(* check if a pointer's array is in memory *)
Definition find_array (mem : Memory) (base : uintptr) : option Array :=
  mem !! (uint_to_pos base).

(* load the value that a pointer points to *)
Definition ld_arr (a : Array) (offset : uintptr) : option uint8 :=
  let offset' := uint_to_pos offset in
  if (Pos.ltb offset' (Pos.of_nat (len a))) then
     (bytes a) !! offset'
  else
    None.
Definition ld_mem (mem : Memory) (base : uintptr) (offset : uintptr) : option uint8 :=
  match (find_array mem base) with
  | Some a => ld_arr a offset
  | None => None
  end.

(* store a value into a pointer *)
Definition st_arr (a : Array) (offset : uintptr) (v : uint8) : option Array :=
  let offset' := uint_to_pos offset in
  if (Pos.ltb offset' (Pos.of_nat (len a))) then
    Some {|
      base := base a;
      len := len a;
      bytes := PMap.set offset' (Some v) (bytes a)
    |}
  else
    None.
Definition st_mem' (mem : Memory) (base : uintptr) (offset : uintptr) (v : uint8) : option Memory :=
  match (find_array mem base) with
  | Some a => match (st_arr a offset v) with
    | Some a' => Some (PMap.set (uint_to_pos base) (Some a') mem)
    | None => None
    end
  | None => None
  end.
Definition st_mem (mem : Memory) (base : uintptr) (offset : uintptr) (v : uint8) : Memory :=
  match (st_mem' mem base offset v) with
  | Some mem' => mem'
  | None => mem
  end.

(* accessing a pointer is valid if...
  - there exists an associated array in memory
  - the pointer's access into that array is in-bounds *)
Definition mem_access_valid (mem: Memory) (base : uintptr) (offset : uintptr) : Prop :=
  let a := find_array mem base in
  let l := match a with
  | Some a' => (Pos.of_nat (len a'))
  | None => 1%positive
  end in
  (a <> None) /\ ((Pos.ltb (uint_to_pos offset) l) = true).

(* random lemma I felt like proving *)
Ltac isi := intros; split; intros.
Lemma valid_st_lemma:
  forall (mem : Memory) (base : uintptr) (offset : uintptr) (v : uint8),
  mem_access_valid mem base offset <->
  (st_mem' mem base offset v) <> None.
Proof.
  isi.
  - destruct H as [Ha Ho].
    unfold st_mem'.
    destruct (find_array mem base0); try (exfalso; congruence).
    unfold st_arr. rewrite Ho. discriminate.
  - unfold mem_access_valid.
    unfold st_mem' in H.
    destruct (find_array mem base0); try (exfalso; congruence).
    split; try discriminate.
    destruct (Pos.ltb (uint_to_pos offset) (Pos.of_nat (len a))) eqn:Hlt; try reflexivity.
    unfold st_arr in H.
    rewrite Hlt in H.
    exfalso. congruence.
Qed.

Lemma still_valid_lemma:
  forall (mem : Memory) (base : uintptr) (offset : uintptr) (v : uint8),
  mem_access_valid mem base offset <->
  mem_access_valid (st_mem mem base offset v) base offset.
Proof.
  isi; unfold mem_access_valid in *; destruct H as [Ha Ho].
  - split; unfold st_mem, st_mem';
    destruct (find_array mem base0); try congruence;
    unfold st_arr;
    rewrite Ho; unfold find_array;
    rewrite PMap.gss; try discriminate.
    simpl. assumption.
  - split.
    + unfold st_mem, st_mem' in *.
      destruct (find_array mem base0) eqn:Hp; try congruence.
    + unfold st_mem, st_mem' in *.
      destruct (find_array mem base0) eqn:Hp.
      * destruct (st_arr a offset v) eqn:Hst.
      -- destruct (find_array (PMap.set (uint_to_pos base0) (Some a0) mem) base0) eqn:Ha1.
      ++ unfold find_array in Ha1.
         rewrite PMap.gss in Ha1.
         injection Ha1 as Ha1.
         rewrite <- Ha1 in Ho.
         unfold st_arr in Hst.
         destruct ((uint_to_pos offset <? Pos.of_nat (len a))%positive); try reflexivity.
         exfalso. congruence.
      ++ exfalso. congruence.
      -- rewrite Hp in Ho. assumption.
      * rewrite Hp in Ho. assumption.
Qed.

(* read after write lemmas *)
Lemma raw_same_address:
  forall (mem : Memory) (base : uintptr) (offset : uintptr) (v : uint8),
  mem_access_valid mem base offset <->
  ld_mem (st_mem mem base offset v) base offset = Some v.
Proof with try congruence.
  intros; split; intros.
  - assert (mem_access_valid (st_mem mem base0 offset v) base0 offset). {
      apply still_valid_lemma. assumption.
    }
    destruct H as [Ha Ho].
    destruct H0 as [Ha' Ho'].
    destruct (find_array mem base0) eqn:Hp...
    destruct (find_array (st_mem mem base0 offset v) base0) eqn:Hp'...
    unfold ld_mem.
    destruct (find_array (st_mem mem base0 offset v) base0) eqn:Hp''...
    unfold ld_arr.
    injection Hp' as Hp'. rewrite Hp'.
    destruct ((uint_to_pos offset <? Pos.of_nat (len a0))%positive)...
    rewrite Hp' in Hp''.
    unfold find_array in Hp''.
    unfold st_mem, st_mem' in Hp''.
    rewrite Hp in Hp''.
    unfold st_arr in Hp''.
    rewrite Ho in Hp''.
    rewrite PMap.gss in Hp''.
    injection Hp'' as Hp''.
    rewrite <- Hp''. simpl.
    rewrite PMap.gss. reflexivity.
  - unfold mem_access_valid. split.
    + unfold ld_mem in H.
      destruct (find_array mem base0) eqn:Hp...
      unfold st_mem, st_mem' in H.
      repeat rewrite Hp in H.
      exfalso. congruence.
    + unfold ld_mem, ld_arr in H.
      unfold st_mem, st_mem', st_arr in H.
      destruct (find_array mem base0) eqn:Hp.
      * destruct ((uint_to_pos offset <? Pos.of_nat (len a))%positive) eqn:Ho...
        rewrite Hp in H.
        rewrite Ho in H.
        exfalso. congruence.
      * rewrite Hp in H. exfalso. congruence.
Qed.
Lemma raw_different_address:
  forall (mem : Memory) (b1 b2 : uintptr) (o1 o2 : uintptr) (v : uint8),
  (o1 <> o2 \/ b1 <> b2) ->
  ld_mem mem b1 o1 = ld_mem (st_mem mem b2 o2 v) b1 o1.
Proof with try congruence; try discriminate; try reflexivity.
  intros.
  unfold st_mem, st_mem'.
  destruct (find_array mem b2) eqn:Hp2...
  destruct (st_arr a o2 v) eqn:Ha2'...
  unfold ld_mem, find_array.
  destruct H.
  - unfold st_arr in Ha2'.
    destruct (Pos.ltb (uint_to_pos o2) (Pos.of_nat (len a))) eqn:Hltb...
    injection Ha2' as Ha2'.
    destruct (Pos.eq_dec (uint_to_pos b1) (uint_to_pos b2)) as [Hbeq | Hbneq].
    + repeat rewrite Hbeq. rewrite PMap.gss.
      unfold find_array in Hp2.
      rewrite Hp2.
      unfold ld_arr.
      rewrite <- Ha2'; simpl.
      rewrite PMap.gso...
      unfold uint_to_pos.
      admit.
      (* intro Heq.
      apply Nat2Pos.inj in Heq.
      * unfold Z.to_nat in Heq.
        destruct  *)
    + rewrite PMap.gso...
  - rewrite PMap.gso...
    admit.
Admitted.

(* Toy Grammar *)
(* Values *)
From MyProject Require Import CrVal.
Inductive RegArg : Type :=
| Reg (x : positive).
Definition reg' (r : RegArg) : positive :=
  match r with
  | Reg x => x
  end.

(* Operators *)
Inductive Op : Type :=
  (*  *)
  (* creates an array in memory *)
| Alloc (base nbyte : nat)
  (* dst_reg = v *)
| SetVal (dst_reg : RegArg) (v : CrVal)
  (* dst_reg = src_reg *)
| SetReg (dst_reg src_reg : RegArg)
  (* dst_reg = *src_reg *)
| LdReg (dst_reg src_reg : RegArg)
  (* *dst_reg = v *)
| StVal (dst_reg : RegArg) (v : CrVal)
  (* *dst_reg = src_reg *)
| StReg (dst_reg src_reg : RegArg)
  (* *dst_reg = *src_reg *)
| IStReg (dst_reg src_reg : RegArg)
  (* dst_reg = src_reg + v *)
| AddVal (dst_reg src_reg : RegArg) (v : CrVal)
  (* dst_reg = src_reg1 + src_reg2 *)
| AddReg (dst_reg src_reg1 src_reg2 : RegArg).

Record MachineState := {
  reg_state : PMap.t CrVal;
  mem_state : Memory;
}.

Definition Interp : Type :=
  MachineState -> MachineState.
Definition Program : Type :=
  list Op.

Definition get_reg (m : MachineState) (r : RegArg) : CrVal :=
  (reg_state m) !! (reg' r).
Transparent get_reg.
Definition x_reg (m : MachineState) (r : RegArg) : CrVal :=
  match get_reg m r with
  | CrPtr b o =>
    match ld_mem (mem_state m) b o with
    | Some v => CrInt v
    | None => CrNil
    end
  | _ => CrNil
  end.
Transparent x_reg.
Definition alloc (base nbyte : nat) (m : MachineState) : MachineState := {|
  reg_state := reg_state m;
  mem_state := PMap.set (Pos.of_nat (base+1)) (Some {|
    base := base;
    len := nbyte;
    bytes := PMap.init None
  |}) (mem_state m);
|}.
Transparent alloc.
Definition set_val (dst_reg : RegArg) (v : CrVal) (m : MachineState) : MachineState := {|
  reg_state := PMap.set (reg' dst_reg) v (reg_state m);
  mem_state := mem_state m;
|}.
Transparent set_val.
Definition set_reg (dst_reg src_reg : RegArg) (m : MachineState) : MachineState := {|
  reg_state := PMap.set (reg' dst_reg) ((reg_state m) !! (reg' src_reg)) (reg_state m);
  mem_state := mem_state m;
|}.
Definition ld_reg (dst_reg src_reg : RegArg) (m : MachineState) : MachineState :=
  let ld_val := x_reg m src_reg in {|
  reg_state := PMap.set (reg' dst_reg) ld_val (reg_state m);
  mem_state := mem_state m;
|}.
Transparent ld_reg.
Definition st_val (dst_reg : RegArg) (v : CrVal) (m : MachineState) : MachineState :=
  match (reg_state m) !! (reg' dst_reg), v with
  | CrPtr b o, CrInt x => {|
      reg_state := reg_state m;
      mem_state := st_mem (mem_state m) b o x;
    |}
  | _, _ => m
  end.
Transparent st_val.
Definition st_reg (dst_reg src_reg : RegArg) (m : MachineState) : MachineState :=
  match (reg_state m) !! (reg' dst_reg), (reg_state m) !! (reg' src_reg) with
  | CrPtr b o, CrInt x => {|
      reg_state := reg_state m;
      mem_state := st_mem (mem_state m) b o x;
    |}
  | _, _ => m
  end.
Transparent st_reg.
Definition ist_reg (dst_reg src_reg : RegArg) (m : MachineState) : MachineState :=
  match (reg_state m) !! (reg' dst_reg), (reg_state m) !! (reg' src_reg) with
  | CrPtr b' o', CrPtr b o => match ld_mem (mem_state m) b o with
    | Some v => {|
        reg_state := reg_state m;
        mem_state := st_mem (mem_state m) b' o' v;
      |}
    | None => m
    end
  | _, _ => m
  end.
Transparent ist_reg.
Definition add_val (dst_reg src_reg : RegArg) (v : CrVal) (m : MachineState) : MachineState :=
  set_val dst_reg match (reg_state m) !! (reg' src_reg), v with
  | CrInt x, CrInt y => CrInt (Integers.add x y)
  | CrPtr x y, CrInt z =>
    let z' : uintptr := repr (intval z) in
    CrPtr x (Integers.add y z')
  | _, _ => CrNil
  end m.
Transparent add_val.
Definition add_reg (dst_reg src_reg1 src_reg2 : RegArg) (m : MachineState) : MachineState :=
  set_val dst_reg match (reg_state m) !! (reg' src_reg1), (reg_state m) !! (reg' src_reg2) with
  | CrInt x, CrInt y => CrInt (Integers.add x y)
  | CrPtr x y, CrInt z =>
    let z' : uintptr := repr (intval z) in
    CrPtr x (Integers.add y z')
  | _, _ => CrNil
  end m.
Transparent add_reg.

Definition apply_op (op : Op) (m : MachineState) : MachineState :=
  match op with
  | Alloc b n => alloc b n
  | SetVal d v => set_val d v
  | SetReg d s => set_reg d s
  | LdReg d s => ld_reg d s
  | StVal d v => st_val d v
  | StReg d s => st_reg d s
  | IStReg d s => ist_reg d s
  | AddVal d s v => add_val d s v
  | AddReg d s1 s2 => add_reg d s1 s2
  end m.

Fixpoint compile' (p : Program) (m : MachineState) : MachineState :=
  match p with
  | [] => m
  | x :: xs => compile' xs (apply_op x m)
  end.
Definition compile (p : Program) : Interp :=
  compile' p.

From MyProject Require Import SmtExpr.
Definition check_registers_and_memory (s1 s2 : MachineState)
  (reg_list : list RegArg) (mem_list : list (uintptr * uintptr)) : SmtBoolExpr :=
  SmtBoolNot (SmtBoolAnd
    (List.fold_right
      (fun r acc => SmtBoolAnd acc (SmtBoolEq
        (SmtConst (get_reg s1 r))
        (SmtConst (get_reg s2 r))))
      SmtTrue reg_list)
    (List.fold_right (fun p acc =>
      SmtBoolAnd acc (match p with
      | (base, offset) =>
        SmtBoolEq
          (match ld_mem (mem_state s1) base offset with
          | Some v => SmtConst (CrInt v)
          | None => SmtConst CrNil
          end)
          (match ld_mem (mem_state s2) base offset with
          | Some v => SmtConst (CrInt v)
          | None => SmtConst CrNil
          end)
      end))
      SmtTrue mem_list)
  ).

From MyProject Require Import SmtTypes.
From MyProject Require Import SmtQuery.
Definition eq_checker (s : MachineState)
  (p1 p2 : Program)
  (reg_list : list RegArg) (mem_list : list (uintptr * uintptr)) : SmtResult :=
  let s1 := compile p1 s in
  let s2 := compile p2 s in
  smt_query (check_registers_and_memory s1 s2 reg_list mem_list).

Record ProgramOutput := {
  out_reg : list RegArg;
  out_mem : list Ptr;
}.

Definition get_output (p : Program) (o : ProgramOutput) (m : MachineState) : list Value * list Value :=
  let m' := (compile p) m in
  (* for each number in (out_reg o), map get_reg onto m' *)
  let reg_vals := List.map (fun r => (reg_state m') !! (reg' r)) (out_reg o) in
  let mem_vals := List.map (fun p =>
    match ld_mem (mem_state m') p with
    | Some v => VInt v
    | None => VNil
    end
  ) (out_mem o) in
  (reg_vals, mem_vals).

Definition programs_eq (p1 p2 : Program) (out : ProgramOutput) :=
  forall (m : MachineState),
  get_output p1 out m = get_output p2 out m.

Definition TabulaRasa : MachineState := {|
  reg_state := PMap.init VNil;
  mem_state := PMap.init None
|}.

Definition mx : MachineState := {|
  reg_state := PMap.set 1 (VPtr (Address 0 0)) (PMap.init VNil);
  mem_state := PMap.set (Pos.of_nat 1) (Some {|
    base := 0;
    len := 1024;
    bytes := PMap.set 1 (Some (repr 10)) (PMap.init None)
  |}) (PMap.init None)
|}.

Definition p1_v1 : Program := [
  LdReg  (Reg 3) (Reg 1); (* r3 = *r1 *)
  SetVal (Reg 6) (VInt (repr 10)); (* r6 = 10 *)
  SetReg (Reg 7) (Reg 1); (* r7 = r1 *)
  StReg  (Reg 7) (Reg 6); (* *r7 = r6 *)
  SetReg (Reg 5) (Reg 1); (* r5 = r1 *)
  LdReg  (Reg 4) (Reg 5); (* r4 = *r5 *)
  AddReg (Reg 2) (Reg 3) (Reg 4) (* r2 = r3 + r4 *)
].
Definition p1_v2 : Program := [
  LdReg  (Reg 2) (Reg 1); (* r2 = *r1 *)
  AddVal (Reg 2) (Reg 2) (VInt (repr 10)) (* r2 = r2 + 10 *)
].
Definition p1_out : ProgramOutput := {|
  out_reg := [Reg 2; Reg 17];
  out_mem := [(Address 100 100)]
|}.

Definition check_registers_and_memory (s1 s2 : MachineState)
  (out_list : ProgramOutput)

Compute (get_output p1_v1 p1_out mx).
Compute get_output p1_v2 p1_out mx.

(* memory operators don't change register state *)
Lemma alloc_is_regnop : forall base nbyte m,
  reg_state (alloc base nbyte m) = reg_state m.
Proof. intros. reflexivity. Qed.
Lemma st_val_is_regnop : forall dst v m,
  reg_state (st_val dst v m) = reg_state m.
Proof. intros. unfold st_val. destruct ((reg_state m) !! (reg' dst)), v; reflexivity. Qed.
Lemma st_reg_is_regnop : forall dst src m,
  reg_state (st_reg dst src m) = reg_state m.
Proof. intros. unfold st_reg. destruct ((reg_state m) !! (reg' dst)), ((reg_state m) !! (reg' src)); reflexivity. Qed.
Lemma ist_reg_is_regnop : forall dst src m,
  reg_state (ist_reg dst src m) = reg_state m.
Proof. intros. unfold ist_reg. destruct ((reg_state m) !! (reg' dst)), ((reg_state m) !! (reg' src)); try reflexivity. destruct (ld_mem (mem_state m) p0); reflexivity. Qed.

(* register operators don't change memory state *)
Lemma set_val_is_memnop : forall dst v m,
  mem_state (set_val dst v m) = mem_state m.
Proof. intros. reflexivity. Qed.
Lemma set_reg_is_memnop : forall dst src m,
  mem_state (set_reg dst src m) = mem_state m.
Proof. intros. reflexivity. Qed.
Lemma ld_reg_is_memnop : forall dst src m,
  mem_state (ld_reg dst src m) = mem_state m.
Proof. intros. reflexivity. Qed.
Lemma add_val_is_memnop : forall dst src v m,
  mem_state (add_val dst src v m) = mem_state m.
Proof. intros. reflexivity. Qed.
Lemma add_reg_is_memnop : forall dst src1 src2 m,
  mem_state (add_reg dst src1 src2 m) = mem_state m.
Proof. intros. reflexivity. Qed.

(* register operators don't affect other registers *)
Lemma set_val_diff : forall r1 r2 v m,
  r1 <> reg' r2 -> (reg_state (set_val r2 v m)) !! r1 = (reg_state m) !! r1.
Proof. intros. simpl. rewrite PMap.gso; try reflexivity. assumption. Qed.
Lemma set_reg_diff : forall r1 r2 src m,
  r1 <> reg' r2 -> (reg_state (set_reg r2 src m)) !! r1 = (reg_state m) !! r1.
Proof. intros. simpl. rewrite PMap.gso; try reflexivity. assumption. Qed.
Lemma ld_reg_diff : forall r1 r2 src m,
  r1 <> reg' r2 -> (reg_state (ld_reg r2 src m)) !! r1 = (reg_state m) !! r1.
Proof. intros. simpl. rewrite PMap.gso; try reflexivity. assumption. Qed.
Lemma add_val_diff : forall r1 r2 src v m,
  r1 <> reg' r2 -> (reg_state (add_val r2 src v m)) !! r1 = (reg_state m) !! r1.
Proof. intros. unfold add_val. apply set_val_diff. assumption. Qed.
Lemma add_reg_diff : forall r1 r2 src1 src2 m,
  r1 <> reg' r2 -> (reg_state (add_reg r2 src1 src2 m)) !! r1 = (reg_state m) !! r1.
Proof. intros. unfold add_reg. apply set_val_diff. assumption. Qed.

(* apply register operator *)
Lemma ld_reg_same : forall r src m,
  (reg_state (ld_reg (Reg r) src m)) !! r = x_reg m src.
Proof.
  intros. simpl. rewrite PMap.gss. reflexivity.
Qed.
