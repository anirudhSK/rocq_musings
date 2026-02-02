Require Import ZArith.
From Coq.Strings Require Import String.
From Coq.Strings Require Import Ascii.
Require Import List.
Import ListNotations.
From MyProject Require Import CrVal.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.


Inductive Imm : Type :=
| imm_u8 (v : uint8)
| imm_u32 (v : uint32)
| imm_ptr (b : uintptr).
Inductive FnArg : Type :=
| VarArg (vid : positive)
| TmpArg (tid : positive)
| ValArg (v : Imm).

Inductive Instruction : Type :=
| AllocOp (dst a1 a2 : FnArg)
  (* dst cannot be val *)
| LdOp (dst a1 a2 : FnArg)
| StOp (a1 a2 a3 : FnArg)
| AddOp (dst a1 a2 : FnArg).

Inductive ValType : Type :=
| uint8_t
| uint32_t
| uintptr_t
| nil_t
| err_t.
Definition MemProgram : Type := (list (positive * ValType)) * (list Instruction).

Definition HasError : Type := bool.
Definition TypedExpr (T : Type) : Type := ValType * T.
Record machine_state {T : Type} := {
  io_map : PMap.t (TypedExpr T);
  tmp_map : PMap.t (TypedExpr T);
  iarr_map : PMap.t (TypedExpr T);
  varr_map : PMap.t (TypedExpr T);
  flag : HasError;
}.
Arguments machine_state T : clear implicits.

Definition set_io {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  io_map := PMap.set k v (io_map m);
  tmp_map := tmp_map m;
  iarr_map := iarr_map m;
  varr_map := varr_map m;
  flag := flag m;
|}.
Definition set_tmp {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  io_map := io_map m;
  tmp_map := PMap.set k v (tmp_map m);
  iarr_map := iarr_map m;
  varr_map := varr_map m;
  flag := flag m;
|}.
Definition set_iarr {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  io_map := io_map m;
  tmp_map := tmp_map m;
  iarr_map := PMap.set k v (iarr_map m);
  varr_map := varr_map m;
  flag := flag m;
|}.
Definition set_varr {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  io_map := io_map m;
  tmp_map := tmp_map m;
  iarr_map := iarr_map m;
  varr_map := PMap.set k v (varr_map m);
  flag := flag m;
|}.
Definition set_flag {T : Type} (m : machine_state T) (b : bool) := {|
  io_map := io_map m;
  tmp_map := tmp_map m;
  iarr_map := iarr_map m;
  varr_map := varr_map m;
  flag := b;
|}.

Record PrintOut (T : Type) : Type := {
  errored : bool;
  values : list (positive * (TypedExpr T))
}.

Inductive arith_expr :=
| Z3_u8 (x : uint8)
| Z3_u32 (x : uint32)
| Z3_arith_var (name : positive)
| Z3_bitadd (e1 e2 : arith_expr)
| Z3_arr_ld (e1 : arr_expr) (e2 : arith_expr)
with ptr_expr :=
| Z3_ptr_lit (x : uintptr)
| Z3_ptr_var (name : positive)
with arr_expr :=
| Z3_arr_init (len : arith_expr)
| Z3_arr_var (name : positive)
| Z3_arr_st (A : arr_expr) (idx : arith_expr) (item : arith_expr).
Inductive Z3Expr :=
| Z3Arith (e : arith_expr)
| Z3Ptr (e : ptr_expr)
| Z3Array (e : arr_expr).
Definition sym_state := machine_state Z3Expr.
Definition TypedZ3Expr := TypedExpr Z3Expr.
Definition init_sym : sym_state := {|
  io_map := PMap.init (nil_t, Z3Arith (Z3_u8 (repr 0)));
  tmp_map := PMap.init (nil_t, Z3Arith (Z3_u8 (repr 0)));
  iarr_map := PMap.init (nil_t, Z3Array (Z3_arr_init (Z3_u32 (repr 0))));
  varr_map := PMap.init (nil_t, Z3Array (Z3_arr_init (Z3_u32 (repr 0))));
  flag := false; (* TODO: don't hardcode *)
|}.

Fixpoint apply_io_helper (io : PMap.t TypedZ3Expr) (input : list (positive * ValType)) : PMap.t TypedZ3Expr :=
  match input with
  | [] => io
  | (k, uint8_t) :: rest =>
    apply_io_helper (PMap.set k (uint8_t, Z3Arith (Z3_arith_var k)) io) rest
  | (k, uint32_t) :: rest =>
    apply_io_helper (PMap.set k (uint32_t, Z3Arith (Z3_arith_var k)) io) rest
  | (k, uintptr_t) :: rest =>
    apply_io_helper (PMap.set k (uintptr_t, Z3Ptr (Z3_ptr_var k)) io) rest
  | (k, t) :: rest => match io !! k with
    | (_, v) => apply_io_helper (PMap.set k (t, v) io) rest
    end
  end.
Fixpoint apply_varr_helper (varr : PMap.t TypedZ3Expr) (input : list (positive * ValType)) : PMap.t TypedZ3Expr :=
  match input with
  | [] => varr
  | (k, uintptr_t) :: rest =>
    apply_varr_helper (PMap.set k (uintptr_t, Z3Array (Z3_arr_var k)) varr) rest
  | (k, t) :: rest => match varr !! k with
    | (_, v) => apply_varr_helper varr rest
    end
  end.
Definition apply_input (m : sym_state) (iv : list (positive * ValType)) : sym_state := {|
  io_map := apply_io_helper (io_map init_sym) iv;
  tmp_map := tmp_map init_sym;
  iarr_map := iarr_map init_sym;
  varr_map := apply_varr_helper (varr_map init_sym) iv;
  flag := flag init_sym;
|}.

Definition imm_to_z3 (x : Imm) : TypedZ3Expr :=
  match x with
  | imm_u8 x' => (uint8_t, Z3Arith (Z3_u8 x'))
  | imm_u32 x' => (uint32_t, Z3Arith (Z3_u32 x'))
  | imm_ptr x' => (uintptr_t, Z3Ptr (Z3_ptr_lit x'))
  end.
Definition sym_interp_arg (m : sym_state) (a : FnArg) : TypedZ3Expr :=
  match a with
  | VarArg x => (io_map m) !! x
  | TmpArg x => (tmp_map m) !! x
  | ValArg x => (imm_to_z3 x)
  end.

Definition uptr_to_key (p : uintptr) : positive :=
  Pos.of_nat (S (Z.to_nat (unsigned p))).

Definition apply_sym_op (i : Instruction) (m : sym_state) : sym_state :=
  let local_lookup := sym_interp_arg m in
  if (flag m) then
    m
  else
    match i with
    | AllocOp dst a1 a2 =>
      let p_m' :=
      match local_lookup a1, local_lookup a2 with
      | (uintptr_t, Z3Ptr (Z3_ptr_lit x)), (uint32_t, Z3Arith e2) =>
        (local_lookup a1, set_iarr m (uptr_to_key x) (uintptr_t, Z3Array (Z3_arr_init e2)))
      | (uintptr_t, Z3Ptr (Z3_ptr_var x)), (uint32_t, Z3Arith e2) =>
        (local_lookup a1, set_varr m x (uintptr_t, Z3Array (Z3_arr_init e2)))
      | _, _ => ((err_t, Z3Arith (Z3_u8 (repr 0))), m)
      end in
      match p_m', dst with
      | ((err_t, _), _), _ => set_flag m true
      | ((uintptr_t, e1), m'), VarArg x => set_io m' x (uintptr_t, e1)
      | ((uintptr_t, e1), m'), TmpArg x => set_tmp m' x (uintptr_t, e1)
      | _, _ => set_flag m true
      end


    | LdOp dst a1 a2 =>
      (* dst = a1[a2] *)
      let arr_a1 : TypedZ3Expr :=
      match local_lookup a1 with
      | (uintptr_t, Z3Ptr (Z3_ptr_lit x)) => (iarr_map m) !! (uptr_to_key x)
      | (uintptr_t, Z3Ptr (Z3_ptr_var x)) => (varr_map m) !! x
      | (_, _) => (err_t, Z3Array (Z3_arr_init (Z3_u32 (repr 0))))
      end in
      let ld_val : TypedZ3Expr :=
      match arr_a1, local_lookup a2 with
      | (uintptr_t, Z3Array A), (uint32_t, Z3Arith e2) =>
        (uint8_t, Z3Arith (Z3_arr_ld A e2))
      | _, _ => (err_t, Z3Arith (Z3_u8 (repr 0)))
      end in
      match ld_val, dst with
      | (err_t, _), _ => set_flag m true
      | (uint8_t, e3), VarArg x => set_io m x (uint8_t, e3)
      | (uint8_t, e3), TmpArg x => set_tmp m x (uint8_t, e3)
      | _, _ => set_flag m true
      end


    | StOp a1 a2 a3 =>
      let arr_a1 :=
      match local_lookup a1 with
      | (uintptr_t, Z3Ptr (Z3_ptr_lit x)) =>
        (uintptr_t, (iarr_map m) !! (uptr_to_key x), set_iarr m (uptr_to_key x))
      | (uintptr_t, Z3Ptr (Z3_ptr_var x)) =>
        (uintptr_t, (varr_map m) !! x, set_varr m x)
      | (_, _) =>
        (err_t, (err_t, Z3Arith (Z3_u8 (repr 0))), fun _ => m)
      end in
      match arr_a1, local_lookup a2, local_lookup a3 with
      | (uintptr_t, (uintptr_t, Z3Array prev), setter), (uint32_t, Z3Arith e2), (uint8_t, Z3Arith e3) =>
        setter (uintptr_t, Z3Array (Z3_arr_st prev e2 e3))
      | _, _, _ => set_flag m true
      end


    | AddOp dst a1 a2 =>
      let new_val : TypedZ3Expr :=
      match local_lookup a1, local_lookup a2 with
      | (uint8_t, Z3Arith e1), (uint8_t, Z3Arith e2) =>
        (uint8_t, Z3Arith (Z3_bitadd e1 e2))
      | (uint32_t, Z3Arith e1), (uint32_t, Z3Arith e2) =>
        (uint32_t, Z3Arith (Z3_bitadd e1 e2))
      | (_, e1), _ => (err_t, e1)
      end in
      match new_val, dst with
      | (err_t, _), _ => set_flag m true
      | _, VarArg x => set_io m x new_val
      | _, TmpArg x => set_tmp m x new_val
      | _, ValArg _ => set_flag m true
      end
    end.

Fixpoint compile_sym_helper (p : list Instruction) (m : sym_state) : sym_state :=
  match p with
  | [] => m
  | i :: rest =>
    let m' := apply_sym_op i m in
    compile_sym_helper rest m'
  end.

Definition compile_sym (p : MemProgram) : sym_state :=
  let '(inp, inst) := p in
  compile_sym_helper inst (apply_input init_sym inp).

Definition get_output (p : MemProgram) (out : list positive) : PrintOut Z3Expr :=
  let m := compile_sym p in {|
    errored := flag m;
    values := List.map (fun k => (k, (io_map m) !! k)) out
  |}.

Definition tdd0 : MemProgram := ([

], [
  AddOp (VarArg 1)
    (ValArg (imm_u8 (repr 6)))
    (ValArg (imm_u8 (repr 7)))
]).
Compute get_output tdd0 [1]%positive.

Definition tdd1 : MemProgram := ([
  (2%positive, uint32_t)
], [
  AddOp (VarArg 1)
    (VarArg 2)
    (ValArg (imm_u32 (repr 1)))
]).
Compute get_output tdd1 [1]%positive.

Definition tdd2 : MemProgram := ([
  (2%positive, uint8_t)
], [
  AddOp (TmpArg 1)
    (ValArg (imm_u8 (repr 16)))
    (VarArg 2);
  AddOp (VarArg 1)
    (TmpArg 1) (TmpArg 1)
]).
Compute get_output tdd2 [1]%positive.

Definition tdd3 : MemProgram := ([
  (2%positive, uintptr_t)
], [
  AllocOp (VarArg 1)
    (ValArg (imm_ptr (repr 0xffff)))
    (ValArg (imm_u32 (repr 128)));
  StOp (VarArg 1)
    (ValArg (imm_u32 (repr 0)))
    (ValArg (imm_u8 (repr 67)));
  LdOp (VarArg 3) (VarArg 1) (ValArg (imm_u32 (repr 0)))
]).
Compute get_output tdd3 [1; 2; 3]%positive.

Definition tdd4 : MemProgram := ([
  (1%positive, uintptr_t)
], [
  LdOp (VarArg 99)
    (VarArg 1)
    (ValArg (imm_u32 (repr 0)));
  StOp (VarArg 1)
    (ValArg (imm_u32 (repr 0)))
    (ValArg (imm_u8 (repr 67)));
  LdOp (VarArg 98)
    (VarArg 1)
    (ValArg (imm_u32 (repr 0)))
]).
Compute get_output tdd4 [99; 98]%positive.

Definition p1 : MemProgram := ([
  (1%positive, uintptr_t);
  (2%positive, uint8_t);
  (3%positive, uint8_t)
], [
  (* f(a, b, c) {
   *   x = alloc(0xffff, 8);
   *   x[4] = b + c;
   *   return a[0] + x[4];
   * } *)
  (* tmp_1 = alloc(0xffff, 8) *)
  AllocOp (TmpArg 1)
          (ValArg (imm_ptr (repr 0xffff)))
          (ValArg (imm_u32 (repr 8)));
  (* tmp_2 = b + c *)
  AddOp   (TmpArg 2)
          (VarArg 2)
          (VarArg 3);
  (* tmp_1[4] = tmp_2 *)
  StOp    (TmpArg 1)
          (ValArg (imm_u32 (repr 4)))
          (TmpArg 2);
  (* tmp_3 = a[0] *)
  LdOp    (TmpArg 3)
          (VarArg 1)
          (ValArg (imm_u32 (repr 0)));
  (* tmp_4 = tmp_1[4] *)
  LdOp    (TmpArg 4)
          (TmpArg 1)
          (ValArg (imm_u32 (repr 4)));
  (* rax = tmp_3 + tmp_4 *)
  AddOp   (VarArg 99)
          (TmpArg 3)
          (TmpArg 4)
]).

Definition p2 : MemProgram := ([
  (1%positive, uintptr_t);
  (2%positive, uint8_t);
  (3%positive, uint8_t)
], [
  (* f(a, b, c) {
   *   x = alloc(0xffff, 8);
   *   x[4] = b + c;
   *   return a[0] + x[2 + 2];
   * } *)
  AllocOp (TmpArg 1)
          (ValArg (imm_ptr (repr 0xffff)))
          (ValArg (imm_u32 (repr 8)));
  AddOp   (TmpArg 2)
          (VarArg 2)
          (VarArg 3);
  StOp    (TmpArg 1)
          (ValArg (imm_u32 (repr 4)))
          (TmpArg 2);
  LdOp    (TmpArg 3)
          (VarArg 1)
          (ValArg (imm_u32 (repr 0)));
  AddOp   (TmpArg 4)
          (ValArg (imm_u32 (repr 2)))
          (ValArg (imm_u32 (repr 2)));
  LdOp    (TmpArg 5)
          (TmpArg 1)
          (TmpArg 4);
  AddOp   (VarArg 99)
          (TmpArg 3)
          (TmpArg 5)
]).

Compute get_output p1 [99]%positive.
Compute get_output p2 [99]%positive.
