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
| IOArg (vid : positive)
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
| array_t
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

Inductive map_select :=
| select_io
| select_tmp
| select_iarr
| select_varr.

Definition get_from {T : Type} (m : machine_state T) (sel : map_select) (k : positive) : ValType * T :=
  match sel with
  | select_io => (io_map m) !! k
  | select_tmp => (tmp_map m) !! k
  | select_iarr => (iarr_map m) !! k
  | select_varr => (varr_map m) !! k
  end.
Definition set_to {T : Type} (m : machine_state T) (sel : map_select) (k : positive) (v : ValType * T) : machine_state T :=
  match sel with
  | select_io => set_io m k v
  | select_tmp => set_tmp m k v
  | select_iarr => set_iarr m k v
  | select_varr => set_varr m k v
  end.

Inductive arith_expr :=
| Z3_u8 (x : uint8)
| Z3_u32 (x : uint32)
| Z3_u8_var (name : positive)
| Z3_u32_var (name : positive)
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
| Z3Array (e : arr_expr)
| Z3Nil.
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
    apply_io_helper (PMap.set k (uint8_t, Z3Arith (Z3_u8_var k)) io) rest
  | (k, uint32_t) :: rest =>
    apply_io_helper (PMap.set k (uint32_t, Z3Arith (Z3_u32_var k)) io) rest
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
    apply_varr_helper (PMap.set k (array_t, Z3Array (Z3_arr_var k)) varr) rest
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
  | IOArg x => (io_map m) !! x
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
      (* m' = updated state with new array *)
      let m' : sym_state :=
      match local_lookup a2 with
      | (uint32_t, Z3Arith e2) =>
        (* a2 is a valid length *)
        match local_lookup a1 with
        | (uintptr_t, Z3Ptr (Z3_ptr_lit x)) =>
          (set_iarr m (uptr_to_key x) (array_t, Z3Array (Z3_arr_init e2)))
        | (uintptr_t, Z3Ptr (Z3_ptr_var x)) =>
          (set_varr m x (array_t, Z3Array (Z3_arr_init e2)))
        | _ => set_flag m true
        end
      | _ => set_flag m true
      end in
      match dst with
      | IOArg x => set_io m' x (local_lookup a1)
      | TmpArg x => set_tmp m' x (local_lookup a1)
      | _ => set_flag m' true
      end

    | LdOp dst a1 a2 =>
      let ld_val := match local_lookup a2 with
      | (uint32_t, Z3Arith e2) =>
        (* a2 is a valid index *)
        let arr_a1 := match local_lookup a1 with
        | (uintptr_t, Z3Ptr (Z3_ptr_lit x)) =>
          (iarr_map m) !! (uptr_to_key x)
        | (uintptr_t, Z3Ptr (Z3_ptr_var x)) =>
          (varr_map m) !! x
        | _ => (err_t, Z3Nil)
        end in
        match arr_a1 with
        | (array_t, Z3Array A) =>
          (uint8_t, Z3Arith (Z3_arr_ld A e2))
        | _ => (err_t, Z3Nil)
        end
      | _ => (err_t, Z3Nil)
      end in
      match ld_val, dst with
      | (uint8_t, e3), IOArg x =>
        set_io m x (uint8_t, e3)
      | (uint8_t, e3), TmpArg x =>
        set_tmp m x (uint8_t, e3)
      | _, _ => set_flag m true
      end


    | StOp a1 a2 a3 =>
      let arr_a1 :=
      match local_lookup a1 with
      | (uintptr_t, Z3Ptr (Z3_ptr_lit x)) =>
        (array_t, (iarr_map m) !! (uptr_to_key x), set_iarr m (uptr_to_key x))
      | (uintptr_t, Z3Ptr (Z3_ptr_var x)) =>
        (array_t, (varr_map m) !! x, set_varr m x)
      | (_, _) =>
        (err_t, (err_t, Z3Arith (Z3_u8 (repr 0))), fun _ => m)
      end in
      match arr_a1, local_lookup a2, local_lookup a3 with
      | (array_t, (array_t, Z3Array prev), setter), (uint32_t, Z3Arith e2), (uint8_t, Z3Arith e3) =>
        setter (array_t, Z3Array (Z3_arr_st prev e2 e3))
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
      | _, IOArg x => set_io m x new_val
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

Record output_space := {
  var_list : list positive;
  iptr_list : list (uintptr * uint32);
  vptr_list : list (positive * uint32);
}.
Record PrintOut {T : Type} : Type := {
  errored : bool;
  out_vars : list (TypedExpr T);
  out_iptr : list (TypedExpr T);
  out_vptr : list (TypedExpr T);
}.
Arguments PrintOut T : clear implicits.

Definition get_output (p : MemProgram) (out : output_space) : PrintOut Z3Expr :=
  let m := compile_sym p in
  {|
    errored := flag m;
    out_vars :=
      List.map (fun k => match (io_map m) !! k with
      | (nil_t, _) => (nil_t, Z3Nil)
      | (err_t, _) => (err_t, Z3Nil)
      | (t, e) => (t, e)
      end) (var_list out);
    out_iptr :=
      List.map (fun k => match k with
      | (b, i) => match (iarr_map m) !! (uptr_to_key b) with
        | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_ld e (Z3_u32 i)))
        | _ => (err_t, Z3Nil)
        end
      end) (iptr_list out);
    out_vptr :=
      List.map (fun k => match k with
      | (k', i) => match (varr_map m) !! k' with
        | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_ld e (Z3_u32 i)))
        | _ => (err_t, Z3Nil)
      end
      end) (vptr_list out)
  |}.

Definition z3_s_val : Type := positive -> CrVal.
Definition z3_a_val : Type := positive -> @Array CrVal.

Definition eval_z3_ptr (e : ptr_expr) (sval : z3_s_val) : CrVal :=
  match e with
  | Z3_ptr_lit x => PtrVal (CrPtr x)
  | Z3_ptr_var name => sval name
  end.
Fixpoint eval_z3_arith (e : arith_expr) (sval : z3_s_val) (aval : z3_a_val) : CrVal :=
  match e with
  | Z3_u8 x => IntVal (CrUInt8 x)
  | Z3_u32 x => IntVal (CrUInt32 x)
  | Z3_u8_var name
  | Z3_u32_var name => sval name
  | Z3_bitadd e1 e2 =>
    let v1 := eval_z3_arith e1 sval aval in
    let v2 := eval_z3_arith e2 sval aval in
    match v1, v2 with
    | IntVal (CrUInt8 x1), IntVal (CrUInt8 x2) =>
      IntVal (CrUInt8 (Integers.add x1 x2))
    | IntVal (CrUInt32 x1), IntVal (CrUInt32 x2) =>
      IntVal (CrUInt32 (Integers.add x1 x2))
    | _, _ => ErrorVal
    end
  | Z3_arr_ld e1 e2 =>
    let res := CrVal.ld_arr (eval_z3_array e1 sval aval) (eval_z3_arith e2 sval aval) in
    match res with
    | Legal v => v
    | Illegal => ErrorVal
    end
  end
with eval_z3_array (e : arr_expr) (sval : z3_s_val) (aval : z3_a_val) : Array :=
  match e with
  | Z3_arr_init e1 =>
    match eval_z3_arith e1 sval aval with
    | IntVal (CrUInt32 len) =>
      Allocated {|
        arr_len := len;
        arr_bytes := PMap.init Uninit
      |}
    | _ => Unallocated
    end
  | Z3_arr_var name => aval name
  | Z3_arr_st A idx item =>
    let arr := eval_z3_array A sval aval in
    let i := eval_z3_arith idx sval aval in
    let v := eval_z3_arith item sval aval in
    match CrVal.st_arr arr i v with
    | Legal a' => a'
    | Illegal => Unallocated
    end
  end.
Definition eval_z3_expr (e : Z3Expr) (sval : z3_s_val) (aval : z3_a_val) : CrVal :=
  match e with
  | Z3Arith e' =>
    eval_z3_arith e' sval aval
  | Z3Ptr e' =>
    eval_z3_ptr e' sval
  | _ => ErrorVal
  end.

Inductive Z3Bool :=
| Z3_T
| Z3_F
| Z3_Neg (e : Z3Bool)
| Z3_Conj (e1 e2 : Z3Bool)
| Z3_Disj (e1 e2 : Z3Bool)
| Z3_Eq (e1 e2 : Z3Expr).

Definition out_cmp (p1 p2 : MemProgram) (out : output_space) : Z3Bool :=
  let o1 := get_output p1 out in
  let o2 := get_output p2 out in
  match o1, o2 with
  | {| errored := e1; out_vars := v1; out_iptr := ip1; out_vptr := vp1 |},
    {| errored := e2; out_vars := v2; out_iptr := ip2; out_vptr := vp2 |} =>
      let e_expr : Z3Bool := if
        (orb (andb e1 e2)
             (andb (negb e1) (negb e2)))
      then Z3_T else Z3_F in
      let v_expr : Z3Bool := fold_right Z3_Conj Z3_T
        (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine v1 v2)) in
      let ip_expr := fold_right Z3_Conj Z3_T
        (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine ip1 ip2)) in
      let vp_expr := fold_right Z3_Conj Z3_T
        (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine vp1 vp2)) in
      Z3_Conj e_expr (
      Z3_Conj v_expr (
      Z3_Conj ip_expr
              vp_expr))
  end.

Fixpoint eval_z3_bool (e : Z3Bool) (sval : z3_s_val) (aval : z3_a_val) : bool :=
  match e with
  | Z3_T => true
  | Z3_F => false
  | Z3_Neg e' => negb (eval_z3_bool e' sval aval)
  | Z3_Conj e1 e2 => andb (eval_z3_bool e1 sval aval) (eval_z3_bool e2 sval aval)
  | Z3_Disj e1 e2 => orb (eval_z3_bool e1 sval aval) (eval_z3_bool e2 sval aval)
  | Z3_Eq e1 e2 =>
    let v1 := eval_z3_expr e1 sval aval in
    let v2 := eval_z3_expr e2 sval aval in
    CrVal.eqb v1 v2
  end.

Definition rdi : positive := 1.
Definition rsi : positive := 2.
Definition rdx : positive := 3.
Definition rcx : positive := 4.
Definition rax : positive := 5.

Definition test0 : MemProgram := ([
  (rdi, uint8_t)
], [
  AllocOp (TmpArg 1)
    (ValArg (imm_ptr (repr 0xffff)))
    (ValArg (imm_u32 (repr 128)));
  StOp (TmpArg 1)
    (ValArg (imm_u32 (repr 0)))
    (ValArg (imm_u8 (repr 67)));
  LdOp (IOArg rax) (TmpArg 1) (ValArg (imm_u32 (repr 0)))
]).
Compute get_output test0 {|
  var_list := [rdi; rax];
  iptr_list := [];
  vptr_list := [];
|}.

Definition test1 : MemProgram := ([
  (rdi, uintptr_t)
], [
  LdOp (IOArg rax)
    (IOArg rdi)
    (ValArg (imm_u32 (repr 0)));
  StOp (IOArg rdi)
    (ValArg (imm_u32 (repr 0)))
    (ValArg (imm_u8 (repr 67)));
  LdOp (IOArg rsi)
    (IOArg rdi)
    (ValArg (imm_u32 (repr 0)))
]).
Compute get_output test1 {|
  var_list := [rax; rsi]%positive;
  iptr_list := [];
  vptr_list := [(rdi, (repr 0))];
|}.

Definition p1 : MemProgram := ([
  (rdi, uintptr_t);
  (rsi, uint8_t);
  (rdx, uint8_t)
], [
  (* f(a, b, c) {
   *   x = alloc(0x400, 16);
   *   x[4] = b + c;
   *   *a = x[4];
   * } *)
  AllocOp (TmpArg 1)
    (ValArg (imm_ptr (repr 0x400)))
    (ValArg (imm_u32 (repr 16)));
  AddOp (TmpArg 2)
    (IOArg rsi)
    (IOArg rdx);
  StOp (TmpArg 1)
    (ValArg (imm_u32 (repr 4)))
    (TmpArg 2);
  LdOp (TmpArg 3)
    (TmpArg 1)
    (ValArg (imm_u32 (repr 4)));
  StOp (IOArg rdi)
    (ValArg (imm_u32 (repr 0)))
    (TmpArg 3)
]).

Definition p2 : MemProgram := ([
  (1%positive, uintptr_t);
  (2%positive, uint8_t);
  (3%positive, uint8_t)
], [
  AllocOp (TmpArg 1)
    (ValArg (imm_ptr (repr 0x400)))
    (ValArg (imm_u32 (repr 16)));
  AddOp (TmpArg 2)
    (IOArg rsi)
    (IOArg rdx);
  StOp (IOArg rdi)
    (ValArg (imm_u32 (repr 0)))
    (TmpArg 2)
]).

Definition p1_out := get_output p1 {|
  var_list := [];
  iptr_list := [];
  vptr_list := [(rdi, (repr 0))];
|}.
Definition p2_out := get_output p2 {|
  var_list := [];
  iptr_list := [];
  vptr_list := [(rdi, (repr 0))];
|}.

Definition exp : MemProgram := ([
  (1%positive, uint8_t)
], [
  AddOp (TmpArg 1)
    (ValArg (imm_u8 (repr 1)))
    (ValArg (imm_u8 (repr 1)));
  AddOp (IOArg 1)
    (ValArg (imm_u8 (repr 1)))
    (ValArg (imm_u8 (repr 1)));
  AddOp (IOArg 2)
    (TmpArg 1)
    (TmpArg 1);
  AddOp (IOArg 3)
    (IOArg 1)
    (IOArg 1)
]).
Definition exp_out := get_output exp {|
  var_list := [2%positive; 3%positive];
  iptr_list := [];
  vptr_list := [];
|}.
Compute exp_out.

Definition ex_expr := match out_vptr p2_out with
| [] => (nil_t, Z3Nil)
| x :: xs => x
end.
Compute ex_expr.


Definition query_expression (p1 p2 : MemProgram) (o : output_space) : Z3Bool :=
  let cmp := out_cmp p1 p2 o in
  Z3_Neg cmp.

Inductive Z3Res :=
| Z3Sat (s : z3_s_val) (a : z3_a_val)
| Z3Unsat
| Z3Unknown.
Parameter z3_query : Z3Bool -> Z3Res.

Axiom z3_sound_some:
  forall e sval aval,
    z3_query e = Z3Sat sval aval ->
    eval_z3_bool e sval aval = true.
Axiom z3_sound_none:
  forall e,
    z3_query e = Z3Unsat ->
    forall sval aval,
    eval_z3_bool e sval aval = false.

(* Lemma mem_prog_soundness:
  forall
    (p1 p2 : MemProgram) (out : output_space)
    (out_vars : list positive)
    (out_iptr : list (uintptr * uint32))
    (out_vptr : list (positive * uint32)),
  z3_query (query_expression p1 p2 out) = Z3Unsat -> *)
