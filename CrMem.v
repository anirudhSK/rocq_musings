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

Inductive ValType : Type :=
| uint8_t
| uint32_t
| uintptr_t
| array_t
| nil_t
| err_t.

Definition var_id := positive.
Inductive Imm : Type :=
| imm_u8 (v : uint8)
| imm_u32 (v : uint32)
| imm_ptr (b : uintptr).
Inductive FnArg : Type :=
| IOArg (vid : var_id)
| TmpArg (tid : var_id)
| ValArg (v : Imm).
Inductive Instruction : Type :=
| AllocOp (dst a1 a2 : FnArg)
| LdOp (dst a1 a2 : FnArg)
| StOp (a1 a2 a3 : FnArg)
| AddOp (dst a1 a2 : FnArg).

Record MemProgram := {
  fn_in : list (var_id * ValType);
  fn_body : list Instruction;
  fn_out_vars : list var_id;
  fn_out_iaddrs : list (uintptr * uint32);
  fn_out_vaddrs : list (var_id * uint32);
}.

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
Definition init_sym : sym_state := {|
  io_map := PMap.init (nil_t, Z3Nil);
  tmp_map := PMap.init (nil_t, Z3Nil);
  iarr_map := PMap.init (nil_t, Z3Nil);
  varr_map := PMap.init (nil_t, Z3Nil);
  flag := false;
|}.

Fixpoint apply_io_helper (io : PMap.t (TypedExpr Z3Expr)) (input : list (positive * ValType)) : PMap.t (TypedExpr Z3Expr) :=
  match input with
  | [] => io
  | (k, uint8_t) :: rest =>
    apply_io_helper (PMap.set k (uint8_t, Z3Arith (Z3_u8_var k)) io) rest
  | (k, uint32_t) :: rest =>
    apply_io_helper (PMap.set k (uint32_t, Z3Arith (Z3_u32_var k)) io) rest
  | (k, uintptr_t) :: rest =>
    apply_io_helper (PMap.set k (uintptr_t, Z3Ptr (Z3_ptr_var k)) io) rest
  | (k, _) :: rest => apply_io_helper (PMap.set k (err_t, Z3Nil) io) rest
  end.
Fixpoint apply_varr_helper (varr : PMap.t (TypedExpr Z3Expr)) (input : list (positive * ValType)) : PMap.t (TypedExpr Z3Expr) :=
  match input with
  | [] => varr
  | (k, uintptr_t) :: rest =>
    apply_varr_helper (PMap.set k (array_t, Z3Array (Z3_arr_var k)) varr) rest
  | _ :: rest => apply_varr_helper varr rest
  end.
Definition apply_input (m : sym_state) (iv : list (positive * ValType)) : sym_state := {|
  io_map := apply_io_helper (io_map init_sym) iv;
  tmp_map := tmp_map init_sym;
  iarr_map := iarr_map init_sym;
  varr_map := apply_varr_helper (varr_map init_sym) iv;
  flag := flag init_sym;
|}.

Definition sym_interp_arg (m : sym_state) (a : FnArg) : TypedExpr Z3Expr :=
  match a with
  | IOArg x => (io_map m) !! x
  | TmpArg x => (tmp_map m) !! x
  | ValArg x =>
    match x with
    | imm_u8 x' => (uint8_t, Z3Arith (Z3_u8 x'))
    | imm_u32 x' => (uint32_t, Z3Arith (Z3_u32 x'))
    | imm_ptr x' => (uintptr_t, Z3Ptr (Z3_ptr_lit x'))
    end
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
      (* TODO: handle case where a1 is a ValArg imm_ptr *)
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
      let new_val : TypedExpr Z3Expr :=
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

Record output_valuation {T : Type} : Type := {
  errored : HasError;
  var_val : var_id -> TypedExpr T;
  iptr_val : (uintptr * uint32) -> TypedExpr T;
  vptr_val : (var_id * uint32) -> TypedExpr T;
}.
Arguments output_valuation T : clear implicits.

Fixpoint compile_sym_helper (p : list Instruction) (m : sym_state) : sym_state :=
  match p with
  | [] => m
  | i :: rest =>
    let m' := apply_sym_op i m in
    compile_sym_helper rest m'
  end.

Definition compile_sym (p : MemProgram) : output_valuation Z3Expr :=
  let m' := compile_sym_helper (fn_body p) (apply_input init_sym (fn_in p)) in {|
    errored := flag m';
    var_val := fun k => match (io_map m') !! k with
      | (nil_t, _) => (nil_t, Z3Nil)
      | (err_t, _) => (err_t, Z3Nil)
      | (t, e) => (t, e)
      end;
    iptr_val := fun '(b, i) => match (iarr_map m') !! (uptr_to_key b) with
      | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_ld e (Z3_u32 i)))
      | _ => (err_t, Z3Nil)
      end;
    vptr_val := fun '(k, i) => match (varr_map m') !! k with
      | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_ld e (Z3_u32 i)))
      | _ => (err_t, Z3Nil)
      end
  |}.

Definition z3_s_val : Type := var_id -> CrVal.
Definition z3_a_val : Type := var_id -> @Array CrVal.

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

Definition query_expression (p1 p2 : MemProgram) : Z3Bool :=
  let val1 := compile_sym p1 in
  let val2 := compile_sym p2 in

  let o1 := (errored val1,
             List.map (var_val val1) (fn_out_vars p1),
             List.map (iptr_val val1) (fn_out_iaddrs p1),
             List.map (vptr_val val1) (fn_out_vaddrs p1)) in
  let o2 := (errored val2,
             List.map (var_val val2) (fn_out_vars p2),
             List.map (iptr_val val2) (fn_out_iaddrs p2),
             List.map (vptr_val val2) (fn_out_vaddrs p2)) in
  match o1, o2 with
  | (e1, v1, ip1, vp1),
    (e2, v2, ip2, vp2)  =>
    let e_expr : Z3Bool :=
      if (orb (andb e1 e2) (andb (negb e1) (negb e2)))
      then Z3_T
      else Z3_F in
    let v_expr : Z3Bool := fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine v1 v2)) in
    let ip_expr := fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine ip1 ip2)) in
    let vp_expr := fold_right Z3_Conj Z3_T
      (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine vp1 vp2)) in
    Z3_Neg (Z3_Conj e_expr (
            Z3_Conj v_expr (
            Z3_Conj ip_expr
                    vp_expr)))
  end.

Inductive Z3Res :=
| Z3Sat (s : z3_s_val) (a : z3_a_val)
| Z3Unsat
| Z3Unknown.
Parameter z3_query : Z3Bool -> Z3Res.

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

Axiom z3_sound_some:
  forall e sval aval,
    z3_query e = Z3Sat sval aval ->
    eval_z3_bool e sval aval = true.
Axiom z3_sound_none:
  forall e,
    z3_query e = Z3Unsat ->
    forall sval aval,
    eval_z3_bool e sval aval = false.
    
Lemma mem_prog_soundness:
  (* for all programs, p1 and p2 *)
  forall (p1 p2 : MemProgram),
  (* with identical IO *)
  (fn_in p1) = (fn_in p2) ->
  (fn_out_vars p1) = (fn_out_vars p2) ->
  (fn_out_iaddrs p1) = (fn_out_iaddrs p2) ->
  (fn_out_vaddrs p1) = (fn_out_vaddrs p2) ->
  (* if z3 returns unsat *)
  z3_query (query_expression p1 p2) = Z3Unsat ->
  (* then under every possible valuation *)
  forall (sval : z3_s_val) (aval : z3_a_val),
    let res1 := compile_sym p1 in
    let res2 := compile_sym p2 in
    (* they have the same error value *)
    (errored res1 = errored res2) /\
    (* they have the same output variable assignments *)
    (forall (v : var_id),
      In v (fn_out_vars p1) ->
      let '(_, x1) := (var_val res1) v in
      let '(_, x2) := (var_val res2) v in
      eval_z3_expr x1 sval aval = eval_z3_expr x2 sval aval
    ) /\
    (* they write to the same absolute addresses *)
    (forall (ia : uintptr) (ix1 : uint32),
      In (ia, ix1) (fn_out_iaddrs p1) ->
      let '(_, x1) := (iptr_val res1) (ia, ix1) in
      let '(_, x2) := (iptr_val res2) (ia, ix1) in
      eval_z3_expr x1 sval aval = eval_z3_expr x2 sval aval
    ) /\
    (* and they write to the same relative addresses *)
    (forall (va : var_id) (ix2 : uint32),
      In (va, ix2) (fn_out_vaddrs p1) ->
      let '(_, x1) := (vptr_val res1) (va, ix2) in
      let '(_, x2) := (vptr_val res2) (va, ix2) in
      eval_z3_expr x1 sval aval = eval_z3_expr x2 sval aval
    ).
Proof.
Admitted.
