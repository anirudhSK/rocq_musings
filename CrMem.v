(* TODO: Add Comments *)

From Stdlib Require Import ZArith.
From Stdlib.Strings Require Import String.
From Stdlib.Strings Require Import Ascii.
From Stdlib Require Import List.
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
| imm_ptr (b : uintbptr).
Inductive FnArg : Type :=
| IOArg (vid : var_id)
| TmpArg (tid : var_id)
| ValArg (v : Imm).
Inductive ArithBinOp : Type :=
| AddOp
| SubOp
| ASLOp
| ASROp
| BitAndOp
| BitOrOp
| BitXorOp.
Inductive Instruction : Type :=
| AllocOp (dst a1 a2 : FnArg)
| LdOp (dst a1 a2 : FnArg)
| StOp (a1 a2 a3 : FnArg)
| Binary (op : ArithBinOp) (dst a1 a2 : FnArg)
| BitFlipOp (dst a1 : FnArg)
| BrzOp (cond : FnArg) (zero_br : list Instruction) (nonzero_br : list Instruction).
Record IM_Program := {
  fn_in : list (var_id * ValType);
  fn_body : list Instruction;
  fn_out_vars : list var_id;
  fn_out_iaddrs : list (uintbptr * uint32);
  fn_out_vaddrs : list (var_id * uint32);
}.

Definition HasError : Type := bool.
Definition TypedExpr (T : Type) : Type := ValType * T.
Record machine_state {T : Type} := {
  io_map : PMap.t (TypedExpr T);
  tmp_map : PMap.t (TypedExpr T);
  iarr_map : PMap.t (TypedExpr T);
  varr_map : PMap.t (TypedExpr T);
  bound_map : PMap.t (TypedExpr T);
  flag : HasError;
}.
Arguments machine_state T : clear implicits.
Definition set_io {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  io_map := PMap.set k v (io_map m);
  tmp_map := tmp_map m; iarr_map := iarr_map m; varr_map := varr_map m; bound_map := bound_map m; flag := flag m;
|}.
Definition set_tmp {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  tmp_map := PMap.set k v (tmp_map m);
  io_map := io_map m; iarr_map := iarr_map m; varr_map := varr_map m; bound_map := bound_map m; flag := flag m;
|}.
Definition set_iarr {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  iarr_map := PMap.set k v (iarr_map m);
  io_map := io_map m; tmp_map := tmp_map m; varr_map := varr_map m; bound_map := bound_map m; flag := flag m;
|}.
Definition set_varr {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  varr_map := PMap.set k v (varr_map m);
  io_map := io_map m; tmp_map := tmp_map m; iarr_map := iarr_map m; bound_map := bound_map m; flag := flag m;
|}.
Definition set_bound {T : Type} (m : machine_state T) (k : positive) (v : ValType * T) := {|
  bound_map := PMap.set k v (bound_map m);
  io_map := io_map m; tmp_map := tmp_map m; iarr_map := iarr_map m; varr_map := varr_map m; flag := flag m;
|}.
Definition set_flag {T : Type} (m : machine_state T) (b : bool) := {|
  flag := b;
  io_map := io_map m; tmp_map := tmp_map m; iarr_map := iarr_map m; varr_map := varr_map m; bound_map := bound_map m;
|}.

Inductive arith_expr :=
| Z3_int8 (x : uint8)
| Z3_int32 (x : uint32)
| Z3_int8_var (name : positive)
| Z3_int32_var (name : positive)
| Z3_bv_add (e1 e2 : arith_expr)
| Z3_bv_sub (e1 e2 : arith_expr)
| Z3_bv_shl (e1 e2 : arith_expr)
| Z3_bv_ashr (e1 e2 : arith_expr)
| Z3_bv_and (e1 e2 : arith_expr)
| Z3_bv_or (e1 e2 : arith_expr)
| Z3_bv_xor (e1 e2 : arith_expr)
| Z3_bv_not (e : arith_expr)
| Z3_arr_sel (e1 : arr_expr) (e2 : arith_expr)
| Z3_arith_ite (c : bool_expr) (e1 e2 : arith_expr)
with ptr_expr :=
| Z3_ptr (x : uintbptr)
| Z3_ptr_var (name : positive)
| Z3_ptr_ite (c : bool_expr) (e1 e2 : ptr_expr)
with arr_expr :=
| Z3_arr_init (len : arith_expr)
| Z3_arr_var (name : positive)
| Z3_arr_st (A : arr_expr) (idx : arith_expr) (item : arith_expr)
| Z3_arr_ite (c : bool_expr) (e1 e2 : arr_expr)
with bool_expr :=
| Z3_T
| Z3_F
| Z3_Neg (e : bool_expr)
| Z3_Conj (e1 e2 : bool_expr)
| Z3_Disj (e1 e2 : bool_expr)
| Z3_Eq (e1 e2 : Z3Expr)
| Z3_Lt (e1 e2 : arith_expr)
with Z3Expr :=
| Z3Arith (e : arith_expr)
| Z3Ptr (e : ptr_expr)
| Z3Array (e : arr_expr)
| Z3Bool (e : bool_expr)
| Z3Nil.

Definition sym_state := machine_state Z3Expr.
Definition init_sym : sym_state := {|
  io_map := PMap.init (nil_t, Z3Nil);
  tmp_map := PMap.init (nil_t, Z3Nil);
  iarr_map := PMap.init (nil_t, Z3Nil);
  varr_map := PMap.init (nil_t, Z3Nil);
  bound_map := PMap.init (nil_t, Z3Nil);
  flag := false;
|}.

Fixpoint apply_io_helper (io : PMap.t (TypedExpr Z3Expr)) (input : list (positive * ValType)) : PMap.t (TypedExpr Z3Expr) :=
  match input with
  | [] => io
  | (k, uint8_t) :: rest =>
    apply_io_helper (PMap.set k (uint8_t, Z3Arith (Z3_int8_var k)) io) rest
  | (k, uint32_t) :: rest =>
    apply_io_helper (PMap.set k (uint32_t, Z3Arith (Z3_int32_var k)) io) rest
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
  bound_map := bound_map init_sym;
  flag := flag init_sym;
|}.

Definition sym_interp_arg (m : sym_state) (a : FnArg) : TypedExpr Z3Expr :=
  match a with
  | IOArg x => (io_map m) !! x
  | TmpArg x => (tmp_map m) !! x
  | ValArg x =>
    match x with
    | imm_u8 x' => (uint8_t, Z3Arith (Z3_int8 x'))
    | imm_u32 x' => (uint32_t, Z3Arith (Z3_int32 x'))
    | imm_ptr x' => (uintptr_t, Z3Ptr (Z3_ptr x'))
    end
  end.

Definition uptr_to_key (p : uintbptr) : positive :=
  Pos.of_nat (S (Z.to_nat (unsigned p))).

Definition sym_alloc (m : sym_state) (dst a1 a2: FnArg) :=
  let local_lookup := sym_interp_arg m in
  let m' :=
    match local_lookup a2 with
    | (uint32_t, Z3Arith e2) =>
      match local_lookup a1 with
      | (uintptr_t, Z3Ptr (Z3_ptr x)) =>
        (set_iarr m (uptr_to_key x) (array_t, Z3Array (Z3_arr_init e2)))
      | (uintptr_t, Z3Ptr (Z3_ptr_var x)) =>
        (set_varr m x (array_t, Z3Array (Z3_arr_init e2)))
      | _ => set_flag m true
      end
    | _ => set_flag m true
    end
  in
  match dst with
  | IOArg x => set_io m' x (local_lookup a1)
  | TmpArg x => set_tmp m' x (local_lookup a1)
  | _ => set_flag m' true
  end.

Definition get_sym_ld_val (m : sym_state) (dst : FnArg) (e1 : ptr_expr) (e2 : arith_expr) :=
  let lookup := match e1 with
  | Z3_ptr x =>
    (iarr_map m) !! (uptr_to_key x)
  | Z3_ptr_var x =>
    (varr_map m) !! x
  | Z3_ptr_ite _ _ _ => (err_t, Z3Nil)
  end in
  let val := match lookup with
  | (array_t, Z3Array A) => (uint8_t, Z3Arith (Z3_arr_sel A e2))
  | _ => (err_t, Z3Nil)
  end in
  let m' := match e1 with 
  | Z3_ptr_var x => match (bound_map m) !! x with
    | (uint32_t, Z3Arith prev_bound) =>
        set_bound m x
        (uint32_t, Z3Arith (Z3_arith_ite
          (Z3_Lt e2 prev_bound)
          prev_bound
          e2))
    | _ => set_bound m x (uint32_t, Z3Arith e2)
    end
  | _ => m
  end in
  match val, dst with
  | (uint8_t, Z3Arith _), IOArg x => set_io m' x val
  | (uint8_t, Z3Arith _), TmpArg x => set_tmp m' x val
  | _, _ => set_flag m true
  end.
Definition sym_ld (m : sym_state) (dst a1 a2 : FnArg) :=
  let local_lookup := sym_interp_arg m in
  let '(a1_t, a1_v) := local_lookup a1 in
  let '(a2_t, a2_v) := local_lookup a2 in
  match a1_t, a1_v, a2_t, a2_v with
  | uintptr_t, Z3Ptr e1, uint32_t, Z3Arith e2 =>
    get_sym_ld_val m dst e1 e2
  | _, _, _, _ => set_flag m true
  end.

Definition sym_st (m : sym_state) (a1 a2 a3 : FnArg) :=
  let local_lookup := sym_interp_arg m in
  (* TODO: handle case where a1 is a ValArg imm_ptr *)
  let st_idx := match local_lookup a2 with
  | (uint32_t, Z3Arith e2) => (uint32_t, Z3Arith e2)
  | _ => (err_t, Z3Nil)
  end in
  let st_val := match local_lookup a3 with
  | (uint8_t, Z3Arith e3) => (uint8_t, Z3Arith e3)
  | _ => (err_t, Z3Nil)
  end in
  match local_lookup a1, st_idx, st_val with
  | (uintptr_t, Z3Ptr (Z3_ptr x)), (uint32_t, Z3Arith e2), (uint8_t, Z3Arith e3) =>
    match (iarr_map m) !! (uptr_to_key x) with
    | (array_t, Z3Array A) =>
      set_iarr m (uptr_to_key x) (array_t, Z3Array (Z3_arr_st A e2 e3))
    | _ => set_flag m true
    end
  | (uintptr_t, Z3Ptr (Z3_ptr_var x)), (uint32_t, Z3Arith e2), (uint8_t, Z3Arith e3) =>
    match (varr_map m) !! x with
    | (array_t, Z3Array A) =>
      match (bound_map m) !! x with
      | (uint32_t, Z3Arith prev_bound) =>
          set_varr (set_bound m x
            (uint32_t, Z3Arith (Z3_arith_ite
              (Z3_Lt e2 prev_bound)
              prev_bound
              e2))) x (array_t, Z3Array (Z3_arr_st A e2 e3))
      | _ => set_varr (set_bound m x st_idx) x (array_t, Z3Array (Z3_arr_st A e2 e3))
      end
    | _ => set_flag m true
    end
  | _, _, _ => set_flag m true
  end.

Definition set_ (dst : FnArg) (m : sym_state) (val : TypedExpr Z3Expr) :=
  match val, dst with
  | (err_t, _), _ => set_flag m true
  | _, IOArg x => set_io m x val
  | _, TmpArg x => set_tmp m x val
  | _, ValArg _ => set_flag m true
  end.

Definition bin_to_expr (op : ArithBinOp) (e1 e2 : arith_expr) : Z3Expr :=
  match op with
  | AddOp => Z3Arith (Z3_bv_add e1 e2)
  | SubOp => Z3Arith (Z3_bv_sub e1 e2)
  | ASLOp => Z3Arith (Z3_bv_shl e1 e2)
  | ASROp => Z3Arith (Z3_bv_ashr e1 e2)
  | BitAndOp => Z3Arith (Z3_bv_and e1 e2)
  | BitOrOp => Z3Arith (Z3_bv_or e1 e2)
  | BitXorOp => Z3Arith (Z3_bv_xor e1 e2)
  end.

Definition sym_binop (m : sym_state) (op : ArithBinOp) (dst a1 a2 : FnArg) :=
  let local_lookup := sym_interp_arg m in
  let new_val : TypedExpr Z3Expr :=
  match local_lookup a1, local_lookup a2 with
  | (uint8_t, Z3Arith e1), (uint8_t, Z3Arith e2) =>
    (uint8_t, bin_to_expr op e1 e2)
  | (uint32_t, Z3Arith e1), (uint32_t, Z3Arith e2) =>
    (uint32_t, bin_to_expr op e1 e2)
  | (_, e1), _ => (err_t, e1)
  end in
  set_ dst m new_val.

Definition sym_bitflip (m : sym_state) (dst a1 : FnArg) :=
  let local_lookup := sym_interp_arg m in
  let new_val : TypedExpr Z3Expr :=
  match local_lookup a1 with
  | (uint8_t, Z3Arith e1) =>
    (uint8_t, Z3Arith (Z3_bv_not e1))
  | (uint32_t, Z3Arith e1) =>
    (uint32_t, Z3Arith (Z3_bv_not e1))
  | (_, e1) => (err_t, e1)
  end in
  set_ dst m new_val.

Definition get_ite_expr (c : bool_expr) (te1 te2 : TypedExpr Z3Expr) : TypedExpr Z3Expr :=
  let '(t1, v1) := te1 in
  let '(t2, v2) := te2 in
  let ite_expr :=
  match v1, v2 with
  | Z3Arith e1, Z3Arith e2 => Z3Arith (Z3_arith_ite c e1 e2)
  | Z3Ptr e1, Z3Ptr e2 => Z3Ptr (Z3_ptr_ite c e1 e2)
  | Z3Array e1, Z3Array e2 => Z3Array (Z3_arr_ite c e1 e2)
  | _, _ => Z3Nil
  end in
  match t1, t2 with
  | err_t, _ => te1
  | _, err_t => te2
  | _, _ => (t1, ite_expr)
  end.

Fixpoint merge_var_maps (c : bool_expr) (keys : list positive)
    (m1 m2 : PMap.t (TypedExpr Z3Expr)) (acc : PMap.t (TypedExpr Z3Expr)) : PMap.t (TypedExpr Z3Expr) :=
  match keys with
  | [] => acc
  | k :: rest =>
    let v := get_ite_expr c (m1 !! k) (m2 !! k) in
    merge_var_maps c rest m1 m2 (PMap.set k v acc)
  end.
Definition as_ite (c : bool_expr) (keys : list positive) (m1 m2 : sym_state) : sym_state := {|
  io_map := merge_var_maps c keys (io_map m1) (io_map m2) (io_map m2);
  tmp_map := merge_var_maps c keys (tmp_map m1) (tmp_map m2) (tmp_map m2);
  iarr_map := merge_var_maps c keys (iarr_map m1) (iarr_map m2) (iarr_map m2);
  varr_map := merge_var_maps c keys (varr_map m1) (varr_map m2) (varr_map m2);
  bound_map := merge_var_maps c keys (bound_map m1) (bound_map m2) (bound_map m2);
  flag := orb (flag m1) (flag m2);
|}.

Fixpoint collect_dst_keys_instr (i : Instruction) : list positive :=
  let dst_key_of := fun a => match a with IOArg x | TmpArg x => [x] | _ => [] end in
  let ptr_key_of := fun a => match a with IOArg x | TmpArg x => [x] | _ => [] end in
  match i with
  | AllocOp dst a1 _ => dst_key_of dst ++ ptr_key_of a1
  | LdOp dst a1 _ => dst_key_of dst ++ ptr_key_of a1
  | StOp a1 _ _ => ptr_key_of a1
  | Binary _ dst _ _ => dst_key_of dst
  | BitFlipOp dst _ => dst_key_of dst
  | BrzOp _ if_z if_nz =>
    (fix go (l : list Instruction) :=
      match l with [] => [] | x :: xs => collect_dst_keys_instr x ++ go xs end) if_z
    ++
    (fix go (l : list Instruction) :=
      match l with [] => [] | x :: xs => collect_dst_keys_instr x ++ go xs end) if_nz
  end.
Definition collect_dst_keys (instrs : list Instruction) : list positive :=
  flat_map collect_dst_keys_instr instrs.

Fixpoint apply_sym_op (i : Instruction) (m : sym_state) {struct i} : sym_state :=
  if (flag m) then
    m
  else
    match i with
    | AllocOp dst a1 a2 => sym_alloc m dst a1 a2
    | LdOp dst a1 a2 => sym_ld m dst a1 a2
    | StOp a1 a2 a3 => sym_st m a1 a2 a3
    | Binary op dst a1 a2 => sym_binop m op dst a1 a2
    | BitFlipOp dst a1 => sym_bitflip m dst a1
    | BrzOp cond zero_br nonzero_br =>
      let eval_list :=
        fix go (p : list Instruction) (m : sym_state) : sym_state :=
          match p with
          | [] => m
          | i :: rest => go rest (apply_sym_op i m)
          end
      in
      let local_lookup := sym_interp_arg m in
      match local_lookup cond with
      | (uint8_t, Z3Arith cond_e) =>
        let if_zero := Z3_Eq (Z3Arith cond_e) (Z3Arith (Z3_int8 (repr 0))) in
        let m_zero := eval_list zero_br m in
        let m_nonzero := eval_list nonzero_br m in
        let keys := collect_dst_keys zero_br ++ collect_dst_keys nonzero_br in
        as_ite if_zero keys m_zero m_nonzero
      | (uint32_t, Z3Arith cond_e) =>
        let if_zero := Z3_Eq (Z3Arith cond_e) (Z3Arith (Z3_int32 (repr 0))) in
        let m_zero := eval_list zero_br m in
        let m_nonzero := eval_list nonzero_br m in
        let keys := collect_dst_keys zero_br ++ collect_dst_keys nonzero_br in
        as_ite if_zero keys m_zero m_nonzero
      | _ => set_flag m true
      end
    end.

Definition sym_eval_helper (p : list Instruction) (m : sym_state) : sym_state :=
  List.fold_left (fun m' i => apply_sym_op i m') p m.

Record output_valuation {T : Type} : Type := {
  errored : HasError;
  var_val : var_id -> TypedExpr T;
  iptr_val : (uintbptr * uint32) -> TypedExpr T;
  vptr_val : (var_id * uint32) -> TypedExpr T;
  vptr_bound : var_id -> TypedExpr T;
}.
Arguments output_valuation T : clear implicits.

Definition sym_eval_program (p : IM_Program) : output_valuation Z3Expr :=
  let m' := sym_eval_helper (fn_body p) (apply_input init_sym (fn_in p)) in {|
    errored := flag m';
    var_val := fun k => match (io_map m') !! k with
      | (nil_t, _) => (nil_t, Z3Nil)
      | (err_t, _) => (err_t, Z3Nil)
      | (t, e) => (t, e)
      end;
    iptr_val := fun '(b, i) => match (iarr_map m') !! (uptr_to_key b) with
      | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_sel e (Z3_int32 i)))
      | _ => (err_t, Z3Nil)
      end;
    vptr_val := fun '(k, i) => match (varr_map m') !! k with
      | (array_t, Z3Array e) => (uint8_t, Z3Arith (Z3_arr_sel e (Z3_int32 i)))
      | _ => (err_t, Z3Nil)
      end;
    vptr_bound := fun k => match (bound_map m') !! k with
      | (uint32_t, Z3Arith e) => (uint32_t, Z3Arith e)
      | _ => (err_t, Z3Nil)
      end;
  |}.

Definition z3_s_val : Type := var_id -> CrVal.
Definition z3_a_val : Type := var_id -> @Array CrVal.

Definition eval_z3_arith_binop (op : ArithBinOp) (v1 v2 : CrVal) : CrVal :=
  match v1, v2 with
  | IntVal (CrUInt8 x1), IntVal (CrUInt8 x2) =>
    match op with
    | AddOp => IntVal (CrUInt8 (Integers.add x1 x2))
    | SubOp => IntVal (CrUInt8 (Integers.sub x1 x2))
    | ASLOp => IntVal (CrUInt8 (Integers.shl x1 x2))
    | ASROp => IntVal (CrUInt8 (Integers.shr x1 x2))
    | BitAndOp => IntVal (CrUInt8 (Integers.and x1 x2))
    | BitOrOp => IntVal (CrUInt8 (Integers.or x1 x2))
    | BitXorOp => IntVal (CrUInt8 (Integers.xor x1 x2))
    end
  | IntVal (CrUInt32 x1), IntVal (CrUInt32 x2) =>
    match op with
    | AddOp => IntVal (CrUInt32 (Integers.add x1 x2))
    | SubOp => IntVal (CrUInt32 (Integers.sub x1 x2))
    | ASLOp => IntVal (CrUInt32 (Integers.shl x1 x2))
    | ASROp => IntVal (CrUInt32 (Integers.shr x1 x2))
    | BitAndOp => IntVal (CrUInt32 (Integers.and x1 x2))
    | BitOrOp => IntVal (CrUInt32 (Integers.or x1 x2))
    | BitXorOp => IntVal (CrUInt32 (Integers.xor x1 x2))
    end
  | _, _ => ErrorVal
  end.

Fixpoint eval_z3_arith (e : arith_expr) (sval : z3_s_val) (aval : z3_a_val) : CrVal :=
  match e with
  | Z3_int8 x => IntVal (CrUInt8 x)
  | Z3_int32 x => IntVal (CrUInt32 x)
  | Z3_int8_var name
  | Z3_int32_var name => sval name
  | Z3_bv_add e1 e2 =>
    eval_z3_arith_binop AddOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_sub e1 e2 =>
    eval_z3_arith_binop SubOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_shl e1 e2 =>
    eval_z3_arith_binop ASLOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_ashr e1 e2 =>
    eval_z3_arith_binop ASROp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_and e1 e2 =>
    eval_z3_arith_binop BitAndOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_or e1 e2 =>
    eval_z3_arith_binop BitOrOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_xor e1 e2 =>
    eval_z3_arith_binop BitXorOp
      (eval_z3_arith e1 sval aval)
      (eval_z3_arith e2 sval aval)
  | Z3_bv_not e1 =>
    let v := eval_z3_arith e1 sval aval in
    match v with
    | IntVal (CrUInt8 x) => IntVal (CrUInt8 (Integers.not x))
    | IntVal (CrUInt32 x) => IntVal (CrUInt32 (Integers.not x))
    | _ => ErrorVal
    end
  | Z3_arr_sel e1 e2 =>
    let res := CrVal.ld_arr (eval_z3_array e1 sval aval) (eval_z3_arith e2 sval aval) in
    match res with
    | Legal v => v
    | Illegal => ErrorVal
    end
  | Z3_arith_ite c e1 e2 =>
    match eval_z3_bool c sval aval with
    | true => eval_z3_arith e1 sval aval
    | false => eval_z3_arith e2 sval aval
    end
  end
with eval_z3_ptr (e : ptr_expr) (sval : z3_s_val) (aval : z3_a_val) : CrVal :=
  match e with
  | Z3_ptr x => PtrVal (CrPtr x)
  | Z3_ptr_var name => sval name
  | Z3_ptr_ite c e1 e2 =>
    match eval_z3_bool c sval aval with
    | true => eval_z3_ptr e1 sval aval
    | false => eval_z3_ptr e2 sval aval
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
  | Z3_arr_ite c e1 e2 =>
    match eval_z3_bool c sval aval with
    | true => eval_z3_array e1 sval aval
    | false => eval_z3_array e2 sval aval
    end
  end
with eval_z3_bool (e : bool_expr) (sval : z3_s_val) (aval : z3_a_val) : bool :=
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
  | Z3_Lt e1 e2 =>
    let v1 := eval_z3_arith e1 sval aval in
    let v2 := eval_z3_arith e2 sval aval in
    CrVal.ltb v1 v2
  end
with eval_z3_expr (e : Z3Expr) (sval : z3_s_val) (aval : z3_a_val) : CrVal :=
  match e with
  | Z3Arith e' =>
    eval_z3_arith e' sval aval
  | Z3Ptr e' =>
    eval_z3_ptr e' sval aval
  | _ => ErrorVal
  end.

(* Check that bounds are equal for all variable arrays *)
Definition query_bounds (p1 p2 : IM_Program) : bool_expr :=
  let val1 := sym_eval_program p1 in
  let val2 := sym_eval_program p2 in

  (* Extract variable ids from input (uintptr_t) and output vaddrs *)
  let input_vars := List.map fst (List.filter (fun '(_, t) => match t with uintptr_t => true | _ => false end) (fn_in p1)) in
  let output_vars := List.map fst (fn_out_vaddrs p1) in
  let bound_vars := input_vars ++ output_vars in

  let b1 := List.map (vptr_bound val1) bound_vars in
  let b2 := List.map (vptr_bound val2) bound_vars in
  
  fold_right Z3_Conj Z3_T
    (map (fun '((_, x), (_, y)) => Z3_Eq x y) (combine b1 b2)).

(* Check that outputs are equal (error flag, variables, and memory writes) *)
Definition query_outputs (p1 p2 : IM_Program) : bool_expr :=
  let val1 := sym_eval_program p1 in
  let val2 := sym_eval_program p2 in

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
    let e_expr :=
      if (orb (andb e1 e2) (andb (negb e1) (negb e2)))
      then Z3_T
      else Z3_F in
    let v_expr := fold_right Z3_Conj Z3_T
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

(* Main query: check if outputs and bounds differ *)
Definition query_expression (p1 p2 : IM_Program) : bool_expr :=
  Z3_Neg (Z3_Conj (query_outputs p1 p2) (query_bounds p1 p2)).

Inductive FailureMode :=
| ValueMismatch
| BoundsMismatch
| FullMismatch.

Inductive Z3Res :=
| Z3Sat (s : z3_s_val) (a : z3_a_val) (f : FailureMode)
| Z3Unsat
| Z3Unknown.
Parameter z3_query : bool_expr -> Z3Res.

Axiom z3_sound_some:
  forall e sval aval f,
    z3_query e = Z3Sat sval aval f ->
    eval_z3_bool e sval aval = true.
Axiom z3_sound_none:
  forall e,
    z3_query e = Z3Unsat ->
    forall sval aval,
    eval_z3_bool e sval aval = false.

Definition matching_fn_io (p1 p2 : IM_Program) : Prop :=
  (fn_in p1) = (fn_in p2) /\
  (fn_out_vars p1) = (fn_out_vars p2) /\
  (fn_out_iaddrs p1) = (fn_out_iaddrs p2) /\
  (fn_out_vaddrs p1) = (fn_out_vaddrs p2).

Definition matching_error (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val),
    errored (sym_eval_program p1) = errored (sym_eval_program p2).
Lemma mem_prog_soundness_error:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_error p1 p2.
Proof.
  intros.
Admitted.

Definition matching_io_vars (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (v : var_id),
    In v (fn_out_vars p1) ->
    eval_z3_expr
      (snd ((var_val (sym_eval_program p1)) v))
      sval aval =
    eval_z3_expr
      (snd ((var_val (sym_eval_program p2)) v))
      sval aval.
Lemma mem_prog_soundness_io_vars:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_io_vars p1 p2.
Proof.
  intros.
Admitted.

Definition matching_abs_addrs (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (ia : uintbptr) (ix1 : uint32),
    In (ia, ix1) (fn_out_iaddrs p1) ->
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p1)) (ia, ix1)))
      sval aval =
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p2)) (ia, ix1)))
      sval aval.
Lemma mem_prog_soundness_abs_addrs:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_abs_addrs p1 p2.
Proof.
  intros.
Admitted.

Definition matching_var_addrs (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (va : var_id) (ix2 : uint32),
    In (va, ix2) (fn_out_vaddrs p1) ->
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p1)) (va, ix2)))
      sval aval =
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p2)) (va, ix2)))
      sval aval.
Lemma mem_prog_soundness_var_addrs:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_var_addrs p1 p2.
Proof.
  intros.
Admitted.

Definition matching_access_bounds (p1 p2 : IM_Program) : Prop :=
  forall (sval : z3_s_val) (aval : z3_a_val) (va : var_id),
    (In va (List.map fst (List.filter (fun '(_, t) => match t with uintptr_t => true | _ => false end) (fn_in p1))) \/
     In va (List.map fst (fn_out_vaddrs p1))) ->
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p1)) va))
      sval aval =
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p2)) va))
      sval aval.
Lemma mem_prog_soundness_access_bounds:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
  matching_access_bounds p1 p2.
Proof.
  intros.
Admitted.

Lemma mem_prog_soundness:
  forall (p1 p2 : IM_Program),
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Unsat ->
    matching_error p1 p2 /\
    matching_io_vars p1 p2 /\
    matching_abs_addrs p1 p2 /\
    matching_var_addrs p1 p2 /\
    matching_access_bounds p1 p2.
Proof with assumption.
  intros. repeat split.
  - apply mem_prog_soundness_error...
  - apply mem_prog_soundness_io_vars...
  - apply mem_prog_soundness_abs_addrs...
  - apply mem_prog_soundness_var_addrs...
  - apply mem_prog_soundness_access_bounds...
Qed.

Definition differing_error (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  errored (sym_eval_program p1) <> errored (sym_eval_program p2).

Definition differing_io_vars (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (v : var_id),
    In v (fn_out_vars p1) /\
    eval_z3_expr
      (snd ((var_val (sym_eval_program p1)) v))
      sval aval <>
    eval_z3_expr
      (snd ((var_val (sym_eval_program p2)) v))
      sval aval.

Definition differing_abs_addrs (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (ia : uintbptr) (ix1 : uint32),
    In (ia, ix1) (fn_out_iaddrs p1) /\
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p1)) (ia, ix1)))
      sval aval <>
    eval_z3_expr
      (snd ((iptr_val (sym_eval_program p2)) (ia, ix1)))
      sval aval.

Definition differing_var_addrs (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (va : var_id) (ix2 : uint32),
    In (va, ix2) (fn_out_vaddrs p1) /\
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p1)) (va, ix2)))
      sval aval <>
    eval_z3_expr
      (snd ((vptr_val (sym_eval_program p2)) (va, ix2)))
      sval aval.

Definition differing_access_bounds (p1 p2 : IM_Program) (sval : z3_s_val) (aval : z3_a_val) : Prop :=
  exists (va : var_id),
    (In va (List.map fst (List.filter (fun '(_, t) => match t with uintptr_t => true | _ => false end) (fn_in p1))) \/
     In va (List.map fst (fn_out_vaddrs p1))) /\
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p1)) va))
      sval aval <>
    eval_z3_expr
      (snd ((vptr_bound (sym_eval_program p2)) va))
      sval aval.

Lemma mem_prog_completeness:
  forall (p1 p2 : IM_Program) sval aval f,
  matching_fn_io p1 p2 ->
  z3_query (query_expression p1 p2) = Z3Sat sval aval f ->
  differing_error p1 p2 sval aval \/
  differing_io_vars p1 p2 sval aval \/
  differing_abs_addrs p1 p2 sval aval \/
  differing_var_addrs p1 p2 sval aval \/
  differing_access_bounds p1 p2 sval aval.
Proof.
  intros.
Admitted.
