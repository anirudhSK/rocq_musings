From MyProject Require Import CrMem.
From MyProject Require Import CrVal.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From Stdlib Require Import ZArith.
From Stdlib.Strings Require Import String.
From Stdlib.Strings Require Import Ascii.
From Stdlib Require Import List.
Import ListNotations.


Definition rdi : positive := 1.
Definition rsi : positive := 2.
Definition rdx : positive := 3.
Definition rcx : positive := 4.
Definition rax : positive := 5.

Definition local_x := (TmpArg 1%positive).
Definition b_plus_c := (TmpArg 2%positive).
Definition x4_val := (TmpArg 3%positive).
Definition two_plus_two := (TmpArg 4%positive).

Definition p1a : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t)
  ];
  fn_body := [
    AllocOp local_x
      (ValArg (imm_ptr (repr 0x400)))
      (ValArg (imm_u32 (repr 16)));
    Binary AddOp b_plus_c
      (IOArg rsi)
      (IOArg rdx);
    StOp uint8_t local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp uint8_t x4_val
      local_x
      (ValArg (imm_u32 (repr 4)));
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      x4_val
  ];
  fn_out_vars := [];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [(rdi, (repr 0))];
|}.

(* Compute List.map (vptr_val (compile_sym p1)) (fn_out_vaddrs p1). *)

Definition p1b : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t)
  ];
  fn_body := [
    AllocOp local_x
      (ValArg (imm_ptr (repr 0x400)))
      (ValArg (imm_u32 (repr 16)));
    Binary AddOp b_plus_c
      (IOArg rsi)
      (IOArg rdx);
    Binary AddOp two_plus_two
      (ValArg (imm_u32 (repr 2)))
      (ValArg (imm_u32 (repr 2)));
    StOp uint8_t local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp uint8_t x4_val
      local_x
      two_plus_two;
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      x4_val
  ];
  fn_out_vars := [];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [(rdi, (repr 0))];
|}.

Definition p1c : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t)
  ];
  fn_body := [
    AllocOp local_x
      (ValArg (imm_ptr (repr 0x400)))
      (ValArg (imm_u32 (repr 16)));
    Binary AddOp b_plus_c
      (IOArg rsi)
      (IOArg rdx);
    StOp uint8_t local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp uint8_t x4_val
      local_x
      (ValArg (imm_u32 (repr 4)));
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      x4_val;
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      (ValArg (imm_u8 (repr 1)))
  ];
  fn_out_vars := [];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [(rdi, (repr 0))];
|}.

Definition p2a : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.
Definition p2b : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    LdOp uint8_t (TmpArg 1%positive)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 1)));
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.
Definition p2c : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)));
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 1)))
      (ValArg (imm_u8 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition p3a : IM_Program := {|
  fn_in := [
    (rdi, uint8_t);
    (rsi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    BrzOp (ValArg (imm_u8 (repr 0)))
      [
        Binary AddOp (IOArg rax)
          (IOArg rdi)
          (ValArg (imm_u8 (repr 0)))
      ]
      [
        LdOp uint8_t (IOArg rax)
          (IOArg rsi)
          (ValArg (imm_u32 (repr 0)))
      ]
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.
Definition p3b : IM_Program := {|
  fn_in := [
    (rdi, uint8_t);
    (rsi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    Binary AddOp (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u8 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition p4a : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 1)));
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.
Definition p4b : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rax, uint8_t)
  ];
  fn_body := [
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)));
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 1)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition example_programs := [
  p1a; p1b; p1c;
  p2a; p2b; p2c;
  p3a; p3b;
  p4a; p4b
].

(* ================================================================= *)
(* Multi-byte load/store test programs                                *)
(* ================================================================= *)

Definition mb8 : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t);
    (rax, uint8_t)
  ];
  fn_body := [
    Binary AddOp (IOArg rax)
      (IOArg rsi)
      (IOArg rdx);
    StOp uint8_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      (IOArg rax);
    LdOp uint8_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition mb16 : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint16_t);
    (rdx, uint16_t);
    (rax, uint16_t)
  ];
  fn_body := [
    Binary AddOp (IOArg rax)
      (IOArg rsi)
      (IOArg rdx);
    StOp uint16_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      (IOArg rax);
    LdOp uint16_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition mb32 : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint32_t);
    (rdx, uint32_t);
    (rax, uint32_t)
  ];
  fn_body := [
    Binary AddOp (IOArg rax)
      (IOArg rsi)
      (IOArg rdx);
    StOp uint32_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      (IOArg rax);
    LdOp uint32_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Definition mb64 : IM_Program := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint64_t);
    (rdx, uint64_t);
    (rax, uint64_t)
  ];
  fn_body := [
    Binary AddOp (IOArg rax)
      (IOArg rsi)
      (IOArg rdx);
    StOp uint64_t (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      (IOArg rax);
    LdOp uint64_t (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
  ];
  fn_out_vars := [rax];
  fn_out_iaddrs := [];
  fn_out_vaddrs := [];
|}.

Compute (var_val (sym_eval_program mb8) rax).
Compute (var_val (sym_eval_program mb16) rax).
Compute (var_val (sym_eval_program mb32) rax).
Compute (var_val (sym_eval_program mb64) rax).
