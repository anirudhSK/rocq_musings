From MyProject Require Import CrMem.
From MyProject Require Import CrVal.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
Require Import ZArith.
From Coq.Strings Require Import String.
From Coq.Strings Require Import Ascii.
Require Import List.
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
    StOp local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp x4_val
      local_x
      (ValArg (imm_u32 (repr 4)));
    StOp (IOArg rdi)
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
    StOp local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp x4_val
      local_x
      two_plus_two;
    StOp (IOArg rdi)
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
    StOp local_x
      (ValArg (imm_u32 (repr 4)))
      b_plus_c;
    LdOp x4_val
      local_x
      (ValArg (imm_u32 (repr 4)));
    StOp (IOArg rdi)
      (ValArg (imm_u32 (repr 0)))
      x4_val;
    StOp (IOArg rdi)
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
    LdOp (IOArg rax)
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
    LdOp (TmpArg 1%positive)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 1)));
    LdOp (IOArg rax)
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
    LdOp (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)));
    StOp (IOArg rdi)
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
        LdOp (IOArg rax)
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
    LdOp (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 1)));
    LdOp (IOArg rax)
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
    LdOp (IOArg rax)
      (IOArg rdi)
      (ValArg (imm_u32 (repr 0)));
    LdOp (IOArg rax)
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
