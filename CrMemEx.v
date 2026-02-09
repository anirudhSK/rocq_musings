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

Definition p1 : MemProgram := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t)
  ];
  fn_body := [
    AllocOp local_x
      (ValArg (imm_ptr (repr 0x400)))
      (ValArg (imm_u32 (repr 16)));
    AddOp b_plus_c
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

Compute List.map (vptr_val (compile_sym p1)) (fn_out_vaddrs p1).

Definition p2 : MemProgram := {|
  fn_in := [
    (rdi, uintptr_t);
    (rsi, uint8_t);
    (rdx, uint8_t)
  ];
  fn_body := [
    AllocOp local_x
      (ValArg (imm_ptr (repr 0x400)))
      (ValArg (imm_u32 (repr 16)));
    AddOp b_plus_c
      (IOArg rsi)
      (IOArg rdx);
    AddOp two_plus_two
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
