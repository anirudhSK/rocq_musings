From MyProject Require Import Maps.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.

From Stdlib Require Import List.
Import ListNotations.

(* [Th] is the header-value type, [Tb] the packet-bit type. *)
Record GeneralProgramState (Th Tb : Type) := {
  sh_hdr_map : PMap.t Th;
  sh_read_tape : list Tb;
  sh_bits_read : Th;
  sh_write_tape : list Tb;
  mod_states : PMap.t (ModuleState Th Tb);
  gps_valid : Tb;
}.

Arguments sh_hdr_map {Th Tb} _.
Arguments sh_read_tape {Th Tb} _.
Arguments sh_bits_read {Th Tb} _.
Arguments sh_write_tape {Th Tb} _.
Arguments mod_states {Th Tb} _.
Arguments gps_valid {Th Tb} _.

Definition set_gps_shared_headers {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (hdrs : PMap.t Th)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := hdrs;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_shared_read_tape {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (bits : list Tb)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := bits;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_bits_read {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (n : Th)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := n;
     sh_write_tape := sh_write_tape gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_shared_write_tape {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (cbits : list Tb)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := cbits;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_mod_states {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (ms : PMap.t (ModuleState Th Tb))
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     mod_states := ms;
     gps_valid := gps_valid gps |}.

Definition set_gps_valid {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (valid : Tb)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     mod_states := mod_states gps;
     gps_valid := valid |}.

Definition GeneralConcreteState : Type := GeneralProgramState CrVal bool.
Definition GeneralSymbolicState : Type := GeneralProgramState SmtArithExpr (ConditionalVal SmtBoolExpr).
