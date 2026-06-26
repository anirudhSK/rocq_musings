From MyProject Require Import Maps.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.

(* [Th] is the header-value type, [Tb] the packet-bit type. *)
Record GeneralProgramState (Th Tb : Type) := {
  sh_hdr_map : PMap.t Th;
  sh_bit_map : list Tb;
  mod_states : PMap.t (ModuleState Th Tb);
}.

Arguments sh_hdr_map {Th Tb} _.
Arguments sh_bit_map {Th Tb} _.
Arguments mod_states {Th Tb} _.

Definition set_gps_shared_headers {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (hdrs : PMap.t Th)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := hdrs;
     sh_bit_map := (sh_bit_map gps);
     mod_states := (mod_states gps); |}.

Definition set_gps_shared_bits {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (bits : list Tb)
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := (sh_hdr_map gps);
     sh_bit_map := bits;
     mod_states := (mod_states gps); |}.

Definition set_gps_mod_states {Th Tb : Type}
  (gps : GeneralProgramState Th Tb) (ms : PMap.t (ModuleState Th Tb))
  : GeneralProgramState Th Tb :=
  {| sh_hdr_map := (sh_hdr_map gps);
     sh_bit_map := (sh_bit_map gps);
     mod_states := ms; |}.

Definition GeneralConcreteState : Type := GeneralProgramState CrVal bool.
Definition GeneralSymbolicState : Type := GeneralProgramState SmtArithExpr SmtBoolExpr.
