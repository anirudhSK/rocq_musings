From MyProject Require Import Maps.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.

From Stdlib Require Import List.
Import ListNotations.

(* [Th] is the header-value type, [Tb] the packet-bit type, [Tm] the type of a
   memory region's contents.

   [Tm] is a third parameter rather than a reuse of [Th] because a region is
   not a scalar: concretely it is an [Array CrVal], symbolically an
   [SmtArrExpr].  Memory lives here rather than on [TransformerState] because
   [TransformerState T] is homogeneous in a single element type -- see the
   comment on [CrConcreteSemanticsTransformer.eval_transformer_concrete_mem]
   for how it is threaded into a transformer instead.

   [sh_mem_extent] is the memory analogue of [sh_bits_read]: per region, HOW
   MANY BYTES of it the run required -- one past the highest byte touched, not
   that byte's offset.  A count, so 0 still means "never touched".  Updated on
   every access, in bounds or not, which is what lets loads and stores stay
   total: two programs emitting the same packet while reaching different
   distances into a region are not interchangeable, since one can fault where
   the other does not. *)
Record GeneralProgramState (Th Tb Tm : Type) := {
  sh_hdr_map : PMap.t Th;
  sh_read_tape : list Tb;
  sh_bits_read : Th;
  sh_write_tape : list Tb;
  sh_mem : PMap.t Tm;
  sh_mem_extent : PMap.t Th;
  mod_states : PMap.t (ModuleState Th Tb);
  gps_valid : Tb;
}.

Arguments sh_hdr_map {Th Tb Tm} _.
Arguments sh_read_tape {Th Tb Tm} _.
Arguments sh_bits_read {Th Tb Tm} _.
Arguments sh_write_tape {Th Tb Tm} _.
Arguments sh_mem {Th Tb Tm} _.
Arguments sh_mem_extent {Th Tb Tm} _.
Arguments mod_states {Th Tb Tm} _.
Arguments gps_valid {Th Tb Tm} _.

Definition set_gps_shared_headers {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (hdrs : PMap.t Th)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := hdrs;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_shared_read_tape {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (bits : list Tb)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := bits;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_bits_read {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (n : Th)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := n;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_shared_write_tape {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (cbits : list Tb)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := cbits;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_mem {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (m : PMap.t Tm)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := m;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_mem_extent {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (e : PMap.t Th)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := e;
     mod_states := mod_states gps;
     gps_valid := gps_valid gps |}.

Definition set_gps_mod_states {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (ms : PMap.t (ModuleState Th Tb))
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := ms;
     gps_valid := gps_valid gps |}.

Definition set_gps_valid {Th Tb Tm : Type}
  (gps : GeneralProgramState Th Tb Tm) (valid : Tb)
  : GeneralProgramState Th Tb Tm :=
  {| sh_hdr_map := sh_hdr_map gps;
     sh_read_tape := sh_read_tape gps;
     sh_bits_read := sh_bits_read gps;
     sh_write_tape := sh_write_tape gps;
     sh_mem := sh_mem gps;
     sh_mem_extent := sh_mem_extent gps;
     mod_states := mod_states gps;
     gps_valid := valid |}.

Definition GeneralConcreteState : Type :=
  GeneralProgramState CrVal bool (@Array CrVal).
Definition GeneralSymbolicState : Type :=
  GeneralProgramState SmtArithExpr (ConditionalVal SmtBoolExpr) SmtArrExpr.

(* -------------------------------------------------------------------- *)
(* What running a parser produces, shared by the two evaluators.        *)
(*                                                                      *)
(* [Th] is the header/count type, [Tb] the accept condition, and [Tbit] *)
(* a residual packet bit.  The last two are NOT the same type on the    *)
(* symbolic side: an accept condition is a bare [SmtBoolExpr], while a  *)
(* residual bit carries its presence flag as a [ConditionalVal].        *)
(*                                                                      *)
(* [pr_accept] is what makes a rejection a RESULT rather than an        *)
(* absence, which is the whole point of the record.  The concrete       *)
(* evaluator returns [option ConcParserResult], and with the verdict    *)
(* living in the payload the [option] is free to mean something much    *)
(* narrower: [None] iff the run did not complete -- fuel exhausted, or  *)
(* a transition named a state with no definition.  A parse that rejects *)
(* the packet, including one that runs off its end, is [Some] with      *)
(* [pr_accept := false].  Well-formedness rules out both [None] cases   *)
(* (see [CrDslProperties.well_formed_parser]), which is what lets       *)
(* [eval_parser_no_fuel_starvation] conclude the concrete evaluator is  *)
(* total on well-formed parsers.                                        *)
Record ParserResult (Th Tb Tbit : Type) : Type := mkParserResult {
  pr_accept    : Tb;              (* accepts iff this holds *)
  pr_headers   : PMap.t Th;       (* final header values *)
  pr_residual  : list Tbit;       (* unconsumed tail *)
  pr_bits_read : Th;              (* bits consumed *)
}.

Arguments pr_accept {Th Tb Tbit} _.
Arguments pr_headers {Th Tb Tbit} _.
Arguments pr_residual {Th Tb Tbit} _.
Arguments pr_bits_read {Th Tb Tbit} _.
Arguments mkParserResult {Th Tb Tbit} _ _ _ _.

Definition ConcParserResult : Type :=
  ParserResult CrVal bool bool.
Definition SymParserResult : Type :=
  ParserResult SmtArithExpr SmtBoolExpr (ConditionalVal SmtBoolExpr).
