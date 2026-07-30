From Stdlib Require Import ZArith.
From MyProject Require Import SmtExpr.
From MyProject Require Import Maps.
From MyProject Require Import CrVal.

(* The TransformerState is a record containing three maps:,
   one each for mapping headers/statevars/ctrlplaneconfigs to their current values *)
Record TransformerState (T : Type) := {
  t_ctrl_map : PMap.t T;
  t_header_map : PMap.t T;
  t_state_map : PMap.t T;
}.

Arguments t_header_map {T} _.
Arguments t_state_map {T} _.  
Arguments t_ctrl_map {T} _.

Definition ConcreteTransformerState := TransformerState CrVal.
Definition SymbolicTransformerState := TransformerState SmtArithExpr.

(* ------------------------------------------------------------------ *)
(* Memory, as seen by a transformer.  [mc_mem] maps a [MemRegion]'s key to
   that region's contents and [mc_extent] to the largest offset touched so far.

   This is a separate bundle rather than a fourth field on [TransformerState]
   because [TransformerState T] is homogeneous in one element type -- ctrl,
   header and state values all have type [T], and [CrVarLike] and
   [program_state_mapper] are built on that.  A region's contents are not of
   that type ([Array CrVal] concretely, [SmtArrExpr] symbolically), so it is
   threaded alongside the state instead of inside it. *)
Record MemCtx (Th Tm : Type) := {
  mc_mem    : PMap.t Tm;
  mc_extent : PMap.t Th;
}.

Arguments mc_mem {Th Tm} _.
Arguments mc_extent {Th Tm} _.

Definition set_mc_mem {Th Tm : Type} (mc : MemCtx Th Tm) (m : PMap.t Tm)
    : MemCtx Th Tm :=
  {| mc_mem := m; mc_extent := mc_extent mc |}.

Definition set_mc_extent {Th Tm : Type} (mc : MemCtx Th Tm) (e : PMap.t Th)
    : MemCtx Th Tm :=
  {| mc_mem := mc_mem mc; mc_extent := e |}.

Definition ConcreteMemCtx := MemCtx CrVal (@Array CrVal).
Definition SymbolicMemCtx := MemCtx SmtArithExpr SmtArrExpr.

(* The memory a program with no declared regions runs against: every region is
   undeclared, so every access is out of bounds.  This is what the memory-free
   entry points ([eval_transformer_concrete] and friends) supply. *)
Definition empty_concrete_mem_ctx : ConcreteMemCtx :=
  {| mc_mem := PMap.init (@Unallocated CrVal);
     mc_extent := PMap.init (mk_int u64 0%Z) |}.

Definition empty_symbolic_mem_ctx : SymbolicMemCtx :=
  {| mc_mem := PMap.init SmtArrInit;
     mc_extent := PMap.init (SmtArithConst (mask_width W64 0) u64) |}.

(* ------------------------------------------------------------------ *)
(* Parser-specific runtime state.  Carries its own header map (the shared
   inter-module interface) plus the input packet bit stream it parses
   from and a read cursor (a bit offset into [p_packet]).  Parameterized
   by two types: [Th] is the header-value type and [Tb] is the packet-bit
   type, since a packet bit and a header value differ between the concrete
   and symbolic engines (concretely [CrVal]/[bool]; symbolically
   [SmtArithExpr]/[SmtBoolExpr]). *)
Record ParserState (Th Tb : Type) := {
  p_header_map : PMap.t Th;
  p_packet     : list Tb;   (* input bit stream, MSB-first *)
  p_cursor     : nat;       (* current read offset into [p_packet] *)
}.

Arguments p_header_map {Th Tb} _.
Arguments p_packet {Th Tb} _.
Arguments p_cursor {Th Tb} _.

Definition ConcreteParserState := ParserState CrVal bool.
Definition SymbolicParserState := ParserState SmtArithExpr (ConditionalVal SmtBoolExpr).

(* ------------------------------------------------------------------------ *)
(* Inject a fresh header map into a [TransformerState], keeping ctrl/state. *)
Definition inject_headers {T : Type} (packet : PMap.t T) (local : TransformerState T)
    : TransformerState T :=
  {| t_ctrl_map   := t_ctrl_map local;
     t_header_map := packet;
     t_state_map  := t_state_map local |}.

(* ------------------------------------------------------------------ *)
(* Per-module runtime state.  Both kinds carry a single payload record that
   owns its own header map: transformer modules a full [TransformerState]
   (ctrl/header/state); parser modules a [ParserState] (header + packet).
   [Th] is the header-value type, [Tb] the packet-bit type. *)
Inductive ModuleState (Th Tb : Type) : Type :=
  | TransformerMod (ts : TransformerState Th)
  | ParserMod (ps : ParserState Th Tb)
  (* A deparser reuses the [ParserState] layout: it reads [p_header_map] and
     writes its emitted bits into [p_packet] (the packet is now an output). *)
  | DeparserMod (ps : ParserState Th Tb).

Arguments TransformerMod {Th Tb} _.
Arguments ParserMod {Th Tb} _.
Arguments DeparserMod {Th Tb} _.

(* The shared inter-module interface: every module exposes a header map. *)
Definition module_header_map {Th Tb} (m : ModuleState Th Tb) : PMap.t Th :=
  match m with
  | TransformerMod ts => t_header_map ts
  | ParserMod ps      => p_header_map ps
  | DeparserMod ps    => p_header_map ps
  end.

(* Replace a module's header map (used when piping the packet downstream). *)
Definition set_module_header_map {Th Tb} (m : ModuleState Th Tb) (packet : PMap.t Th)
    : ModuleState Th Tb :=
  match m with
  | TransformerMod ts => TransformerMod (inject_headers packet ts)
  | ParserMod ps      => ParserMod {| p_header_map := packet;
                                      p_packet     := p_packet ps;
                                      p_cursor     := p_cursor ps |}
  | DeparserMod ps    => DeparserMod {| p_header_map := packet;
                                        p_packet     := p_packet ps;
                                        p_cursor     := p_cursor ps |}
  end.

(* Feed an incoming packet into a module (used to thread the residual packet
   along the network).  A parser starts parsing the new packet from its head;
   a deparser will prepend its emitted bits to this incoming payload; a
   transformer has no packet, so it is left unchanged. *)
Definition set_module_packet {Th Tb} (m : ModuleState Th Tb) (pkt : list Tb)
    : ModuleState Th Tb :=
  match m with
  | TransformerMod ts => TransformerMod ts
  | ParserMod ps      => ParserMod {| p_header_map := p_header_map ps;
                                      p_packet     := pkt;
                                      p_cursor     := 0 |}
  | DeparserMod ps    => DeparserMod {| p_header_map := p_header_map ps;
                                        p_packet     := pkt;
                                        p_cursor     := 0 |}
  end.

Definition ConcreteModuleState := ModuleState CrVal bool.
Definition SymbolicModuleState := ModuleState SmtArithExpr (ConditionalVal SmtBoolExpr).
