From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrConcreteSemanticsDeparser.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Concrete module / network semantics.  Dispatches each module to its  *)
(* engine (transformer or parser FSM) and threads the shared header map  *)
(* along the network's edges.                                          *)
(* ================================================================== *)

Definition module_update_gs_concrete
  (m : CrModule) (ls : ConcreteModuleState)
  (gs : GeneralConcreteState) : GeneralConcreteState :=
  match m, ls with
  | TransformerModule m_id _ _ t, TransformerMod ts =>
    (* Memory is forwarded in from the general state and copied back out, the
       same shape as the header map.  Unlike the header map it is not also
       passed along the network's edges: memory is global machine state, not a
       value carried on an edge.  Under the linear-chain assumption the two are
       the same thing; with fan-out they would not be, which is one more reason
       [is_linear_chain] is a precondition of the equivalence lemmas. *)
    let r := eval_transformer_concrete_mem t
               {| mc_mem := sh_mem gs; mc_extent := sh_mem_extent gs |} ts in
    let mc' := fst r in
    let ls' := TransformerMod (snd r) in
    let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
    let f_hdrs' := module_header_map ls' in
    set_gps_mod_states
      (set_gps_mem_extent
        (set_gps_mem
          (set_gps_shared_headers gs f_hdrs') (mc_mem mc')) (mc_extent mc')) ms'
  | ParserModule m_id p, ParserMod ps =>
    match eval_parser_concrete p ps with
    | Some ps' =>
      let ls' := ParserMod ps' in
      let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
      let f_hdrs' := module_header_map ls' in
      let rt' := List.skipn (p_cursor ps') (p_packet ps') in
      (* The cursor is what this parser consumed; the network-wide count is the
         running sum, since each parser reads from its predecessor's residual. *)
      let n' := add_at u64 (sh_bits_read gs) (mk_int u64 (Z.of_nat (p_cursor ps'))) in
      set_gps_mod_states
        (set_gps_bits_read
        (set_gps_shared_read_tape
        (set_gps_shared_headers gs f_hdrs') rt') n') ms'
    | None => set_gps_valid gs false
    end
  | DeparserModule m_id d, DeparserMod ds =>
    (* Total, unlike the parser: see [eval_deparser_concrete] for why a deparser
       has no validity condition on either the concrete or the symbolic side. *)
    let ds' := eval_deparser_concrete d ds in
    let ls' := DeparserMod ds' in
    let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
    (* APPEND to the write tape rather than replace it, so a network with more
       than one deparser emits the concatenation of what each wrote, in the
       order they run.  The tape starts empty, so a single-deparser network is
       unaffected.  [eval_deparser_symbolic]'s caller mirrors this. *)
    let wt' := sh_write_tape gs ++ p_packet ds' in
    set_gps_mod_states
      (set_gps_shared_write_tape gs wt') ms'
  | _, _ => set_gps_valid gs false
  end.

Fixpoint eval_network_from_concrete
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t CrVal)
    (f_bits : list bool)
    (gs     : GeneralConcreteState)
    (fuel   : nat)
    : option (GeneralConcreteState) :=
  match fuel with | O => None | S fuel' =>
  match gps_valid gs with | false => None | true =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    let ls' := set_module_packet (set_module_header_map ls f_hdrs) f_bits in
    let gs' := module_update_gs_concrete m ls' gs in
    List.fold_left
      (fun acc dst =>
        match acc with
        | None => None
        | Some gs_acc =>
            eval_network_from_concrete
              net dst (sh_hdr_map gs') (sh_read_tape gs') gs_acc fuel'
        end)
      (downstream_modules net start)
      (Some gs')
  | _, _ => None
  end end end.

Definition eval_general_program_concrete
  (p  : GeneralCaracaraProgram)
  (gs : GeneralConcreteState)
  : option (GeneralConcreteState) :=
  let mods := net_modules (get_network_from_general p) in
  let fuel := List.length mods in
  let net := get_network_from_general p in
  let start := start_module net in
  match (mod_states gs) ?? (unwrap start) with
  | None => None
  | Some start_state =>
    (* The input packet threads in from the shared read tape. *)
    eval_network_from_concrete
      net start (sh_hdr_map gs) (sh_read_tape gs) gs fuel
  end.
