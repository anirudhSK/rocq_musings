From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsDeparser.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Symbolic module / network semantics, plus concretization of a       *)
(* symbolic network state under a valuation.                           *)
(*                                                                     *)
(* This is the symbolic mirror of [CrConcreteSemanticsModule].  It      *)
(* dispatches each module to its symbolic engine and threads the shared  *)
(* header map and read/write tapes along the network's edges.  Two       *)
(* differences from the concrete semantics follow from path-merging:     *)
(*   - a parser never fail-closes; its (data-dependent) accept condition  *)
(*     is conjoined into [gps_valid] instead of aborting the network;     *)
(*   - correspondingly there is no [gps_valid] guard on the network        *)
(*     recursion (the validity is a symbolic formula, not a decidable      *)
(*     bool), so execution always proceeds and merges every path.          *)
(* ================================================================== *)

Definition module_update_gs_symbolic
  (m : CrModule) (ls : SymbolicModuleState)
  (gs : GeneralSymbolicState) : GeneralSymbolicState :=
  match m, ls with
  | TransformerModule m_id _ _ t, TransformerMod ts =>
    (* Mirrors the concrete side: memory is forwarded in from the general state
       and copied back out. *)
    let r := eval_transformer_smt_mem t
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
    let r := eval_parser_symbolic p ps in
    let ls' := ParserMod {| p_header_map := spr_headers r;
                            p_packet     := p_packet ps;
                            p_cursor     := p_cursor ps |} in
    let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
    let f_hdrs' := spr_headers r in
    let rt' := spr_residual r in
    (* Fold the accept condition into the running validity, rather than
       fail-closing as the concrete [None] branch does. *)
    let v' := {| cvc := cvc (gps_valid gs);
                 cvv := SmtBoolAnd (cvv (gps_valid gs)) (spr_accept r) |} in
    (* Mirrors the concrete [add_at u64]: the network-wide count is the running
       sum of what each parser in the chain consumed. *)
    let n' := SmtBitAdd u64 (sh_bits_read gs) (spr_bits_read r) in
    set_gps_valid
      (set_gps_bits_read
        (set_gps_mod_states
          (set_gps_shared_read_tape
            (set_gps_shared_headers gs f_hdrs') rt') ms') n')
      v'
  | DeparserModule m_id d, DeparserMod ds =>
    let ds' := eval_deparser_symbolic d ds in
    let ls' := DeparserMod ds' in
    let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
    (* Mirrors the concrete side: append rather than replace, so several
       deparsers concatenate their output in run order. *)
    let wt' := sh_write_tape gs ++ p_packet ds' in
    set_gps_mod_states
      (set_gps_shared_write_tape gs wt') ms'
  | _, _ => set_gps_valid gs {| cvc := SmtTrue; cvv := SmtFalse |}
  end.

Fixpoint eval_network_from_symbolic
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t SmtArithExpr)
    (f_bits : list (ConditionalVal SmtBoolExpr))
    (gs     : GeneralSymbolicState)
    (fuel   : nat)
    : option (GeneralSymbolicState) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    let ls' := set_module_packet (set_module_header_map ls f_hdrs) f_bits in
    let gs' := module_update_gs_symbolic m ls' gs in
    List.fold_left
      (fun acc dst =>
        match acc with
        | None => None
        | Some gs_acc =>
            eval_network_from_symbolic
              net dst (sh_hdr_map gs') (sh_read_tape gs') gs_acc fuel'
        end)
      (downstream_modules net start)
      (Some gs')
  | _, _ => None
  end end.

Definition eval_general_program_symbolic
  (p  : GeneralCaracaraProgram)
  (gs : GeneralSymbolicState)
  : option (GeneralSymbolicState) :=
  let net := get_network_from_general p in
  let fuel := List.length (net_modules net) in
  let start := start_module net in
  match (mod_states gs) ?? (unwrap start) with
  | None => None
  | Some start_state =>
    (* The input packet threads in from the shared read tape. *)
    eval_network_from_symbolic
      net start (sh_hdr_map gs) (sh_read_tape gs) gs fuel
  end.

(* ================================================================== *)
(* Concretization of a symbolic network state under a valuation.       *)
(*                                                                     *)
(* The mirror of [eval_sym_state] (transformers) lifted to the whole    *)
(* network: every symbolic header value runs through [eval_smt_arith],  *)
(* every symbolic packet bit's value through [eval_smt_bool], and the    *)
(* validity through [eval_smt_bool] on its [cvv].  The result is a       *)
(* [GeneralConcreteState], so equivalence can be stated over concretized *)
(* outputs (see [SmtModuleQuery.modnet_equivalence_checker_sound]).      *)
(* ================================================================== *)

Definition concretize_sym_module_state
  (m : SymbolicModuleState) (f : SmtValuation) : ConcreteModuleState :=
  match m with
  | TransformerMod ts => TransformerMod (eval_sym_state ts f)
  | ParserMod ps =>
      ParserMod {| p_header_map :=
                     PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
                   p_packet := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet ps);
                   p_cursor := p_cursor ps |}
  | DeparserMod ps =>
      DeparserMod {| p_header_map :=
                       PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
                     p_packet := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet ps);
                     p_cursor := p_cursor ps |}
  end.

Definition concretize_sym_modnet_state
  (s : GeneralSymbolicState) (f : SmtValuation) : GeneralConcreteState :=
  {| sh_hdr_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map s);
     sh_read_tape := List.map (fun b => eval_smt_bool (cvv b) f) (sh_read_tape s);
     sh_bits_read := eval_smt_arith (sh_bits_read s) f;
     sh_write_tape := List.map (fun b => eval_smt_bool (cvv b) f) (sh_write_tape s);
     sh_mem := PMap.map (fun a => eval_smt_mem a f) (sh_mem s);
     sh_mem_extent := PMap.map (fun e => eval_smt_arith e f) (sh_mem_extent s);
     mod_states := PMap.map (fun sym_st => concretize_sym_module_state sym_st f) (mod_states s);
     gps_valid := eval_smt_bool (cvv (gps_valid s)) f |}.
