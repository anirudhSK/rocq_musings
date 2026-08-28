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

(* ===================================================================== *)
(* Symbolic module / network semantics, plus concretization of a         *)
(* symbolic network state under a valuation.                             *)
(*                                                                       *)
(* This is the symbolic mirror of [CrConcreteSemanticsModule].  It       *)
(* dispatches each module to its symbolic engine and threads the shared  *)
(* header map and read/write tapes along the network's edges.  Two       *)
(* differences from the concrete semantics follow from path-merging:     *)
(*   - a parser never fail-closes; its (data-dependent) accept condition *)
(*     is conjoined into [gps_valid] instead of aborting the network;    *)
(*   - correspondingly there is no [gps_valid] guard on the network      *)
(*     recursion (the validity is a symbolic formula, not a decidable    *)
(*     bool), so execution always proceeds and merges every path.        *)
(* ===================================================================== *)

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
    (* Mirrors the concrete side: the module-local state holds the unconsumed
       tail at cursor 0, not the entry packet at the entry cursor.  See the
       comment in [module_update_gs_concrete] for why the cursor is 0 rather
       than the amount consumed. *)
    let ls' := ParserMod {| p_header_map := pr_headers r;
                            p_packet     := pr_residual r;
                            p_cursor     := 0 |} in
    let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
    let f_hdrs' := pr_headers r in
    let rt' := pr_residual r in
    (* Fold the accept condition into the running validity, rather than
       fail-closing as the concrete [None] branch does. *)
    let v' := {| cvc := cvc (gps_valid gs);
                 cvv := SmtBoolAnd (cvv (gps_valid gs)) (pr_accept r) |} in
    (* Mirrors the concrete [add_at u64]: the network-wide count is the running
       sum of what each parser in the chain consumed. *)
    let n' := SmtBitAdd u64 (sh_bits_read gs) (pr_bits_read r) in
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

(* Mirror of [mem_extents_in_bounds_concrete], node for node: the same fold
   over the same key set, with [SmtBoolNot (SmtBoolLt ...)] where the concrete
   side has [negb (CrVal.ltb ...)] and the same u64 bound constant.  The two
   agree under [eval_smt_bool] because [SmtBoolLt] evaluates to [CrVal.ltb] and
   [SmtArithConst (mask_width W64 n) u64] to [mk_int u64 n].

   The key set is the SYMBOLIC extent map's, which is the concrete one's:
   [concretize_sym_modnet_state] maps [sh_mem_extent] pointwise, and [PMap.map]
   preserves bindings. *)
Definition mem_extents_in_bounds_smt
  (rs : list MemRegionDecl) (ext : PMap.t SmtArithExpr) : SmtBoolExpr :=
  let lens := region_len_map rs in
  List.fold_right
    (fun k acc =>
      SmtBoolAnd acc
        (SmtBoolNot
          (SmtBoolLt (SmtArithConst (mask_width W64 (Z.of_nat (lens !! k))) u64)
                     (ext !! k))))
    SmtTrue (pmap_keys ext).

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
    match eval_network_from_symbolic
            net start (sh_hdr_map gs) (sh_read_tape gs) gs fuel with
    | None => None
    | Some gs' =>
      (* Mirrors the concrete side: the memory-safety condition is conjoined
         into the final validity, in the same [SmtBoolAnd] shape every other
         writer of [gps_valid] uses.  [cvc] is untouched -- it says whether the
         flag is there, not what it is. *)
      Some (set_gps_valid gs'
              {| cvc := cvc (gps_valid gs');
                 cvv := SmtBoolAnd (cvv (gps_valid gs'))
                          (mem_extents_in_bounds_smt
                             (get_mem_regions_from_general p)
                             (sh_mem_extent gs')) |})
    end
  end.

(* ===================================================================== *)
(* Concretization of a symbolic network state under a valuation.         *)
(*                                                                       *)
(* The mirror of [eval_sym_state] (transformers) lifted to the whole     *)
(* network: every symbolic header value runs through [eval_smt_arith],   *)
(* every symbolic packet bit's value through [eval_smt_bool], and the    *)
(* validity through [eval_smt_bool] on its [cvv].  The result is a       *)
(* [GeneralConcreteState], so equivalence can be stated over concretized *)
(* outputs (see [SmtModuleQuery.modnet_equivalence_checker_sound]).      *)
(* ===================================================================== *)

Definition concretize_sym_module_state
  (m : SymbolicModuleState) (f : SmtValuation) : ConcreteModuleState :=
  match m with
  | TransformerMod ts => TransformerMod (eval_sym_state ts f)
  | ParserMod ps =>
      (* A parser module's local packet is its residual (see
         [module_update_gs_symbolic]), so it is a read tape and concretizes
         like one -- through [present_bits], which is what
         [eval_sym_parser_state] does. *)
      ParserMod (eval_sym_parser_state ps f)
  | DeparserMod ps =>
      DeparserMod {| p_header_map :=
                       PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
                     (* Positional, unlike the parser case: a deparser's local
                        packet is what it EMITTED, and every emitted bit is
                        present ([eval_deparser_symbolic] sets [cvc := SmtTrue]
                        on all of them). *)
                     p_packet := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet ps);
                     p_cursor := p_cursor ps |}
  end.

Definition concretize_sym_modnet_state
  (s : GeneralSymbolicState) (f : SmtValuation) : GeneralConcreteState :=
  {| sh_hdr_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map s);
     (* Present positions only -- see [present_bits]. *)
     sh_read_tape := present_bits (sh_read_tape s) f;
     sh_bits_read := eval_smt_arith (sh_bits_read s) f;
     (* Positional, deliberately: every emitted bit is present by
        [wt_unconditional], and [sym_out_equal_sound] compares them that way. *)
     sh_write_tape := List.map (fun b => eval_smt_bool (cvv b) f) (sh_write_tape s);
     sh_mem := PMap.map (fun a => eval_smt_mem a f) (sh_mem s);
     sh_mem_extent := PMap.map (fun e => eval_smt_arith e f) (sh_mem_extent s);
     mod_states := PMap.map (fun sym_st => concretize_sym_module_state sym_st f) (mod_states s);
     gps_valid := eval_smt_bool (cvv (gps_valid s)) f |}.
