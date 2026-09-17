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

(* ==================================================================== *)
(* Concrete module / network semantics.  Dispatches each module to its  *)
(* engine (transformer or parser FSM) and threads the shared header map *)
(* along the network's edges.                                           *)
(* ==================================================================== *)

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
    (* [None] is only the two incomplete-run cases (out of fuel, undefined
       state), which [well_formed_parser] rules out; a rejected packet arrives
       as [Some] with [pr_accept := false] and folds into [gps_valid] exactly
       as the symbolic side folds [pr_accept] in.  Structurally this branch is
       now the mirror of [eval_module_symbolic]'s. *)
    match eval_parser_concrete p ps with
    | Some r =>
      (* The module-local state records what the run PRODUCED, not what it was
         handed: the packet becomes the unconsumed tail, positioned at its
         start.  It used to keep [p_packet ps] and [p_cursor ps] -- the entry
         packet at the entry cursor -- so a parser module's own state claimed
         it had consumed nothing, however much it read.

         The cursor is 0 rather than the count consumed because the result
         record carries no cursor: symbolically the parse is path-merged and
         there is no single [nat] to record (which is why [pr_bits_read] is an
         expression).  What was consumed lives in [sh_bits_read], and the two
         evaluators agree on this shape. *)
      let ls' := ParserMod {| p_header_map := pr_headers r;
                              p_packet     := pr_residual r;
                              p_cursor     := 0 |} in
      let ms' := PMap.set (unwrap m_id) ls' (mod_states gs) in
      let f_hdrs' := pr_headers r in
      let rt' := pr_residual r in
      (* The cursor is what this parser consumed; the network-wide count is the
         running sum, since each parser reads from its predecessor's residual. *)
      let n' := add_at u64 (sh_bits_read gs) (pr_bits_read r) in
      set_gps_valid
        (set_gps_mod_states
          (set_gps_bits_read
            (set_gps_shared_read_tape
              (set_gps_shared_headers gs f_hdrs') rt') n') ms')
        (andb (gps_valid gs) (pr_accept r))
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

(* [None] means the NETWORK did not run to completion -- fuel exhausted, an
   edge naming a module that does not exist, or a module state of the wrong
   kind.  It does NOT mean the packet was rejected.

   A rejecting parser leaves [gps_valid := false] in the state and the
   remaining modules still run, exactly as they do symbolically (there is no
   validity guard in [eval_network_from_symbolic] either, because a symbolic
   [pr_accept] is a predicate that has no single truth value to branch on).
   This used to short-circuit to [None] on an invalid state, which made
   rejection indistinguishable from non-termination and left "both runs
   rejected" -- the first disjunct of [modnet_equivalence_checker_sound] --
   unreachable for any network whose parser is not also its sink.

   Running the downstream modules on an invalidated state is safe because
   nothing downstream can clear [gps_valid] back to true: every writer of it
   conjoins ([andb] here, [SmtBoolAnd] symbolically). *)
Fixpoint eval_network_from_concrete
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t CrVal)
    (f_bits : list bool)
    (gs     : GeneralConcreteState)
    (fuel   : nat)
    : option (GeneralConcreteState) :=
  match fuel with | O => None | S fuel' =>
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
  end end.

(* ------------------------------------------------------------------ *)
(* Memory safety of a completed run.

   A load or a store is TOTAL -- out of bounds reads ErrorVal and drops the
   write -- and deliberately so: making the individual access reject would put
   a validity condition on a memory op, which the symbolic side cannot express
   per-cell (see the note on [SmtArrSt] not being atomic).  What it does record
   is [sh_mem_extent]: per region, how many bytes of it the run required.  So
   the fault shows up here instead, once, at the end of the network: the run is
   valid only if every region it touched stayed inside its declared length.

   Every key with a binding is checked, not just the declared ones.  A key the
   program never declared has bound 0 in [region_len_map], so touching an
   undeclared region overruns it -- which is what "there is no such region"
   should mean.  Keys with no binding read the extent map's default, and that
   default is the initial zero: [PMap.set] is the only writer and it never
   moves the default, so an unbound key is a region nothing ever touched.

   [negb (ltb bound extent)] rather than an [le] test because [CrVal.ltb] is
   what exists and is type-checked: both sides are u64 here, extents being
   normalised to u64 by [as_offset]/[byte_addr].  It also fail-OPEN on a
   non-integer extent -- but no extent can be one, since [bump_extent_concrete]
   keeps the previous value whenever [ltb] says no, and the initial value is
   [mk_int u64 0]. *)
Definition mem_extents_in_bounds_concrete
  (rs : list MemRegionDecl) (ext : PMap.t CrVal) : bool :=
  let lens := region_len_map rs in
  List.forallb
    (fun k => negb (CrVal.ltb (mk_int u64 (Z.of_nat (lens !! k))) (ext !! k)))
    (pmap_keys ext).

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
    match eval_network_from_concrete
            net start (sh_hdr_map gs) (sh_read_tape gs) gs fuel with
    | None => None
    | Some gs' =>
      (* Conjoined, like every other writer of [gps_valid] -- a run that
         rejected stays rejected, and one that overran memory is rejected now.
         Extents only grow, so the final map is the whole run's reach and one
         check at the end covers every access.  [None] still means only that
         the network did not run to completion. *)
      Some (set_gps_valid gs'
              (andb (gps_valid gs')
                    (mem_extents_in_bounds_concrete
                       (get_mem_regions_from_general p) (sh_mem_extent gs'))))
    end
  end.
