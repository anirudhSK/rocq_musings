From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Concrete module / network semantics.  Dispatches each module to its  *)
(* engine (transformer or parser FSM) and threads the shared header map  *)
(* along the network's edges.                                          *)
(* ================================================================== *)

Definition eval_module_concrete (m : CrModule) (st : ModuleState CrVal bool)
    : option (ModuleState CrVal bool) :=
  match m, st with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      Some (TransformerMod (eval_transformer_concrete t ts))
  | ParserModule _ p, ParserMod ps =>
      match eval_parser_concrete p ps with
      | None => None
      | Some ps' => Some (ParserMod ps')
      end
  | _, _ => None  (* module-kind / state-kind mismatch *)
  end.

Fixpoint eval_network_from_concrete
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t CrVal)
    (f_bits : PMap.t CrVal)
    (gs     : GeneralConcreteState)
    (fuel   : nat)
    : option (GeneralConcreteState) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    let ls' := set_module_header_map ls f_hdrs in
    match eval_module_concrete m ls' with
    | None => None
    | Some ls'' =>
      let gs' := set_gps_mod_states gs (PMap.set (unwrap start) ls'' (mod_states gs)) in
      let f_hdrs' := module_header_map ls'' in
      let f_bits' := f_bits in
      (* Recurse over downstream modules; on [], fold_left returns
          the seed [Some ms'] as is, which is the desired sink behaviour. *)
      List.fold_left
        (fun acc dst =>
          match acc with
          | None => None
          | Some gs_acc =>
              eval_network_from_concrete
                net dst f_hdrs' f_bits' gs_acc fuel'
          end)
        (downstream_modules net start)
        (Some gs')
    end
  | _, _ => None
  end end.

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
    let hdr_i := module_header_map start_state in
    let bit_i := PMap.init (IntVal CrNilInt) in
    eval_network_from_concrete
      net start hdr_i bit_i gs fuel
  end.

Definition eval_general_program_concrete_sinks
  (p : GeneralCaracaraProgram)
  (module_states : GeneralConcreteState)
  : option (list (ModuleState CrVal bool)) :=
  match eval_general_program_concrete p module_states with
  | None        => None
  | Some ledger =>
      Some (get_sink_states (get_network_from_general p) (mod_states ledger))
  end.
