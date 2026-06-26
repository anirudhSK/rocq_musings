From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrSymbolicSemanticsTransformer.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Symbolic module / network semantics, plus concretization of a       *)
(* symbolic network state under a valuation.                           *)
(* ================================================================== *)

Definition eval_module_symbolic (m : CrModule) (st : ModuleState SmtArithExpr SmtBoolExpr)
    : option (ModuleState SmtArithExpr SmtBoolExpr) :=
  match m, st with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      Some (TransformerMod (eval_transformer_smt t ts))
  | ParserModule _ p, ParserMod ps =>
      match eval_parser_symbolic p ps with
      | None => None
      | Some ps' => Some (ParserMod ps')
      end
  | _, _ => None  (* module-kind / state-kind mismatch *)
  end.

Fixpoint eval_network_from_symbolic
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t SmtArithExpr)
    (f_bits : PMap.t SmtArithExpr)
    (gs     : GeneralSymbolicState)
    (fuel   : nat)
    : option (GeneralSymbolicState) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    let ls' := set_module_header_map ls f_hdrs in
    match eval_module_symbolic m ls' with
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
              eval_network_from_symbolic
                net dst f_hdrs' f_bits' gs_acc fuel'
          end)
        (downstream_modules net start)
        (Some gs')
    end
  | _, _ => None
  end end.

Definition eval_general_program_symbolic
  (p  : GeneralCaracaraProgram)
  (gs : GeneralSymbolicState)
  : option (GeneralSymbolicState) :=
  let mods := net_modules (get_network_from_general p) in
  let fuel := List.length mods in
  let net := get_network_from_general p in
  let start := start_module net in
  match (mod_states gs) ?? (unwrap start) with
  | None => None
  | Some start_state =>
    let hdr_i := module_header_map start_state in
    (* [f_bits] is stubbed for now: seeded with nil and threaded through
       unchanged, mirroring [eval_general_program_concrete]. *)
    let bit_i := PMap.init (SmtArithConst CrNilInt) in
    eval_network_from_symbolic
      net start hdr_i bit_i gs fuel
  end.

Definition eval_general_program_symbolic_sinks
  (p : GeneralCaracaraProgram)
  (module_states: GeneralSymbolicState)
  : option (list (ModuleState SmtArithExpr SmtBoolExpr)) :=
  match eval_general_program_symbolic p module_states with
  | None => None
  | Some ledger =>
      Some (get_sink_states (get_network_from_general p) (mod_states ledger))
  end.

Definition concretize_sym_module_state (m : ModuleState SmtArithExpr SmtBoolExpr) (f : SmtValuation)
    : ModuleState CrVal bool :=
  match m with
  | TransformerMod ts => TransformerMod (eval_sym_state ts f)
  | ParserMod ps =>
      (* Concretize the header map (via [eval_smt_arith]) and the packet
         bits (via [eval_smt_bool]) under [f]; carry the cursor unchanged. *)
      ParserMod {| p_header_map :=
                     PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
                   p_packet := List.map (fun b => eval_smt_bool b f) (p_packet ps);
                   p_cursor := p_cursor ps |}
  end.

Definition concretize_sym_modnet_state (s: GeneralSymbolicState) (f : SmtValuation) : GeneralConcreteState :=
  {| sh_hdr_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map s);
     sh_bit_map := List.map (fun b => eval_smt_bool b f) (sh_bit_map s);
     mod_states := PMap.map (fun sym_st => concretize_sym_module_state sym_st f) (mod_states s) |}.
