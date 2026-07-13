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
From MyProject Require Import CrSymbolicSemanticsDeparser.
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
  | DeparserModule _ d, DeparserMod ps =>
      Some (DeparserMod (eval_deparser_symbolic d ps))
  | _, _ => None  (* module-kind / state-kind mismatch *)
  end.

(* ================================================================== *)
(* Accept-aware module / network semantics.                            *)
(*                                                                     *)
(* Symbolic execution is path-merged (one formula, no branching), so a  *)
(* parser [Reject] is not a control-flow abort — it is a symbolic        *)
(* predicate over the input bits.  This variant threads that predicate:  *)
(* each module yields its state plus an [SmtBoolExpr] accept condition,   *)
(* and the network folds their conjunction.  A parser contributes its     *)
(* [spr_accept] (via the total [eval_parser_symbolic_acc]); a transformer *)
(* and a deparser never reject, so they contribute [SmtTrue].             *)
(* ================================================================== *)

Definition eval_module_symbolic_acc (m : CrModule) (st : ModuleState SmtArithExpr SmtBoolExpr)
    : option (ModuleState SmtArithExpr SmtBoolExpr * SmtBoolExpr) :=
  match m, st with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      Some (TransformerMod (eval_transformer_smt t ts), SmtTrue)
  | ParserModule _ p, ParserMod ps =>
      let r := eval_parser_symbolic_acc p ps in
      (* Reuse the input packet/cursor (as [eval_parser_symbolic] does): under
         path merging the consumed length is data-dependent, so only the merged
         header map and the accept condition are meaningful here. *)
      Some (ParserMod {| p_header_map := spr_headers r;
                         p_packet     := p_packet ps;
                         p_cursor     := p_cursor ps |},
            spr_accept r)
  | DeparserModule _ d, DeparserMod ps =>
      Some (DeparserMod (eval_deparser_symbolic d ps), SmtTrue)
  | _, _ => None  (* module-kind / state-kind mismatch *)
  end.

Fixpoint eval_network_from_symbolic
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t SmtArithExpr)
    (f_pkt  : list SmtBoolExpr)
    (gs     : GeneralSymbolicState)
    (fuel   : nat)
    : option (GeneralSymbolicState) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    (* Feed this module both the upstream header map and the residual packet. *)
    let ls' := set_module_packet (set_module_header_map ls f_hdrs) f_pkt in
    match eval_module_symbolic m ls' with
    | None => None
    | Some ls'' =>
      let gs' := set_gps_mod_states gs (PMap.set (unwrap start) ls'' (mod_states gs)) in
      let f_hdrs' := module_header_map ls'' in
      (* Residual packet passed downstream (mirrors the concrete semantics):
         a parser hands on the bits past its cursor; a transformer flows it through. *)
      let f_pkt' := match ls'' with
                    | ParserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                    | DeparserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                    | TransformerMod _ => f_pkt
                    end in
      (* Recurse over downstream modules; on [], fold_left returns
          the seed [Some ms'] as is, which is the desired sink behaviour. *)
      List.fold_left
        (fun acc dst =>
          match acc with
          | None => None
          | Some gs_acc =>
              eval_network_from_symbolic
                net dst f_hdrs' f_pkt' gs_acc fuel'
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
    (* The network's input packet threads in from the shared bit map. *)
    let pkt_i := sh_bit_map gs in
    eval_network_from_symbolic
      net start hdr_i pkt_i gs fuel
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

(* Accept-aware analogue of [eval_network_from_symbolic]: identical header /
   packet threading, but also carries [acc], the conjunction of every module's
   accept condition along the path so far. *)
Fixpoint eval_network_from_symbolic_acc
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t SmtArithExpr)
    (f_pkt  : list SmtBoolExpr)
    (gs     : GeneralSymbolicState)
    (acc    : SmtBoolExpr)
    (fuel   : nat)
    : option (GeneralSymbolicState * SmtBoolExpr) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    let ls' := set_module_packet (set_module_header_map ls f_hdrs) f_pkt in
    match eval_module_symbolic_acc m ls' with
    | None => None
    | Some (ls'', a) =>
      (* Conjoin this module's accept condition into the running accumulator. *)
      let acc' := SmtBoolAnd acc a in
      let gs' := set_gps_mod_states gs (PMap.set (unwrap start) ls'' (mod_states gs)) in
      let f_hdrs' := module_header_map ls'' in
      let f_pkt' := match ls'' with
                    | ParserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                    | DeparserMod ps' => List.skipn (p_cursor ps') (p_packet ps')
                    | TransformerMod _ => f_pkt
                    end in
      List.fold_left
        (fun acc_opt dst =>
          match acc_opt with
          | None => None
          | Some (gs_acc, acc_cond) =>
              eval_network_from_symbolic_acc
                net dst f_hdrs' f_pkt' gs_acc acc_cond fuel'
          end)
        (downstream_modules net start)
        (Some (gs', acc'))
    end
  | _, _ => None
  end end.

Definition eval_general_program_symbolic_acc
  (p  : GeneralCaracaraProgram)
  (gs : GeneralSymbolicState)
  : option (GeneralSymbolicState * SmtBoolExpr) :=
  let net := get_network_from_general p in
  let fuel := List.length (net_modules net) in
  let start := start_module net in
  match (mod_states gs) ?? (unwrap start) with
  | None => None
  | Some start_state =>
    let hdr_i := module_header_map start_state in
    let pkt_i := sh_bit_map gs in
    (* Seed the accept accumulator with [SmtTrue] (an empty network accepts). *)
    eval_network_from_symbolic_acc net start hdr_i pkt_i gs SmtTrue fuel
  end.

Definition eval_general_program_symbolic_sinks_acc
  (p : GeneralCaracaraProgram)
  (module_states: GeneralSymbolicState)
  : option (list (ModuleState SmtArithExpr SmtBoolExpr) * SmtBoolExpr) :=
  match eval_general_program_symbolic_acc p module_states with
  | None => None
  | Some (ledger, acc) =>
      Some (get_sink_states (get_network_from_general p) (mod_states ledger), acc)
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
  | DeparserMod ps =>
      (* Same concretization as a parser state (a deparser reuses the layout). *)
      DeparserMod {| p_header_map :=
                       PMap.map (fun e => eval_smt_arith e f) (p_header_map ps);
                     p_packet := List.map (fun b => eval_smt_bool b f) (p_packet ps);
                     p_cursor := p_cursor ps |}
  end.

Definition concretize_sym_modnet_state (s: GeneralSymbolicState) (f : SmtValuation) : GeneralConcreteState :=
  {| sh_hdr_map := PMap.map (fun e => eval_smt_arith e f) (sh_hdr_map s);
     sh_bit_map := List.map (fun b => eval_smt_bool b f) (sh_bit_map s);
     mod_states := PMap.map (fun sym_st => concretize_sym_module_state sym_st f) (mod_states s) |}.
