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
(* ================================================================== *)

Definition eval_module_symbolic (m : CrModule) (st : ModuleState SmtArithExpr SmtBoolExpr)
    : option (ModuleState SmtArithExpr SmtBoolExpr) :=
  match m, st with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      Some (TransformerMod (eval_transformer_smt t ts))
  | ParserModule _ p, ParserMod ps =>
      (* Accept-aware parser step.  [eval_parser_symbolic] is total; we
         fail-close ([None], aborting the network exactly as the concrete
         [eval_parser_concrete] reject does) only on a statically-certain
         reject — [spr_accept] literally [SmtFalse], i.e. every path is an
         unconditional [Reject] / dead-end.  Otherwise the merged header map
         ([spr_headers]) flows on; a *data-dependent* reject is retained as
         the [spr_accept] predicate (used by the bitstream checker, dropped
         by the header-observable path). *)
      let r := eval_parser_symbolic p ps in
      match spr_accept r with
      | SmtFalse => None
      | _ =>
          Some (ParserMod {| p_header_map := spr_headers r;
                             p_packet     := p_packet ps;
                             p_cursor     := p_cursor ps |})
      end
  | DeparserModule _ d, DeparserMod ps =>
      Some (DeparserMod (eval_deparser_symbolic d ps))
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

(* ================================================================== *)
(* Accept-aware, bitstream-carrying network semantics.                 *)
(*                                                                     *)
(* Symbolic execution is path-merged (one formula, no branching), so a  *)
(* parser [Reject] is a symbolic predicate over the input bits, not a    *)
(* control-flow abort; and the number of bits a parser consumes is data- *)
(* dependent, so the residual it leaves has a data-dependent length.     *)
(* This path threads both: each module yields (updated headers, an        *)
(* accept condition, an outgoing residual bitstream [SymBitstream]).  The  *)
(* network conjoins the accept conditions and carries the residual to the  *)
(* sink, whose deparser prepends its emitted bits.  Reject is modelled as  *)
(* [spr_accept = SmtFalse]; the residual's [valid] channel carries the      *)
(* data-dependent length.                                                  *)
(* ================================================================== *)

(* A deparser's output bitstream: its emitted bits (all valid — they are
   freshly written) followed by the incoming residual. *)
Definition deparser_output_bitstream
    (d : Deparser) (hm : PMap.t SmtArithExpr) (residual : SymBitstream)
    : SymBitstream :=
  List.map (fun b => (b, SmtTrue))
           (List.flat_map (emit_bits_symbolic hm) (deparser_emits d))
  ++ residual.

(* One module, accept/bitstream-aware: returns its updated state, its accept
   condition, and its outgoing residual bitstream.  A parser reads the incoming
   residual as a validity-annotated bitstream: it extracts the bits but its
   accept condition also requires every extracted position to be VALID (via
   [eval_parser_symbolic_v]), and the residual it emits carries the incoming
   validity forward ([eval_parser_residual_v]).  This models CHAINED parsers
   exactly — a parser reading an upstream parser's data-dependent residual will
   not treat padding as real bits.  With an all-valid source packet the validity
   guard is vacuous, so this matches the single-source-parser behaviour.  A
   transformer flows the residual through; a deparser writes ahead of it. *)
Definition eval_module_bitstream_acc
    (m : CrModule) (ls : ModuleState SmtArithExpr SmtBoolExpr)
    (f_hdrs : PMap.t SmtArithExpr) (f_bits : SymBitstream)
    : option (ModuleState SmtArithExpr SmtBoolExpr * SmtBoolExpr * SymBitstream) :=
  let ls' := set_module_packet (set_module_header_map ls f_hdrs)
                               (List.map fst f_bits) in
  match m, ls' with
  | TransformerModule _ _ _ t, TransformerMod ts =>
      Some (TransformerMod (eval_transformer_smt t ts), SmtTrue, f_bits)
  | ParserModule _ p, ParserMod ps =>
      let validity := List.map snd f_bits in
      let r := eval_parser_symbolic_v p ps validity in
      Some (ParserMod {| p_header_map := spr_headers r;
                         p_packet     := p_packet ps;
                         p_cursor     := p_cursor ps |},
            spr_accept r,
            eval_parser_residual_v p ps validity)
  | DeparserModule _ d, DeparserMod ps =>
      Some (DeparserMod (eval_deparser_symbolic d ps), SmtTrue,
            deparser_output_bitstream d (p_header_map ps) f_bits)
  | _, _ => None  (* module-kind / state-kind mismatch *)
  end.

(* Thread headers, the conjoined accept condition [acc], and the residual
   bitstream [f_bits] along the network; return the accumulated ledger, the
   network accept condition, and the bitstream leaving the sink module. *)
Fixpoint eval_network_bitstream_acc
    (net    : ModuleNetwork)
    (start  : ModuleName)
    (f_hdrs : PMap.t SmtArithExpr)
    (f_bits : SymBitstream)
    (gs     : GeneralSymbolicState)
    (acc    : SmtBoolExpr)
    (fuel   : nat)
    : option (GeneralSymbolicState * SmtBoolExpr * SymBitstream) :=
  match fuel with | O => None | S fuel' =>
  match lookup_module net start, (mod_states gs) ?? (unwrap start) with
  | Some m, Some ls =>
    match eval_module_bitstream_acc m ls f_hdrs f_bits with
    | None => None
    | Some (ls'', a, out_bits) =>
      let acc' := SmtBoolAnd acc a in
      let gs' := set_gps_mod_states gs (PMap.set (unwrap start) ls'' (mod_states gs)) in
      let f_hdrs' := module_header_map ls'' in
      match downstream_modules net start with
      (* Sink: its outgoing bitstream is the network's observable output. *)
      | [] => Some (gs', acc', out_bits)
      | dsts =>
          List.fold_left
            (fun acc_opt dst =>
              match acc_opt with
              | None => None
              | Some (gs_acc, acc_cond, _) =>
                  eval_network_bitstream_acc
                    net dst f_hdrs' out_bits gs_acc acc_cond fuel'
              end)
            dsts
            (Some (gs', acc', out_bits))
      end
    end
  | _, _ => None
  end end.

Definition eval_general_program_bitstream_acc
  (p  : GeneralCaracaraProgram)
  (gs : GeneralSymbolicState)
  : option (list (ModuleState SmtArithExpr SmtBoolExpr) * SmtBoolExpr * SymBitstream) :=
  let net := get_network_from_general p in
  let fuel := List.length (net_modules net) in
  let start := start_module net in
  match (mod_states gs) ?? (unwrap start) with
  | None => None
  | Some start_state =>
    let hdr_i := module_header_map start_state in
    (* The input packet threads in from the shared bit map, all bits valid. *)
    let bits_i := List.map (fun b => (b, SmtTrue)) (sh_bit_map gs) in
    match eval_network_bitstream_acc net start hdr_i bits_i gs SmtTrue fuel with
    | None => None
    | Some (ledger, acc, out_bits) =>
        Some (get_sink_states net (mod_states ledger), acc, out_bits)
    end
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
