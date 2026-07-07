From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrParser.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrVal.
From MyProject Require Import Maps.
From MyProject Require Import Integers.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Symbolic parser FSM semantics.                                      *)
(*                                                                     *)
(* Mirrors the concrete parser FSM (CrConcreteSemanticsParser) but,     *)
(* like the symbolic transformer, never path-splits: data-dependent     *)
(* [select] control flow is merged into a single symbolic header map    *)
(* using [SmtConditional], exactly as [eval_transformer_smt] does for    *)
(* match-action rules.                                                  *)
(* ================================================================== *)

(* Parsed fields are typed [u64] (see [apply_extract_concrete]).  A field is the
   [SmtBitsToInt] of its packet-bit slice (MSB first); this denotes the same
   [u64] value as the concrete [mk_int u64 (bits_to_Z ...)] but lowers to a
   bitvector [concat] in Z3 instead of an arithmetic assembly chain. *)

(* Apply a symbolic extraction at the current cursor.  Fails ([None]) if
   the slice runs past the (statically known) end of the packet.  Mirrors
   [apply_extract_concrete], assembling symbolic bits instead of concrete ones.
   ([CrParser.bit_slice] is fixed to [list bool], so we slice inline.) *)
Definition apply_extract_symbolic (eo : ExtractOp) (ps : SymbolicParserState)
    : option SymbolicParserState :=
  match eo with
  | ExtractOpConstructor h width =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        let slice := List.firstn width (List.skipn (p_cursor ps) (p_packet ps)) in
        let v := SmtBitsToInt slice in
        Some {| p_header_map := PMap.set (get_key h) v (p_header_map ps);
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  end.

(* The symbolic condition under which a [select] case fires: header
   [sc_header]'s current value equals the pattern's denoted value. *)
Definition select_case_cond_symbolic (ps : SymbolicParserState) (c : SelectCase)
    : SmtBoolExpr :=
  let pat_v := mk_int u64 (bits_to_Z (sc_pattern c)) in
  match pat_v with
  | IntVal k kty => SmtBoolEq (lookup_varlike_map (p_header_map ps) (sc_header c))
                              (SmtArithConst k kty)
  | _ => SmtFalse
  end.

(* Merge two header maps under [cond]: each header becomes
   [SmtConditional cond then_val else_val].  Keys are taken from [m_then]
   (the two maps share the same header domain in practice). *)
Definition merge_header_maps (cond : SmtBoolExpr)
    (m_then m_else : PMap.t SmtArithExpr) : PMap.t SmtArithExpr :=
  (fst m_then,
   PTree.map (fun k v_then =>
                let v_else := PMap.get k m_else in
                SmtConditional cond v_then v_else)
             (snd m_then)).

(* Merge all [select] cases into one symbolic header map, given a
   continuation [run_tgt] that resolves a single target at the current fuel
   level.  Each case's resulting map is merged under its firing condition;
   a branch that fails ([None]) falls back to [ps]'s current headers.
   Structurally recursive on [cases]. *)
Fixpoint resolve_select_symbolic
    (run_tgt : ParserTarget -> option (PMap.t SmtArithExpr))
    (ps : SymbolicParserState)
    (cases : list SelectCase) (default : ParserTarget)
    : PMap.t SmtArithExpr :=
  match cases with
  | [] =>
      match run_tgt default with
      | Some m => m
      | None => p_header_map ps
      end
  | c :: rest =>
      let cond := select_case_cond_symbolic ps c in
      let then_map :=
        match run_tgt (sc_target c) with
        | Some m => m
        | None => p_header_map ps
        end in
      let else_map := resolve_select_symbolic run_tgt ps rest default in
      merge_header_maps cond then_map else_map
  end.

(* Run the parser FSM symbolically from [lbl], returning the merged
   symbolic header map for the subtree.  [fuel] bounds state visits.
   On [Reject], a missing state, failed extraction, or fuel exhaustion the
   branch yields [None]; a [None] branch within a [select] contributes the
   pre-branch header values. *)
Fixpoint run_parser_symbolic (p : Parser) (lbl : ParserStateLabel)
    (ps : SymbolicParserState) (fuel : nat)
    : option (PMap.t SmtArithExpr) :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_state p lbl with
      | None => None
      | Some d =>
          let ps_extracted :=
            match psd_extract d with
            | None => Some ps
            | Some eo => apply_extract_symbolic eo ps
            end in
          match ps_extracted with
          | None => None
          | Some ps' =>
              let run_tgt := fun (tgt : ParserTarget) =>
                match tgt with
                | Accept => Some (p_header_map ps')
                | Reject => None
                | TargetState next => run_parser_symbolic p next ps' fuel'
                end in
              match psd_trans d with
              | Unconditional tgt => run_tgt tgt
              | Select cases default =>
                  Some (resolve_select_symbolic run_tgt ps' cases default)
              end
          end
      end
  end.

(* Same fuel as [eval_parser_concrete] — |states| * (|packet| + 1) — which must
   match for concrete/symbolic commutation ([concretize] preserves packet
   length).  Admits P4-style parser loops while guaranteeing termination. *)
Definition eval_parser_symbolic (p : Parser) (ps : SymbolicParserState)
    : option SymbolicParserState :=
  match run_parser_symbolic p (parser_start p) ps
          (List.length (parser_states p) * S (List.length (p_packet ps))) with
  | None => None
  | Some hm => Some {| p_header_map := hm;
                       p_packet     := p_packet ps;
                       p_cursor     := p_cursor ps |}
  end.

(* ================================================================== *)
(* Accept-aware symbolic parser semantics.                             *)
(*                                                                     *)
(* The [run_parser_symbolic] above merges a [Reject] branch as leaving  *)
(* the headers unchanged, which loses the accept/reject outcome — fine  *)
(* for feeding a downstream module, but useless for equivalence, where  *)
(* two parsers may differ precisely in when they reject.  This variant  *)
(* threads an [spr_accept] condition (a [SmtBoolExpr] over the packet    *)
(* bits) alongside the merged header map, so a caller can ask both       *)
(* whether the parsers accept the same packets and, when both accept,    *)
(* whether the headers agree.                                           *)
(* ================================================================== *)

Record SymParserResult : Type := mkSymParserResult {
  spr_accept  : SmtBoolExpr;          (* condition under which the parse accepts *)
  spr_headers : PMap.t SmtArithExpr;  (* final header values (used when accept holds) *)
}.

(* Boolean if-then-else, since [SmtConditional] only builds arith exprs. *)
Definition smt_bool_ite (c a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd c a) (SmtBoolAnd (SmtBoolNot c) b).

(* Merge two results under [cond]: accept conditions combine with a boolean
   ite, header maps with the existing [merge_header_maps]. *)
Definition merge_results (cond : SmtBoolExpr) (r_then r_else : SymParserResult)
    : SymParserResult :=
  {| spr_accept  := smt_bool_ite cond (spr_accept r_then) (spr_accept r_else);
     spr_headers := merge_header_maps cond (spr_headers r_then) (spr_headers r_else) |}.

(* Accept-aware analogue of [resolve_select_symbolic]; [run_tgt] is now total
   (a target always yields a result — [Reject] just carries [SmtFalse]). *)
Fixpoint resolve_select_symbolic_acc
    (run_tgt : ParserTarget -> SymParserResult)
    (ps : SymbolicParserState)
    (cases : list SelectCase) (default : ParserTarget)
    : SymParserResult :=
  match cases with
  | [] => run_tgt default
  | c :: rest =>
      let cond := select_case_cond_symbolic ps c in
      merge_results cond (run_tgt (sc_target c))
                    (resolve_select_symbolic_acc run_tgt ps rest default)
  end.

(* Accept-aware analogue of [run_parser_symbolic].  Total (never [None]): a
   dead-end (missing state, failed extraction, fuel exhaustion, [Reject]) yields
   [spr_accept := SmtFalse] with the headers reached so far. *)
Fixpoint run_parser_symbolic_acc (p : Parser) (lbl : ParserStateLabel)
    (ps : SymbolicParserState) (fuel : nat) : SymParserResult :=
  let reject := mkSymParserResult SmtFalse (p_header_map ps) in
  match fuel with
  | O => reject
  | S fuel' =>
      match lookup_state p lbl with
      | None => reject
      | Some d =>
          let ps_extracted :=
            match psd_extract d with
            | None => Some ps
            | Some eo => apply_extract_symbolic eo ps
            end in
          match ps_extracted with
          | None => reject
          | Some ps' =>
              let run_tgt := fun (tgt : ParserTarget) =>
                match tgt with
                | Accept => mkSymParserResult SmtTrue  (p_header_map ps')
                | Reject => mkSymParserResult SmtFalse (p_header_map ps')
                | TargetState next => run_parser_symbolic_acc p next ps' fuel'
                end in
              match psd_trans d with
              | Unconditional tgt => run_tgt tgt
              | Select cases default =>
                  resolve_select_symbolic_acc run_tgt ps' cases default
              end
          end
      end
  end.

Definition eval_parser_symbolic_acc (p : Parser) (ps : SymbolicParserState)
    : SymParserResult :=
  run_parser_symbolic_acc p (parser_start p) ps
    (List.length (parser_states p) * S (List.length (p_packet ps))).

(* Concretize a symbolic parser state under a valuation [f]: the parser analogue
   of [eval_sym_state] for transformers.  Every symbolic header value runs
   through [eval_smt_arith f] and every symbolic packet bit through
   [eval_smt_bool f]; the cursor is unchanged.  [List.map] preserves the packet
   length, so [eval_sym_parser_state] of an [n]-bit symbolic packet is an [n]-bit
   concrete one. *)
Definition eval_sym_parser_state (s : SymbolicParserState) (f : SmtValuation)
    : ConcreteParserState :=
  {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map s);
     p_packet     := List.map (fun b => eval_smt_bool b f) (p_packet s);
     p_cursor     := p_cursor s |}.
