From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import SmtExpr.
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

(* Symbolic analogue of [bits_to_Z] / [bits_to_crint]: fold the symbolic packet
   bits MSB-first as [acc := 2*acc + bit].  Each bit contributes 1 or 0 via
   [SmtConditional]; every intermediate stays an [IntVal (CrInt _)] under
   evaluation, so this commutes with [bits_to_crint] on the concretized bits. *)
Definition assemble_bits_symbolic (bs : list SmtBoolExpr) : SmtArithExpr :=
  List.fold_left
    (fun acc b =>
       SmtBitAdd (SmtBitAdd acc acc)
                 (SmtConditional b (SmtArithConst (CrInt (repr 1)))
                                   (SmtArithConst (CrInt (repr 0)))))
    bs (SmtArithConst (CrInt (repr 0))).

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
        let v := assemble_bits_symbolic slice in
        Some {| p_header_map := PMap.set (get_key h) v (p_header_map ps);
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  end.

(* The symbolic condition under which a [select] case fires: header
   [sc_header]'s current value equals the pattern's denoted value. *)
Definition select_case_cond_symbolic (ps : SymbolicParserState) (c : SelectCase)
    : SmtBoolExpr :=
  let pat_v := bits_to_crint (sc_pattern c) in
  match pat_v with
  | IntVal k => SmtBoolEq (lookup_varlike_map (p_header_map ps) (sc_header c))
                          (SmtArithConst k)
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
