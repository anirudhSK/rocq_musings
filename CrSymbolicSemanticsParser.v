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

(* ===================================================================== *)
(* Symbolic parser FSM semantics.                                        *)
(*                                                                       *)
(* Mirrors the concrete parser FSM (CrConcreteSemanticsParser) but,      *)
(* like the symbolic transformer, never path-splits: data-dependent      *)
(* [select] control flow is merged into a single symbolic header map     *)
(* using [SmtConditional], exactly as [eval_transformer_smt] does for    *)
(* match-action rules.                                                   *)
(*                                                                       *)
(* The packet-bit type is [ConditionalVal SmtBoolExpr]: [cvv] is the     *)
(* bit's value and [cvc] its presence/validity condition.  A source      *)
(* parser reads an all-present packet ([cvc = SmtTrue] everywhere); a    *)
(* CHAINED parser reads the residual an upstream parser left, whose      *)
(* trailing positions may be padding ([cvc] false).  Extracting from a   *)
(* padded position must not accept, so the accept condition conjoins the *)
(* presence [cvc] of every consumed position (see [slice_valid]).        *)
(* ===================================================================== *)

(* The bit width a parser op consumes from the stream. *)
Definition parser_op_width (po : ParserOp) : nat :=
  match po with
  | SeekForward width => width
  | ExtractOpConstructor _ width _ => width
  end.

(* Parsed fields are typed by the extract's [of].  A field is the [u64]
   [SmtBitsToInt] of its packet-bit values (MSB first), cast to [of]; this
   denotes the same value as the concrete [mk_int of (bits_to_Z ...)] but
   lowers to a bitvector [concat] in Z3 instead of an arithmetic chain. *)
Definition apply_extract_symbolic (po : ParserOp) (ps : SymbolicParserState)
    : option SymbolicParserState :=
  match po with
  | SeekForward width =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        Some {| p_header_map := p_header_map ps;
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  | ExtractOpConstructor h width of =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        let slice := List.map cvv
          (List.firstn width (List.skipn (p_cursor ps) (p_packet ps))) in
        let v := SmtCast u64 of (SmtBitsToInt slice) in
        Some {| p_header_map := PMap.set (get_key h) v (p_header_map ps);
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  end.

(* Presence of the consumed range [cursor, cursor+width): the conjunction of
   the [cvc] flags of those packet positions.  For a source parser (all
   positions present) this is [SmtTrue]; for a chained parser it forces the
   accept condition to be false when a consumed position is padding. *)
Definition slice_valid (pkt : list (ConditionalVal SmtBoolExpr)) (cursor width : nat)
    : SmtBoolExpr :=
  List.fold_right SmtBoolAnd SmtTrue
    (List.map cvc (List.firstn width (List.skipn cursor pkt))).

(* The symbolic condition under which a [select] case fires: bits
   [sc_start_index, sc_end_index) of header [sc_header]'s current value equal
   the pattern's denoted value.  Mirrors [select_case_matches_concrete]. *)
Definition select_case_cond_symbolic (ps : SymbolicParserState) (c : SelectCase)
    : SmtBoolExpr :=
  SmtBoolEq
    (SmtBitSlice (sc_start_index c) (sc_end_index c)
      (lookup_varlike_map (p_header_map ps) (sc_header c)))
    (SmtArithConst (mask_width W64 (bits_to_Z (sc_pattern c))) u64).

(* ===================================================================== *)
(* Accept-aware symbolic parser semantics.                               *)
(*                                                                       *)
(* Symbolic execution is path-merged: data-dependent [select] control    *)
(* flow is merged into a single symbolic header map, and a [Reject] is a *)
(* symbolic predicate over the packet bits rather than a control-flow    *)
(* abort.  The evaluator threads three things together:                  *)
(*   - [spr_accept]: the condition under which the parse accepts;        *)
(*   - [spr_headers]: the merged final header values;                    *)
(*   - [spr_residual]: the bits left unconsumed (the network's next read *)
(*     tape), path-merged as a [ConditionalVal] bitstream.               *)
(* ===================================================================== *)

Record SymParserResult : Type := mkSymParserResult {
  spr_accept    : SmtBoolExpr;                          (* accepts iff this holds *)
  spr_headers   : PMap.t SmtArithExpr;                  (* final header values *)
  spr_residual  : list (ConditionalVal SmtBoolExpr);    (* unconsumed tail *)
  spr_bits_read : SmtArithExpr;                         (* bits consumed *)
}.

(* A [nat] bit count as a [u64] SMT constant.  The count is concrete on each
   individual path (the cursor is a [nat]); it only becomes symbolic once
   [merge_results] combines paths that consumed different amounts. *)
Definition smt_bits_count (n : nat) : SmtArithExpr :=
  SmtArithConst (mask_width W64 (Z.of_nat n)) u64.

(* Boolean if-then-else, since [SmtConditional] only builds arith exprs. *)
Definition smt_bool_ite (c a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd c a) (SmtBoolAnd (SmtBoolNot c) b).

(* Merge two header maps under [cond]: each header becomes
   [SmtConditional cond then_val else_val].  Keys are taken from [m_then]
   (the two maps share the same header domain in practice). *)
Definition merge_header_maps (cond : SmtBoolExpr)
    (m_then m_else : PMap.t SmtArithExpr) : PMap.t SmtArithExpr :=
  (fst m_then,
   PTree.map (fun k v_then =>
                SmtConditional cond v_then (PMap.get k m_else))
             (snd m_then)).

(* Merge two residuals under [cond]: keep [l1] where [cond] holds, else [l2];
   pad the shorter side with absent ([SmtFalse] presence) positions.
   Structurally recursive on [l1]. *)
Fixpoint merge_bitstream (cond : SmtBoolExpr)
    (l1 l2 : list (ConditionalVal SmtBoolExpr))
    : list (ConditionalVal SmtBoolExpr) :=
  match l1 with
  | [] =>
      List.map (fun c2 =>
                  {| cvc := smt_bool_ite cond SmtFalse (cvc c2);
                     cvv := smt_bool_ite cond SmtFalse (cvv c2) |}) l2
  | c1 :: r1 =>
      match l2 with
      | [] =>
          {| cvc := smt_bool_ite cond (cvc c1) SmtFalse;
             cvv := smt_bool_ite cond (cvv c1) SmtFalse |}
            :: merge_bitstream cond r1 []
      | c2 :: r2 =>
          {| cvc := smt_bool_ite cond (cvc c1) (cvc c2);
             cvv := smt_bool_ite cond (cvv c1) (cvv c2) |}
            :: merge_bitstream cond r1 r2
      end
  end.

(* Merge two results under [cond]. *)
Definition merge_results (cond : SmtBoolExpr) (r_then r_else : SymParserResult)
    : SymParserResult :=
  {| spr_accept    := smt_bool_ite cond (spr_accept r_then) (spr_accept r_else);
     spr_headers   := merge_header_maps cond (spr_headers r_then) (spr_headers r_else);
     spr_residual  := merge_bitstream cond (spr_residual r_then) (spr_residual r_else);
     spr_bits_read := SmtConditional cond (spr_bits_read r_then) (spr_bits_read r_else) |}.

(* Merge all [select] cases into one accept-aware result, given a total
   continuation [run_tgt].  Structurally recursive on [cases]. *)
Fixpoint resolve_select_symbolic
    (run_tgt : ParserTarget -> SymParserResult)
    (ps : SymbolicParserState)
    (cases : list SelectCase) (default : ParserTarget)
    : SymParserResult :=
  match cases with
  | [] => run_tgt default
  | c :: rest =>
      let cond := select_case_cond_symbolic ps c in
      merge_results cond (run_tgt (sc_target c))
                    (resolve_select_symbolic run_tgt ps rest default)
  end.

(* Run the parser FSM symbolically from [lbl], threading an accept condition
   [guard] (the presence of everything consumed so far) alongside the merged
   header map and residual.  [fuel] bounds state visits.  Total (never [None]):
   a dead-end (missing state, failed extraction, fuel exhaustion, [Reject])
   yields [spr_accept := SmtFalse] with the headers reached so far, an empty
   residual (which [merge_bitstream] pads as absent), and the bits consumed up
   to that point.  On a non-accepting path the count is never observed -- the
   checker only compares it where both sides accept -- but it must still be a
   well-defined expression for [merge_results] to combine. *)
Fixpoint run_parser_symbolic (p : Parser) (lbl : ParserStateLabel)
    (ps : SymbolicParserState) (guard : SmtBoolExpr) (fuel : nat)
    : SymParserResult :=
  let reject :=
    mkSymParserResult SmtFalse (p_header_map ps) [] (smt_bits_count (p_cursor ps)) in
  match fuel with
  | O => reject
  | S fuel' =>
      match lookup_def p lbl with
      | None => reject
      | Some d =>
          (* Apply the action, advancing the cursor and conjoining the
             presence of the consumed range into the running [guard]. *)
          let ext :=
            match psd_action d with
            | None => Some (ps, guard)
            | Some po =>
                match apply_extract_symbolic po ps with
                | None => None
                | Some ps' =>
                    Some (ps', SmtBoolAnd guard
                                 (slice_valid (p_packet ps) (p_cursor ps)
                                              (parser_op_width po)))
                end
            end in
          match ext with
          | None => reject
          | Some (ps', guard') =>
              let run_tgt := fun (tgt : ParserTarget) =>
                match tgt with
                | Accept =>
                    mkSymParserResult guard' (p_header_map ps')
                      (List.skipn (p_cursor ps') (p_packet ps'))
                      (smt_bits_count (p_cursor ps'))
                | Reject =>
                    mkSymParserResult SmtFalse (p_header_map ps') []
                      (smt_bits_count (p_cursor ps'))
                | TargetState next => run_parser_symbolic p next ps' guard' fuel'
                end in
              match psd_trans d with
              | Unconditional tgt => run_tgt tgt
              | Select cases default =>
                  resolve_select_symbolic run_tgt ps' cases default
              end
          end
      end
  end.

(* Fuel bounds total state visits, exactly as [eval_parser_concrete]. *)
Definition eval_parser_symbolic (p : Parser) (ps : SymbolicParserState)
    : SymParserResult :=
  run_parser_symbolic p (parser_start p) ps SmtTrue
    (List.length (parser_states p) * S (List.length (p_packet ps))).

(* Concretize a symbolic parser state under a valuation [f]: the parser analogue
   of [eval_sym_state] for transformers.  Every symbolic header value runs
   through [eval_smt_arith f] and every symbolic packet bit's value through
   [eval_smt_bool f]; the cursor is unchanged.  [List.map] preserves the packet
   length. *)
Definition eval_sym_parser_state (s : SymbolicParserState) (f : SmtValuation)
    : ConcreteParserState :=
  {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map s);
     p_packet     := List.map (fun b => eval_smt_bool (cvv b) f) (p_packet s);
     p_cursor     := p_cursor s |}.
