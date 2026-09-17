From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
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

(* The bits a [select] case matches against.  Mirrors
   [select_bits_concrete] node for node: [SmtBitSlice] denotes [slice_val]
   and [SmtBitsToInt] denotes [mk_int u64 (bits_to_Z ...)], so the [Peek]
   arm reads the same bits at the same offset as the concrete one.  [None]
   on the same length condition, and like there the cursor does not move. *)
Definition select_bits_symbolic (ps : SymbolicParserState) (o : SelBits)
    : option SmtArithExpr :=
  match o with
  | SelHdr h lo hi =>
      Some (SmtBitSlice lo hi (lookup_varlike_map (p_header_map ps) h))
  | Peek off width =>
      if Nat.leb (p_cursor ps + off + width) (List.length (p_packet ps)) then
        Some (SmtBitsToInt (List.map cvv
                (List.firstn width (List.skipn (p_cursor ps + off) (p_packet ps)))))
      else None
  end.

(* Mirrors [select_bits_available_concrete]: the packet must be long enough
   for EVERY case's peek, or the parse rejects.  This is the length check
   only -- concrete on each path, since offsets, widths and the cursor are
   all [nat]s.  Whether those positions are PRESENT rather than padding is
   the separate, symbolic [select_bits_valid] below. *)
Definition select_bits_available_symbolic (ps : SymbolicParserState)
    (cases : list SelectCase) : bool :=
  List.forallb
    (fun c => match select_bits_symbolic ps (sc_origin c) with
              | Some _ => true
              | None => false
              end)
    cases.

(* Presence of everything a peek requires, conjoined.  A [Peek] examines
   packet positions without consuming them, so its range contributes to the
   accept condition exactly as an extract's does even though no cursor moves
   -- for a chained parser reading an upstream residual, peeking at padding
   must not accept.  [SelHdr] reads a header, not the packet, and contributes
   nothing.

   The range is [cursor, cursor + off + width), NOT the peeked window
   [cursor + off, cursor + off + width), and the difference is load-bearing.
   [select_bits_available_concrete] asks whether the packet REACHES
   [cursor + off + width]; the presence conjunct has to say the same thing,
   and it only does when it starts at the cursor.  With the window alone a
   zero-width peek at a positive offset contributes [SmtTrue] no matter how
   short the packet is, so a chained parser whose residual ends before
   [cursor + off] would REJECT concretely and ACCEPT symbolically.  Starting
   at the cursor makes the two exact: given that the cursor is itself inside
   the present prefix (which it is, since every step that moved it passed
   this same check), "the present prefix reaches [cursor + off + width]" and
   "every position in [cursor, cursor + off + width) is present" are the same
   statement.  See [ParserCommuteLemmas.slice_range_out_of_prefix]. *)
Definition select_bits_valid (ps : SymbolicParserState)
    (cases : list SelectCase) : SmtBoolExpr :=
  List.fold_right SmtBoolAnd SmtTrue
    (List.map (fun c => match sc_origin c with
                        | SelHdr _ _ _ => SmtTrue
                        | Peek off width =>
                            slice_valid (p_packet ps) (p_cursor ps) (off + width)
                        end)
              cases).

(* The symbolic condition under which a [select] case fires.  Mirrors
   [select_case_matches_concrete]. *)
Definition select_case_cond_symbolic (ps : SymbolicParserState) (c : SelectCase)
    : SmtBoolExpr :=
  match select_bits_symbolic ps (sc_origin c) with
  | None => SmtFalse
  | Some bits =>
      SmtBoolEq bits
        (SmtArithConst (mask_width W64 (bits_to_Z (sc_pattern c))) u64)
  end.

(* ===================================================================== *)
(* Accept-aware symbolic parser semantics.                               *)
(*                                                                       *)
(* Symbolic execution is path-merged: data-dependent [select] control    *)
(* flow is merged into a single symbolic header map, and a [Reject] is a *)
(* symbolic predicate over the packet bits rather than a control-flow    *)
(* abort.  The evaluator threads three things together:                  *)
(*   - [pr_accept]: the condition under which the parse accepts;         *)
(*   - [pr_headers]: the merged final header values;                     *)
(*   - [pr_residual]: the bits left unconsumed (the network's next read  *)
(*     tape), path-merged as a [ConditionalVal] bitstream.               *)
(*                                                                       *)
(* [SymParserResult] is [CrGeneralProgramState.ParserResult] at the      *)
(* symbolic types, the same record the concrete evaluator returns at the *)
(* concrete ones.  This side has no [option] around it: it never fails   *)
(* to produce a result, it only produces [SmtFalse].                     *)
(* ===================================================================== *)

(* A [nat] bit count as a [u64] SMT constant.  The count is concrete on each
   individual path (the cursor is a [nat]); it only becomes symbolic once
   [merge_results] combines paths that consumed different amounts. *)
Definition smt_bits_count (n : nat) : SmtArithExpr :=
  SmtArithConst (mask_width W64 (Z.of_nat n)) u64.

(* Boolean if-then-else, since [SmtConditional] only builds arith exprs. *)
Definition smt_bool_ite (c a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd c a) (SmtBoolAnd (SmtBoolNot c) b).

(* Merge two header maps under [cond]: each header becomes
   [SmtConditional cond then_val else_val].

   Keys come from BOTH maps.  This used to take them from [m_then] alone, on
   the grounds that "the two maps share the same header domain in practice" --
   which was true only because [init_general_symbolic_state] seeds the header
   map with the whole network's header interface, so every header a branch
   could write was already a key.  Where that seeding does not apply (a parser
   evaluated on its own, as [SmtParserQuery] and the parser test programs do),
   a header extracted only on the ELSE side of a [select] was not a key of
   [m_then] and was silently dropped: on that path it read back the map's
   default instead of what the branch parsed.  That is the same failure mode
   as SOUNDNESS.md model-debt item 2, where a dropped header made the network
   checker compare two empty outputs and answer [Equivalent].

   Folding over the union is the same shape [merge_mem_ctx_smt] uses one level
   up, and it leaves only one obligation -- that the two maps carry the same
   DEFAULT, which they do because [PMap.set] is the only writer and it never
   moves the default. *)
Definition merge_header_maps (cond : SmtBoolExpr)
    (m_then m_else : PMap.t SmtArithExpr) : PMap.t SmtArithExpr :=
  List.fold_left
    (fun acc k => PMap.set k (SmtConditional cond (m_then !! k) (m_else !! k)) acc)
    (pmap_keys m_then ++ pmap_keys m_else)
    m_then.

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
  {| pr_accept    := smt_bool_ite cond (pr_accept r_then) (pr_accept r_else);
     pr_headers   := merge_header_maps cond (pr_headers r_then) (pr_headers r_else);
     pr_residual  := merge_bitstream cond (pr_residual r_then) (pr_residual r_else);
     pr_bits_read := SmtConditional cond (pr_bits_read r_then) (pr_bits_read r_else) |}.

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
   yields [pr_accept := SmtFalse] with the headers reached so far, an empty
   residual (which [merge_bitstream] pads as absent), and the bits consumed up
   to that point.  On a non-accepting path the count is never observed -- the
   checker only compares it where both sides accept -- but it must still be a
   well-defined expression for [merge_results] to combine. *)
(* One transition target, under accept condition [g].

   Factored out of [run_parser_symbolic] below rather than left as a local
   [let] so that proofs can name it -- the concrete/symbolic commutation
   argument needs to say "this step accepts nothing when [g] is false", and a
   nameless [let]-bound lambda cannot appear in a lemma statement.  The
   recursive call is passed in as [rec]; the guard checker accepts that
   because at the one call site it is applied to a structural subterm of the
   fuel. *)
Definition run_target_symbolic
    (rec : ParserStateLabel -> SymbolicParserState -> SmtBoolExpr -> SymParserResult)
    (ps : SymbolicParserState) (g : SmtBoolExpr) (tgt : ParserTarget)
    : SymParserResult :=
  match tgt with
  | Accept =>
      mkParserResult g (p_header_map ps)
        (List.skipn (p_cursor ps) (p_packet ps))
        (smt_bits_count (p_cursor ps))
  | Reject =>
      mkParserResult SmtFalse (p_header_map ps) [] (smt_bits_count (p_cursor ps))
  | TargetState next => rec next ps g
  end.

Fixpoint run_parser_symbolic (p : Parser) (lbl : ParserStateLabel)
    (ps : SymbolicParserState) (guard : SmtBoolExpr) (fuel : nat)
    : SymParserResult :=
  let reject :=
    mkParserResult SmtFalse (p_header_map ps) [] (smt_bits_count (p_cursor ps)) in
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
              (* [run_tgt] takes the guard rather than closing over [guard'],
                 because a [select]'s peeks add to it before any target runs. *)
              let run_tgt := run_target_symbolic
                (fun next ps'' g => run_parser_symbolic p next ps'' g fuel')
                ps' in
              match psd_trans d with
              | Unconditional tgt => run_tgt guard' tgt
              | Select cases default =>
                  (* Mirrors [eval_transition_concrete].  Too short for some
                     case's peek rejects outright; otherwise the presence of
                     every peeked range joins the guard on EVERY path out of
                     the select, because concretely we would have rejected
                     before finding out which case fires. *)
                  if select_bits_available_symbolic ps' cases then
                    resolve_select_symbolic
                      (run_tgt (SmtBoolAnd guard' (select_bits_valid ps' cases)))
                      ps' cases default
                  else
                    mkParserResult SmtFalse (p_header_map ps') []
                      (smt_bits_count (p_cursor ps'))
              end
          end
      end
  end.

(* Fuel bounds total state visits, exactly as [eval_parser_concrete]. *)
Definition eval_parser_symbolic (p : Parser) (ps : SymbolicParserState)
    : SymParserResult :=
  run_parser_symbolic p (parser_start p) ps SmtTrue
    (List.length (parser_states p) * S (List.length (p_packet ps))).

(* The bits of a symbolic bitstream that are actually THERE under [f]:
   [cvc] decides presence, [cvv] supplies the value.

   Read tapes are concretized with this rather than positionally, and the
   reason is [merge_bitstream].  A [select] whose branches consume different
   amounts leaves a merged residual as long as the LONGEST branch, with the
   surplus positions carrying [cvc] false on the paths that did not take them.
   A concrete run takes ONE path and leaves exactly that path's residual, so a
   positional concretization compares a short concrete tape against a longer
   symbolic one and no commutation lemma can hold.  Dropping the absent
   positions is what makes the two lengths agree.

   Write tapes do NOT need this and must not use it: [wt_unconditional] says
   every bit a deparser emits carries [cvc := SmtTrue], which is exactly the
   invariant that lets the write tape be compared positionally -- and
   [sym_out_equal_sound], which the soundness proof runs on, is stated that
   way.  Hence the split in [concretize_sym_module_state]: a parser module's
   local packet goes through here, a deparser module's does not.

   Lives at the parser level rather than in [CrSymbolicSemanticsModule], where
   it used to, because [eval_sym_parser_state] below needs it and the module
   file is downstream of this one. *)
Definition present_bits (l : list (ConditionalVal SmtBoolExpr)) (f : SmtValuation)
    : list bool :=
  List.map (fun b => eval_smt_bool (cvv b) f)
           (List.filter (fun b => eval_smt_bool (cvc b) f) l).

(* Concretize a symbolic parser state under a valuation [f]: the parser analogue
   of [eval_sym_state] for transformers.  Every symbolic header value runs
   through [eval_smt_arith f]; the cursor is unchanged.

   The packet goes through [present_bits], NOT positionally -- a parser's
   packet is a read tape.  This used to map over it positionally, which is the
   concretization TODO 1.1.1 records as giving a wrong VERDICT rather than
   merely an unprovable lemma; it was dead code, so nothing depended on the
   wrong version, but it is the function a parser-commutation proof reaches for
   first.  [concretize_sym_module_state]'s [ParserMod] branch is this, so there
   is one definition and not two that can drift. *)
Definition eval_sym_parser_state (s : SymbolicParserState) (f : SmtValuation)
    : ConcreteParserState :=
  {| p_header_map := PMap.map (fun e => eval_smt_arith e f) (p_header_map s);
     p_packet     := present_bits (p_packet s) f;
     p_cursor     := p_cursor s |}.
