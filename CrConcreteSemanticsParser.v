From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrParser.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Concrete parser FSM semantics.                                     *)
(* ================================================================== *)

(* Apply a single extraction: read [width] bits from the packet at the
   current cursor (the packet is a [list bool], MSB-first), store the
   assembled value into header [h], and advance the cursor.  If the slice
   runs past the end of the packet the parse fails ([None]). *)
Definition apply_extract_concrete (po : ParserOp) (ps : ConcreteParserState)
    : option ConcreteParserState :=
  match po with
  | SeekForward width =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        Some {| p_header_map := (p_header_map ps);
                p_packet := p_packet ps;
                p_cursor := p_cursor ps + width |}
      else None
  | ExtractOpConstructor h width of =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        let slice := bit_slice (p_packet ps) (p_cursor ps) width in
        (* Assemble the [width] bits (MSB-first) and coerce into type [of]. *)
        let v := mk_int of (bits_to_Z slice) in
        Some {| p_header_map := PMap.set (get_key h) v (p_header_map ps);
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  end.

(* The bits a [select] case matches against, right-aligned in a [u64].
   [None] iff a [Peek] runs past the end of the packet -- a [SelHdr] reads
   already-parsed data and so always succeeds.

   A [Peek] does not move the cursor: it reads at [p_cursor + cursor_offset]
   and leaves [ps] alone, so the state a select transitions into starts where
   this one ended.  That is the whole of P4's [lookahead]. *)
Definition select_bits_concrete (ps : ConcreteParserState) (o : SelBits)
    : option CrVal :=
  match o with
  | SelHdr h lo hi =>
      Some (slice_val lo hi (lookup_varlike_map (p_header_map ps) h))
  | Peek off width =>
      if Nat.leb (p_cursor ps + off + width) (List.length (p_packet ps)) then
        Some (mk_int u64
                (bits_to_Z (bit_slice (p_packet ps) (p_cursor ps + off) width)))
      else None
  end.

(* A select reads the bits of EVERY one of its cases before matching any of
   them, so a [Peek] that runs off the end rejects the parse even when an
   earlier case would have matched and the peeked bits would never have been
   looked at.

   Two reasons.  P4 evaluates a select's key expression once, in full, before
   comparing it against any case, and with a per-case origin "all of them" is
   the analogue.  And it is what keeps the two evaluators in step: the
   symbolic side path-MERGES the cases, so it cannot make the presence of one
   case's bits conditional on an earlier case not matching -- it has only one
   accept condition to put them in.  Rejecting on any unavailable peek is the
   reading both can express. *)
Definition select_bits_available_concrete (ps : ConcreteParserState)
    (cases : list SelectCase) : bool :=
  List.forallb
    (fun c => match select_bits_concrete ps (sc_origin c) with
              | Some _ => true
              | None => false
              end)
    cases.

(* The case fires when its bits equal the value the pattern denotes. *)
Definition select_case_matches_concrete (ps : ConcreteParserState) (c : SelectCase)
    : bool :=
  match select_bits_concrete ps (sc_origin c) with
  | None => false
  | Some bits => CrVal.eqb bits (mk_int u64 (bits_to_Z (sc_pattern c)))
  end.

Fixpoint resolve_select_concrete (ps : ConcreteParserState)
    (cases : list SelectCase) (default : ParserTarget) : ParserTarget :=
  match cases with
  | [] => default
  | c :: rest =>
      if select_case_matches_concrete ps c
      then sc_target c
      else resolve_select_concrete ps rest default
  end.

(* [None] iff the transition's bits could not be read, which rejects. *)
Definition eval_transition_concrete (ps : ConcreteParserState) (t : Transition)
    : option ParserTarget :=
  match t with
  | Unconditional tgt => Some tgt
  | Select cases default =>
      if select_bits_available_concrete ps cases
      then Some (resolve_select_concrete ps cases default)
      else None
  end.

(* A run that finished, in either verdict.  [pr_bits_read] mirrors the
   symbolic [smt_bits_count]; a rejecting run leaves no residual, exactly as
   the symbolic [reject] does.

   The empty residual is what the symbolic side uses on all four of its
   non-accepting exits, and the two have to agree: [concretize_sym_modnet_state]
   maps over the residual positionally and DISCARDS [cvc], so a symbolic
   residual and its concrete counterpart correspond by length.  A rejecting run
   whose residual was the whole packet (all bits zeroed, say) would concretize
   against a symbolic [[]] and disagree on every position.  Nothing observes
   either one -- [gps_valid] is false and [check_sym_pkt_out] does not compare
   read tapes -- but the two evaluators still have to say the same thing. *)
Definition parser_reject_concrete (ps : ConcreteParserState) : ConcParserResult :=
  mkParserResult
    false
    (p_header_map ps)
    []
    (mk_int u64 (Z.of_nat (p_cursor ps))).

Definition parser_accept_concrete (ps : ConcreteParserState) : ConcParserResult :=
  mkParserResult true (p_header_map ps)
    (List.skipn (p_cursor ps) (p_packet ps))
    (mk_int u64 (Z.of_nat (p_cursor ps))).

(* Run the parser FSM from [lbl].  [fuel] bounds the number of state visits.

   [None] means the run DID NOT COMPLETE, and only that: the fuel ran out, or
   a transition named a state with no definition.  Every verdict about the
   packet -- including a [Reject], an extraction that ran off the end, and a
   [Peek] that did -- is a [Some] carrying [pr_accept].  [well_formed_parser]
   rules out both [None] cases, which is what makes this evaluator total on
   the programs the checker is allowed to see; see
   [ParserTerminationLemmas.eval_parser_no_fuel_starvation].

   The symbolic evaluator collapses all four into [pr_accept := SmtFalse],
   having no [option] to return.  On a well-formed parser the two agree
   because the [None] cases are unreachable -- which is exactly why the
   well-formedness conditions are not optional. *)
Fixpoint run_parser_concrete (p : Parser) (lbl : ParserStateLabel)
    (ps : ConcreteParserState) (fuel : nat) : option ConcParserResult :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_def p lbl with
      | None => None
      | Some def =>
          (* apply action *)
          let ps_post :=
            match psd_action def with
            | None => Some ps
            | Some po => apply_extract_concrete po ps
            end in
          match ps_post with
          (* Ran off the end of the packet: a verdict, not a failure. *)
          | None => Some (parser_reject_concrete ps)
          | Some ps' =>
              match eval_transition_concrete ps' (psd_trans def) with
              | None => Some (parser_reject_concrete ps')
              | Some Accept => Some (parser_accept_concrete ps')
              | Some Reject => Some (parser_reject_concrete ps')
              | Some (TargetState next) => run_parser_concrete p next ps' fuel'
              end
          end
      end
  end.

(* Fuel bounds total state visits.  A parse configuration is a (state, cursor)
   pair, and a terminating parse never repeats one, so |states| * (|packet| + 1)
   distinct configurations bound the visits.  This admits P4-style loops (a state
   may be revisited, once per cursor position) while still guaranteeing
   termination; exhausting the fuel means a (state, cursor) repeated, i.e. a true
   infinite loop. *)
Definition eval_parser_concrete (p : Parser) (ps : ConcreteParserState)
    : option ConcParserResult :=
  run_parser_concrete p (parser_start p) ps
    (List.length (parser_states p) * S (List.length (p_packet ps))).
