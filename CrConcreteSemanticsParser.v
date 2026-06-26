From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrParser.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

(* ================================================================== *)
(* Concrete parser FSM semantics.                                      *)
(* ================================================================== *)

(* Apply a single extraction: read [width] bits from the packet at the
   current cursor (the packet is a [list bool], MSB-first), store the
   assembled value into header [h], and advance the cursor.  If the slice
   runs past the end of the packet the parse fails ([None]). *)
Definition apply_extract_concrete (eo : ExtractOp) (ps : ConcreteParserState)
    : option ConcreteParserState :=
  match eo with
  | ExtractOpConstructor h width =>
      if Nat.leb (p_cursor ps + width) (List.length (p_packet ps)) then
        let slice := bit_slice (p_packet ps) (p_cursor ps) width in
        let v := bits_to_crint slice in
        Some {| p_header_map := PMap.set (get_key h) v (p_header_map ps);
                p_packet     := p_packet ps;
                p_cursor     := p_cursor ps + width |}
      else None
  end.

(* Resolve a [select] case against the current header values: the case
   fires when header [sc_header]'s current value equals the value the
   pattern bits denote (matched over the [start,end) slice width). *)
Definition select_case_matches_concrete (ps : ConcreteParserState) (c : SelectCase)
    : bool :=
  let width := sc_end_index c - sc_start_index c in
  let pat_v := bits_to_crint (sc_pattern c) in
  CrVal.eqb (lookup_varlike_map (p_header_map ps) (sc_header c)) pat_v.

Fixpoint resolve_select_concrete (ps : ConcreteParserState)
    (cases : list SelectCase) (default : ParserTarget) : ParserTarget :=
  match cases with
  | [] => default
  | c :: rest =>
      if select_case_matches_concrete ps c
      then sc_target c
      else resolve_select_concrete ps rest default
  end.

Definition eval_transition_concrete (ps : ConcreteParserState) (t : Transition)
    : ParserTarget :=
  match t with
  | Unconditional tgt => tgt
  | Select cases default => resolve_select_concrete ps cases default
  end.

(* Run the parser FSM from [lbl].  [fuel] bounds the number of state
   visits.  Returns the parser state on a successful [Accept]; [None] on
   [Reject], a missing state, a failed extraction, or fuel exhaustion. *)
Fixpoint run_parser_concrete (p : Parser) (lbl : ParserStateLabel)
    (ps : ConcreteParserState) (fuel : nat) : option ConcreteParserState :=
  match fuel with
  | O => None
  | S fuel' =>
      match lookup_state p lbl with
      | None => None
      | Some d =>
          let ps_extracted :=
            match psd_extract d with
            | None => Some ps
            | Some eo => apply_extract_concrete eo ps
            end in
          match ps_extracted with
          | None => None
          | Some ps' =>
              match eval_transition_concrete ps' (psd_trans d) with
              | Accept => Some ps'
              | Reject => None
              | TargetState next => run_parser_concrete p next ps' fuel'
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
    : option ConcreteParserState :=
  run_parser_concrete p (parser_start p) ps
    (List.length (parser_states p) * S (List.length (p_packet ps))).
