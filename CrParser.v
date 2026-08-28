(* ================================================================== *)
(* P4-style packet parser.                                            *)
(*                                                                    *)
(* A parser is a finite state machine.  Each parser state may extract *)
(* a contiguous run of bits from the incoming packet into a header,   *)
(* then transition to a successor state (possibly conditioned on the  *)
(* bits just observed).  Parsing terminates at the distinguished      *)
(* [Accept] (success) or [Reject] (failure) pseudo-states.            *)
(* ================================================================== *)
From Stdlib Require Import List.
From Stdlib Require Import ZArith.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import Integers.
From MyProject Require Import MyInts.
From MyProject Require Import CrVal.

(* ------------------------------------------------------------------- *)
(* Extraction: read [width] bits from the packet's current cursor and  *)
(* store them into header [eo_header].  The [width] is given as a bit  *)
(* count (the number of bits consumed from the stream); the assembled  *)
(* value is then coerced into the integer type [of] (e.g. [u8], [u16]).*)
Inductive ParserOp : Type :=
  | SeekForward (width: nat)
  | ExtractOpConstructor (eo_header : Header) (width : nat) (of : CrIntType).

(* ------------------------------------------------------------------- *)
(* A target of a transition is either another parser state, or one of  *)
(* the two terminal pseudo-states.                                     *)
Inductive ParserTarget : Type :=
  | TargetState (s : ParserStateLabel)
  | Accept
  | Reject.

(* TODO: See how P4 pads fields into containers *)

(* Where a [select] case reads the bits it matches on.                  *)
(*                                                                      *)
(* [SelHdr h start_idx end_idx] reads bits [start_idx, end_idx) of the   *)
(* CURRENT VALUE of header [h] -- already-parsed data, so it can never   *)
(* fail.                                                                *)
(*                                                                      *)
(* [Peek cursor_offset width] reads [width] bits from the packet itself, *)
(* starting [cursor_offset] bits past the current cursor.  This is P4's  *)
(* [lookahead]: it does NOT consume, so the cursor is the same after the *)
(* transition as before it, and a state is free to peek at bits a later  *)
(* state will go on to extract.  Unlike [SelHdr] it CAN run out of       *)
(* packet, and when it does the parse rejects (P4's [PacketTooShort]) --  *)
(* it does not fall through to the select's default.  So a [Peek]'s      *)
(* range joins the accept condition exactly as an extract's does, even   *)
(* though no cursor moves; see [select_bits_valid].                      *)
Inductive SelBits : Type :=
| SelHdr (h : Header) (start_idx : nat) (end_idx : nat)
| Peek (cursor_offset : nat) (width: nat).

(* A single transition selection rule: if the bits named by [sc_origin]  *)
(* match the bit [pattern], jump to [target].                            *)
Record SelectCase : Type := mkSelectCase {
  sc_origin  : SelBits;
  sc_pattern : list bool;
  sc_target  : ParserTarget;
}.

(* A transition is either an unconditional jump, or a P4-style          *)
(* [select]: a list of cases tried in order, with a default target.     *)
Inductive Transition : Type :=
  | Unconditional (target : ParserTarget)
  | Select (cases : list SelectCase) (default : ParserTarget).

(* A parser state definition: its label, the (optional) extraction it   *)
(* performs, and its outgoing transition.                               *)
Record ParserStateDef : Type := mkParserStateDef {
  psd_label  : ParserStateLabel;
  psd_action : option ParserOp;
  psd_trans  : Transition;
}.

(* A parser is a start state plus the list of its state definitions.    *)
Record Parser : Type := mkParser {
  parser_start  : ParserStateLabel;
  parser_states : list ParserStateDef;
}.

(* ------------------------------------------------------------------- *)
(* Look up the definition of a parser state by its label.              *)
Definition lookup_def (p : Parser) (lbl : ParserStateLabel)
    : option ParserStateDef :=
  find (fun d => posesque_eqb (psd_label d) lbl) (parser_states p).

(* list of all parser i/o headers *)
Definition parser_headers (p : Parser) : list Header :=
  List.fold_left (fun acc d =>
    (* get write headers *)
    let acc' := match psd_action d with
    | Some (ExtractOpConstructor h _ _) => h :: acc
    | _ => acc
    end in
    (* get read headers *)
    match psd_trans d with
    | Unconditional _ => acc'
    | Select cases _ =>
      List.fold_left
        (fun acc'' c => match sc_origin c with
          | SelHdr h _ _ => h :: acc''
          | Peek _ _ => acc''
          end)
        cases acc'
    end) (parser_states p) [].

(* --------------------------------------------------------------- *)
(* Bit helpers.  A packet bit stream is represented MSB-first as a *)
(* [list bool]; index 0 is the first bit on the wire.              *)

(* Interpret a bit list (MSB-first) as a non-negative integer. *)
Definition bits_to_Z (bs : list bool) : Z :=
  List.fold_left (fun (acc : Z) (b : bool) => Z.add (Z.mul 2 acc) (if b then 1%Z else 0%Z)) bs 0%Z.

(* Take the [n] bits starting at offset [start] (0-indexed). *)
Definition bit_slice (bs : list bool) (start width : nat) : list bool :=
  List.firstn width (List.skipn start bs).
