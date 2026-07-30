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

(* ------------------------------------------------------------------ *)
(* Extraction: read [width] bits from the packet's current cursor and  *)
(* store them into header [eo_header].  The [width] is given as a bit  *)
(* count (the number of bits consumed from the stream); the assembled  *)
(* value is then coerced into the integer type [of] (e.g. [u8], [u16]).*)
Inductive ParserOp : Type :=
  | SeekForward (width: nat)
  | ExtractOpConstructor (eo_header : Header) (width : nat) (of : CrIntType).

(* ------------------------------------------------------------------ *)
(* A target of a transition is either another parser state, or one of  *)
(* the two terminal pseudo-states.                                     *)
Inductive ParserTarget : Type :=
  | TargetState (s : ParserStateLabel)
  | Accept
  | Reject.

(* TODO: See how P4 pads fields into containers *)

(* A single transition selection rule: if the most-recently-parsed     *)
(* bits of header [h] (the slice [start_index, end_index)) match the    *)
(* bit [pattern], jump to [target].                                     *)
Record SelectCase : Type := mkSelectCase {
  sc_header      : Header;
  sc_start_index : nat;
  sc_end_index   : nat;
  sc_pattern     : list bool;
  sc_target      : ParserTarget;
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

(* ------------------------------------------------------------------ *)
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
        (fun acc'' c => sc_header c :: acc'')
        cases acc'
    end) (parser_states p) [].

(* ------------------------------------------------------------------ *)
(* Bit helpers.  A packet bit stream is represented MSB-first as a      *)
(* [list bool]; index 0 is the first bit on the wire.                   *)

(* Interpret a bit list (MSB-first) as a non-negative integer. *)
Definition bits_to_Z (bs : list bool) : Z :=
  List.fold_left (fun (acc : Z) (b : bool) => Z.add (Z.mul 2 acc) (if b then 1%Z else 0%Z)) bs 0%Z.

(* Take the [n] bits starting at offset [start] (0-indexed). *)
Definition bit_slice (bs : list bool) (start width : nat) : list bool :=
  List.firstn width (List.skipn start bs).
