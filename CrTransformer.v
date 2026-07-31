(* Transformer section below *)

(* Import necessary modules *)
From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVal.
From MyProject Require Import MyInts.

(* A transformer is either a sequential or a parallel transformer *)
Inductive TransformerType : Type := 
  | Sequential
  | Parallel.

(* Where an operand's value comes from. Operands are width-free: the width at
   which an operand is read is fixed by the operation that consumes it. *)
Inductive Operand :=
  | OpCtrlPlane (c : Ctrl)
  | OpHeader (h : Header)
  | OpConst (n : uint64) (* the constant adopts the consuming operation's type *)
  | OpStateful (s : State).

Inductive CmpOp :=
  | CmpEq
  | CmpGt
  | CmpLt.

(* A BinaryOp's operands are width-free; the operation's [CrIntType] (carried
   on the HdrOp) fixes the width it reads and writes at. *)
Inductive BinaryOp :=
  | AddOp
  | SubOp (* In modulo u8 *)
  | AndOp
  | OrOp
  | XorOp
  | MulOp 
  | DivOp 
  | ModOp.

(* Define the header operations.

   Arithmetic ops carry a single [CrIntType] [ty]: both operands are read at
   [ty] and the result is produced at [ty] (akin to the b/w/l/q suffix on a
   single instruction). Cast ops convert an operand from one int type to
   another ([from] tells the cast which bits are meaningful / how to extend,
   [to] the target); both widths are explicit because the value itself no
   longer records one.  (See the [prog_cast_*] programs in [TestPrograms.v] for
   worked examples.) *)
Inductive HdrOp :=
  | StatefulOp   (f : BinaryOp) (ty : CrIntType) (arg1 : Operand) (arg2 : Operand) (target : State)
  | StatelessOp  (f : BinaryOp) (ty : CrIntType) (arg1 : Operand) (arg2 : Operand) (target : Header)
  | CastStateOp  (from : CrIntType) (to : CrIntType) (arg : Operand) (target : State)
  | CastHeaderOp (from : CrIntType) (to : CrIntType) (arg : Operand) (target : Header)
  (* Memory.  The region is named statically and the offset within it is a
     runtime value, which is how eBPF works in practice -- the verifier fixes
     pointer provenance before the program runs.  [ty] is the type the loaded
     value is produced at / the stored value is read at, exactly as on the
     arithmetic ops.

     Both are TOTAL.  An access outside the region's declared length yields
     [ErrorVal] into the target (load) or is dropped (store); neither clears
     [gps_valid].  What distinguishes a program that reads further is
     [CrGeneralProgramState.sh_mem_extent], which every access updates, not a
     rejection.  Do not make these partial -- SOUNDNESS.md, on the
     both-rejected disjunct, says why. *)
  | LoadOp  (ty : CrIntType) (region : MemRegion) (off : Operand) (target : Header)
  | StoreOp (ty : CrIntType) (region : MemRegion) (off : Operand) (val : Operand).

(* Define MatchPattern as a list of header, pattern pairs.  A [MatchConst]
   carries its own [CrIntType]: the constant is read at [ty] and compared
   against the header value, which (like every [CrVal] comparison) requires the
   two operands to share a type.  A [MatchHeader] compares two header values
   directly.  TODO: Need to handle wildcards. *)
Inductive MatchValue :=
| MatchConst (k : uint64) (ty : CrIntType)
| MatchHeader (h : Header).
Definition MatchPattern := list (Header * CmpOp * MatchValue).

Inductive SeqRule :=
  | SeqCtr (match_pattern : MatchPattern) (action : list HdrOp).

(* Extract targets out of a HdrOp.  A [StoreOp]'s target is a memory cell, not
   a [State] or a [Header], and it contributes nothing here: the [NoDup]
   obligation on [ParRule] below is about two actions writing the same
   variable, and the corresponding property for memory -- two stores hitting
   the same offset of the same region -- is not statically decidable, since
   offsets are runtime values.  Memory ops SHOULD therefore be barred from
   [ParRule] -- [CrDslProperties.no_mem_ops_in_parb] is that check -- but
   nothing enforces it, and nothing proves what the [NoDup] below buys either.
   A racy program is expressible and silently accepted; TODO.md 1.5 has why
   that is currently harmless and what it would take to catch. *)
Definition extract_targets (op : HdrOp) : (list State) * (list Header) :=
  match op with
  | StatefulOp _ _ _ _ target => ([target], [])
  | StatelessOp _ _ _ _ target => ([], [target])
  | CastStateOp _ _ _ target => ([target], [])
  | CastHeaderOp _ _ _ target => ([], [target])
  | LoadOp _ _ _ target => ([], [target])
  | StoreOp _ _ _ _ => ([], [])
  end.

Definition is_mem_op (op : HdrOp) : bool :=
  match op with
  | LoadOp _ _ _ _ | StoreOp _ _ _ _ => true
  | _ => false
  end.

(* Extract all targets from a list of HdrOps *)
Definition extract_all_targets (ops : list HdrOp) : (list State) * (list Header) :=
  List.fold_left (fun acc op => 
    let (state_vars, headers) := extract_targets op in
    (state_vars ++ fst acc, headers ++ snd acc)) ops ([], []).

(* TODO: Add masks and don't care bits *)
Inductive ParRule :=
  | ParCtr (match_pattern : MatchPattern)
    (action : {l : list HdrOp | NoDup (fst (extract_all_targets l)) /\
                                NoDup (snd (extract_all_targets l))}).

Inductive MatchActionRule :=
  | Seq (s : SeqRule)
  | Par (p : ParRule).

Definition Transformer : Type := list MatchActionRule.