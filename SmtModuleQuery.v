From Stdlib Require Import ZArith.
From Stdlib Require Import String.
From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import Maps.
From MyProject Require Import SmtTypes.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtQuery.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrGeneralProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsModule.
From MyProject Require Import CrConcreteSemanticsModule.
From MyProject Require Import SmtHelperLemmas.

Definition keys_from_map {T A : Type} (fn : positive -> A) (m : PMap.t T) : list A :=
  List.map fn (List.map fst (PTree.elements (snd m))).

(* iff / implication, built from the primitive boolean connectives. *)
Definition smt_iff (a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolAnd a b) (SmtBoolAnd (SmtBoolNot a) (SmtBoolNot b)).
Definition smt_implies (a b : SmtBoolExpr) : SmtBoolExpr :=
  SmtBoolOr (SmtBoolNot a) b.

Fixpoint sym_out_equal (out1 out2 : list (ConditionalVal SmtBoolExpr)) : SmtBoolExpr :=
  match out1, out2 with
  | [], [] => SmtTrue
  | b1 :: _, [] => SmtBoolNot (cvc b1)   (* out1 must already be past its end *)
  | [], b2 :: _ => SmtBoolNot (cvc b2)
  | b1 :: r1, b2 :: r2 =>
      let v1 := cvc b1 in
      let v2 := cvc b2 in
      SmtBoolAnd
        (smt_iff v1 v2)                              (* same length so far *)
        (smt_implies
          (SmtBoolAnd v1 v2)                        (* only if both live... *)
          (SmtBoolAnd
            (smt_iff (cvv b1) (cvv b2))       (* ...bits agree *)
            (sym_out_equal r1 r2)))                 (* ...and recurse *)
  end.

(* Two accepting runs agree only if they consumed the same amount of the input
   packet.  This is the bitstream analogue of the memory IR's access-extent
   equivalence: a network that reads further into its input needs more of it to
   be there, so two networks that emit identical output packets but read
   different numbers of bits are not interchangeable.  Compared only where both
   sides accept -- a rejecting run has no meaningful read extent. *)
Definition check_sym_bits_read (s1 s2 : GeneralSymbolicState) : SmtBoolExpr :=
  SmtBoolEq (sh_bits_read s1) (sh_bits_read s2).

Definition check_sym_pkt_out (s1 s2 : GeneralSymbolicState) : SmtBoolExpr :=
  let v1 := cvv (gps_valid s1) in
  let v2 := cvv (gps_valid s2) in
  let eq_expr := SmtBoolOr
    (SmtBoolAnd (SmtBoolNot v1) (SmtBoolNot v2))
    (SmtBoolAnd (SmtBoolAnd v1 v2)
                (SmtBoolAnd
                  (sym_out_equal (sh_write_tape s1) (sh_write_tape s2))
                  (check_sym_bits_read s1 s2))) in
  SmtBoolNot eq_expr.

Definition modnet_equivalence_checker
  (p1 : GeneralCaracaraProgram) (p2 : GeneralCaracaraProgram)
  : EquivalenceResult :=
  let len_1 := get_inp_len_from_general p1 in
  let len_2 := get_inp_len_from_general p2 in
  (* packet shape must be the same *)
  if Nat.eqb len_1 len_2 then
    let sym1_opt := eval_general_program_symbolic p1 (init_general_symbolic_state "p1" p1) in
    let sym2_opt := eval_general_program_symbolic p2 (init_general_symbolic_state "p2" p2) in
    match sym1_opt, sym2_opt with
    | Some fs1, Some fs2 =>
      match smt_query (check_sym_pkt_out fs1 fs2) with
      | SmtUnsat => Equivalent
      | SmtSat f => NotEquivalent f
      | SmtUnknown => NotEquivalentUnknown
      end
    | _, _ => NotEquivalentVariablesDiffer
    end
  else
    NotEquivalentVariablesDiffer.

Definition is_linear_chain (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  is_dag net /\
  single_sink net /\
  no_fan_out net /\
  no_fan_in net.

Lemma modnet_equivalence_checker_sound :
  forall p1 p2,
  (* if two well-formed programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and they're considered equivalent *)
  modnet_equivalence_checker p1 p2 = Equivalent ->
  (* if we run them from their initial symbolic states *)
  forall s_i1 s_i2 s_f1 s_f2,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  eval_general_program_symbolic p1 s_i1 = Some s_f1 ->
  eval_general_program_symbolic p2 s_i2 = Some s_f2 ->
  (* then for every valuation of the symbolic variables *)
  forall c_f1 c_f2 (f : SmtValuation),
  (* the concretized outputs *)
  concretize_sym_modnet_state s_f1 f = c_f1 ->
  concretize_sym_modnet_state s_f2 f = c_f2 ->
  (* both are invalid *)
  (gps_valid c_f1 = false /\ gps_valid c_f2 = false)
  (* or both are valid and have identical output packets *)
  \/
  ( gps_valid c_f1 = true /\ gps_valid c_f2 = true /\
    List.length (sh_write_tape c_f1) = List.length (sh_write_tape c_f2) /\
    (* ...consumed the same amount of the input packet ([check_sym_bits_read]).
       Stated over [sh_bits_read] rather than the residual's list length: the
       symbolic residual is padded by [merge_bitstream], so its raw length is
       not the read extent and concretization does not shrink it. *)
    sh_bits_read c_f1 = sh_bits_read c_f2 /\
    List.Forall (fun '(b1, b2) => b1 = b2)
      (List.combine (sh_write_tape c_f1) (sh_write_tape c_f2))).
Proof.
Admitted.

Lemma modnet_equivalence_checker_complete :
  forall p1 p2 f,
  (* if two well-formed programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* and they're considered not equivalent with witness f *)
  modnet_equivalence_checker p1 p2 = NotEquivalent f ->
  (* if we run them from their initial symbolic states *)
  forall s_i1 s_i2 s_f1 s_f2,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  eval_general_program_symbolic p1 s_i1 = Some s_f1 ->
  eval_general_program_symbolic p2 s_i2 = Some s_f2 ->
  (* for the concretized outputs under f *)
  forall c_f1 c_f2,
  concretize_sym_modnet_state s_f1 f = c_f1 ->
  concretize_sym_modnet_state s_f2 f = c_f2 ->
  (* either the accept flags are not equal *)
  (gps_valid c_f1 <> gps_valid c_f2)
  (* or the emitted output packets are not equal *)
  \/
  ( gps_valid c_f1 = true /\ gps_valid c_f2 = true /\
    ( List.length (sh_write_tape c_f1) <> List.length (sh_write_tape c_f2) \/
      sh_bits_read c_f1 <> sh_bits_read c_f2 \/
    ~ List.Forall (fun '(b1, b2) => b1 = b2)
      (List.combine (sh_write_tape c_f1) (sh_write_tape c_f2)))).
Proof.
Admitted.
