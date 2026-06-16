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
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrDslProperties.
From MyProject Require Import CrTModSymbolicSemantics.
From MyProject Require Import CrTModConcreteSemantics.

Definition keys_from_map {T A : Type} (fn : positive -> A) (m : PMap.t T) : list A :=
  List.map fn (List.map fst (PTree.elements (snd m))).

Definition modnet_equivalence_checker
  (p1 : GeneralCaracaraProgram) (p2 : GeneralCaracaraProgram)
  : EquivalenceResult :=
  let sym1_opt := eval_general_program_symbolic_sinks p1 (init_general_symbolic_state "p1" p1) in
  let sym2_opt := eval_general_program_symbolic_sinks p2 (init_general_symbolic_state "p2" p2) in
  match sym1_opt, sym2_opt with
  | Some [sym1], Some [sym2] => (* assume one sink *)
    let h_map : PMap.t SmtArithExpr := (header_map sym1) in
    let header_ids : list Header := get_signature_from_general p1 in
    match smt_query (check_headers_and_state_vars sym1 sym2 header_ids []) with
    | SmtUnsat => Equivalent
    | SmtSat f => NotEquivalent f
    | SmtUnknown => NotEquivalentUnknown
    end
  | _, _ => NotEquivalentVariablesDiffer
  end.

Definition is_linear_chain (p : GeneralCaracaraProgram) : Prop :=
  let net := get_network_from_general p in
  is_dag net /\
  single_sink net /\
  no_fan_out net /\
  no_fan_in net.

(* NOTE/TODO: Open question about state equivalence and what it means for states to be equivalent for different network topologies *)
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
  (* then when starting from their initial concrete states *)
  forall s_i1 s_i2 c_i1 c_i2 f,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  (* if they produce some final state *)
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* there is only one such final state *)
  exists c_f1 c_f2,
  l1 = [c_f1] /\
  l2 = [c_f2] /\
  (* and the output headers are identical *)
  (forall h, In h (get_headers_from_general p1) ->
    lookup_varlike c_f1 h = lookup_varlike c_f2 h).
Proof.
Admitted.

Lemma modnet_equivalence_checker_complete :
  forall p1 p2 f,
  (* if two programs *)
  well_formed_general_program p1 ->
  well_formed_general_program p2 ->
  (* have a single source and sink *)
  is_linear_chain p1 ->
  is_linear_chain p2 ->
  (* if they're not considered equivalent *)
  modnet_equivalence_checker p1 p2 = NotEquivalent f ->
  (* then when starting from their initial concrete states *)
  forall s_i1 s_i2 c_i1 c_i2,
  s_i1 = init_general_symbolic_state "p1" p1 ->
  s_i2 = init_general_symbolic_state "p2" p2 ->
  c_i1 = concretize_sym_modnet_state s_i1 f ->
  c_i2 = concretize_sym_modnet_state s_i2 f ->
  (* if they produce a some final state *)
  forall l1 l2,
  eval_general_program_concrete_sinks p1 c_i1 = Some l1 ->
  eval_general_program_concrete_sinks p2 c_i2 = Some l2 ->
  (* they each produce a single final state *)
  exists cf_1 cf_2,
  l1 = [cf_1] /\
  l2 = [cf_2] /\
  (* and the output headers differ on at least one header *)
  (exists h, In h (get_signature_from_general p1) /\
    lookup_varlike cf_1 h <> lookup_varlike cf_2 h).
Proof.
Admitted.

Print Assumptions modnet_equivalence_checker_sound.
Print Assumptions modnet_equivalence_checker_complete.
