From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import Maps.
From Stdlib Require Import ZArith.

Definition eval_module_concrete (m : CrModule) (ps : ConcreteState)
    : option ConcreteState :=
  match m with
  | TransformerModule _ _ _ t => Some (eval_transformer_concrete t ps)
  | ParserModule _ _ => None
  end.

Fixpoint eval_network_from_concrete
    (net           : ModuleNetwork)
    (start         : ModuleName)
    (packet        : PMap.t CrVal)
    (module_states : GeneralConcreteState)
    (fuel          : nat)
    : option (GeneralConcreteState) :=
  match fuel with
  | O => None
  | S fuel' =>
    match lookup_module net start with
    | None => None
    | Some m =>
      let key := unwrap (get_mod_name m) in
      match module_states ?? key with
      | None => None  (* module has no entry in module_states *)
      | Some local =>
        match eval_module_concrete m (inject_headers packet local) with
        | None => None
        | Some ps' =>
          let ms' := PMap.set key ps' module_states in
          (* Recurse over downstream modules; on [], fold_left returns
             the seed [Some ms'] as is, which is the desired sink behaviour. *)
          List.fold_left
            (fun acc dst =>
              match acc with
              | None => None
              | Some ms_acc =>
                  eval_network_from_concrete
                    net dst (header_map ps') ms_acc fuel'
              end)
            (downstream_modules net start)
            (Some ms')
        end
      end
    end
  end.

Definition eval_general_program_concrete'
    (p             : GeneralCaracaraProgram)
    (module_states : GeneralConcreteState)
    (fuel          : nat)
    : option (GeneralConcreteState) :=
  let net   := get_network_from_general p in
  let start := start_module net in
  match module_states ?? (unwrap start) with
  | None => None
  | Some start_state =>
    eval_network_from_concrete net start (header_map start_state) module_states fuel
  end.

Definition eval_general_program_concrete
  (p : GeneralCaracaraProgram)
  (module_states : GeneralConcreteState)
  : option (GeneralConcreteState) :=
  let mods := net_modules (get_network_from_general p) in
  let fuel := List.length mods in
  eval_general_program_concrete' p module_states fuel.

Definition eval_general_program_concrete_sinks
  (p : GeneralCaracaraProgram)
  (module_states : GeneralConcreteState)
  : option (list ConcreteState) :=
  match eval_general_program_concrete p module_states with
  | None        => None
  | Some ledger =>
      Some (get_sink_states (get_network_from_general p) ledger)
  end.
