From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import CrConcreteSemanticsTransformer.
From MyProject Require Import Maps.
From MyProject Require Import PosWrapper.
From Stdlib Require Import ZArith.

Definition inject_headers (packet : PMap.t CrVal) (local : ConcreteState)
    : ConcreteState :=
  {| ctrl_map   := ctrl_map local;
     header_map := packet;
     state_map  := state_map local |}.

Definition eval_module_concrete (m : CrModule) (ps : ConcreteState)
    : option ConcreteState :=
  match m with
  | TransformerModule _ _ _ t => Some (eval_transformer_concrete t ps)
  | ParserModule _ _ => None
  end.

(* Note: Assumes that network is a tree *)
Fixpoint eval_network_from_concrete
    (net           : ModuleNetwork)
    (start         : ModuleName)
    (packet        : PMap.t CrVal)
    (module_states : PMap.t ConcreteState)
    (fuel          : nat)
    : option (list ConcreteState * PMap.t ConcreteState) :=
  match fuel with
  | O => None
  | S fuel' =>
    match lookup_module net start with
    | None => None
    | Some m =>
      (* evaluate m next *)
      let key := unwrap (get_mod_name m) in
      match module_states ?? key with
      | None => None  (* module has no entry in module_states *)
      | Some local =>
        match eval_module_concrete m (inject_headers packet local) with
        | None => None
        | Some ps' =>
          let ms' := PMap.set key ps' module_states in
          match downstream_modules net start with
          | [] => Some ([ps'], ms')
          | nexts =>
            List.fold_left
              (fun acc dst =>
                match acc with
                | None => None
                | Some (sink_states, ms_acc) =>
                  match eval_network_from_concrete
                          net dst (header_map ps') ms_acc fuel' with
                  | None => None
                  | Some (sinks', ms'') =>
                    Some (sink_states ++ sinks', ms'')
                  end
                end)
              nexts (Some ([], ms'))
          end
        end
      end
    end
  end.

Definition eval_general_program_concrete'
    (p             : GeneralCaracaraProgram)
    (module_states : PMap.t ConcreteState)
    (fuel          : nat)
    : option (list ConcreteState * PMap.t ConcreteState) :=
  let net   := get_network_from_general p in
  let start := start_module net in
  match module_states ?? (unwrap start) with
  | None => None
  | Some start_state =>
    eval_network_from_concrete net start (header_map start_state) module_states fuel
  end.

Definition eval_general_program_concrete
  (p : GeneralCaracaraProgram)
  (module_states : PMap.t ConcreteState)
  : option (list ConcreteState * PMap.t ConcreteState) :=
  let mods := all_modules (get_network_from_general p) in
  let fuel := List.length mods in
  eval_general_program_concrete' p module_states fuel.
