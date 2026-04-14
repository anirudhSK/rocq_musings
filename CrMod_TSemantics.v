From Stdlib Require Import List.
Import ListNotations.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrDsl.
From MyProject Require Import CrModule.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrConcreteSemanticsTransformer.

Definition oops_all_transformers (P : GeneralCaracaraProgram) : Prop :=
  forall m n,
    n = get_network_from_general P ->
    In m (all_modules n) -> is_transformer_module m = true.

(* For now we assume that all modules in a network are transformers.
   If needed, return a failure type if a Parser Module is encountered.
*)

(* ------------------------------------------------------------------ *)
(* 1.  Single-module evaluation                                        *)
(* ------------------------------------------------------------------ *)

(* Evaluate one module against a concrete state.
   Returns None if the module is a ParserModule (not yet supported). *)
Definition eval_module_concrete (m : CrModule) (ps : ConcreteState)
    : option ConcreteState :=
  match m with
  | TransformerModule _ t => Some (eval_transformer_concrete t ps)
  | ParserModule _ _      => None
  end.

(* ------------------------------------------------------------------ *)
(* 2.  Helper: flatten a list of option-lists                         *)
(* ------------------------------------------------------------------ *)

(* If every element is Some, concatenate the inner lists.
   If any element is None, return None. *)
Fixpoint sequence_options {A : Type} (l : list (option (list A)))
    : option (list A) :=
  match l with
  | []             => Some []
  | None    :: _   => None
  | Some xs :: rest =>
      match sequence_options rest with
      | None    => None
      | Some ys => Some (xs ++ ys)
      end
  end.

(* ------------------------------------------------------------------ *)
(* 3.  Network evaluation                                             *)
(* ------------------------------------------------------------------ *)

(* Evaluate the transformer network starting from module [start], threading
   [ps] through each transformer in topological (forward) order.

   Because wf_module_network includes is_dag, execution always terminates;
   the fuel parameter makes that termination structurally obvious to Coq.
   A fuel value >= the number of modules reachable from [start] is always
   sufficient.

   Returns:
     None      -- a ParserModule was encountered, the named module was absent,
                  or fuel was exhausted
     Some pss  -- one ConcreteState per sink reachable from [start];
                  the single-module case returns a singleton list *)
Fixpoint eval_network_from_concrete
    (net   : ModuleNetwork)
    (start : ModuleName)
    (ps    : ConcreteState)
    (fuel  : nat)
    : option (list ConcreteState) :=
  match fuel with
  | O       => None
  | S fuel' =>
    match lookup_module net start with
    | None   => None
    | Some m =>
      match eval_module_concrete m ps with
      | None    => None
      | Some ps' =>
        match downstream_modules net start with
        | []    => Some [ps']   (* sink: packet exits the network here *)
        | nexts =>
          (* forward ps' to every downstream module and collect results *)
          sequence_options
            (List.map
              (fun dst => eval_network_from_concrete net dst ps' fuel')
              nexts)
        end
      end
    end
  end.

(* ------------------------------------------------------------------ *)
(* 4.  Top-level program evaluator                                    *)
(* ------------------------------------------------------------------ *)

(* Evaluate a GeneralCaracaraProgram: enter at start_module with state [ps].
   [fuel] should be at least the length of the longest path in the network. *)
Definition eval_general_program_concrete
    (p    : GeneralCaracaraProgram)
    (ps   : ConcreteState)
    (fuel : nat)
    : option (list ConcreteState) :=
  let net := get_network_from_general p in
  eval_network_from_concrete net (start_module net) ps fuel.
