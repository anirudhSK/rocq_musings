(* Concrete<->symbolic parser commutation lemmas: the supporting machinery for
   [SmtParserQuery]'s soundness and completeness (the parser analogue of
   [ConcreteToSymbolicLemmas] for transformers).  Culminates in
   [eval_parser_commute]. *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import Bool.
From Stdlib Require Import ZArith.
From Stdlib Require Import micromega.Lia.
From MyProject Require Import Integers.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrParser.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import SmtTypes.
From MyProject Require Import CrVarLike.
From MyProject Require Import CrConcreteSemanticsParser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import Maps.
From MyProject Require Import PMapHelperLemmas.
From MyProject Require Import SmtHelperLemmas.

(* ====================================================================== *)
(* Value-level sublemmas for the commutation proof.                       *)
(* ====================================================================== *)
