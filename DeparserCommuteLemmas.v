(* Concrete<->symbolic deparser commutation: the deparser analogue of
   [ParserCommuteLemmas].  Culminates in [eval_deparser_commute], which says
   concretizing the symbolic deparser output equals running the concrete
   deparser on the concretized input.  A deparser never fails, so this is a
   plain equality (no option / accept condition). *)

From Stdlib Require Import List.
Import ListNotations.
From Stdlib Require Import ZArith.
From MyProject Require Import CrIdentifiers.
From MyProject Require Import CrProgramState.
From MyProject Require Import CrVal.
From MyProject Require Import SmtExpr.
From MyProject Require Import CrDeparser.
From MyProject Require Import CrConcreteSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsDeparser.
From MyProject Require Import CrSymbolicSemanticsParser.
From MyProject Require Import ParserCommuteLemmas.
From MyProject Require Import SmtHelperLemmas.
From MyProject Require Import CrVarLike.
From MyProject Require Import Maps.
