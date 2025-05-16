(* Scheduler section below *)
Require Import List.
Import ListNotations.
Require Import Strings.String.
From MyProject Require Export CrIdentifiers.

(* Dummy function definition for now *)
Definition function : Type := (nat -> nat -> nat).

(* A PNode is a tuple consisting of:
   (1) a Header,
   (2) a start index,
   (3) an end index,
   (4) a bit-pattern,
   (5) a function *)
Definition PNode : Type := Header * nat * nat * list bool * function.

(* A PTree is a tree structure where each node is a PNode.
   The tree can be either a leaf node (PNodeCtr) or an internal node (PTreeCtr) with two children. *)
Inductive PTree :=
    | PTreeCtr (n : PNode) (t1 : PTree) (t2 : PTree)
    | PNodeCtr (n : PNode).

Definition Scheduler : Type := PTree.