open BinNums
open CrIdentifiers
open CrTransformer
open Datatypes
open Integers

(** val h_b : coq_Header **)

let h_b =
  Coq_xO Coq_xH

(** val coq_MyAction1_op : coq_HdrOp **)

let coq_MyAction1_op =
  StatelessOp (AddOp, (ConstantArg
    (repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) (Zpos Coq_xH))), (ConstantArg
    (repr (Coq_xO (Coq_xO (Coq_xO Coq_xH))) Z0)), h_b)

(** val the_table_0_seq_rule : coq_SeqRule **)

let the_table_0_seq_rule =
  SeqCtr (Coq_nil, (Coq_cons (coq_MyAction1_op, Coq_nil)))

(** val the_table_0_rule : coq_MatchActionRule **)

let the_table_0_rule =
  Seq the_table_0_seq_rule

