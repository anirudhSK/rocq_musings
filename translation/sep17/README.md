So we have the combine file that takes both the first and second generated. We add the line:
`Extraction "combine" example_program_1.`
This causes the creation of the combine.ml file in the working directory when we run the make command and we can see data structures related to the first example programa


```
(** val h_b : header **)

let h_b =
  XI (XI XH)

(** val myAction1_op : hdrOp **)

let myAction1_op =
  StatelessOp (AddOp, (ConstantArg (repr (XO (XO (XO XH))) (Zpos XH))),
    (ConstantArg (repr (XO (XO (XO XH))) Z0)), h_b)

(** val the_table_0_seq_rule : seqRule **)

let the_table_0_seq_rule =
  SeqCtr (Nil, (Cons (myAction1_op, Nil)))

(** val the_table_0_rule : matchActionRule **)

let the_table_0_rule =
  Seq the_table_0_seq_rule

(** val headers_to_check : header list **)

let headers_to_check =
  Cons ((XI (XI XH)), Nil)

(** val state_vars_to_check : state list **)

let state_vars_to_check =
  Nil

(** val ctrl_stmts_to_check : ctrl list **)

let ctrl_stmts_to_check =
  Nil

(** val transformer_first : transformer **)

let transformer_first =
  Cons (the_table_0_rule, Nil)

(** val example_program_1 : caracaraProgram **)

let example_program_1 =
  CaracaraProgramDef (headers_to_check, state_vars_to_check,
    ctrl_stmts_to_check, transformer_first)
```


In our example with the `crc1.out` below:
```
(CaracaraProgramDef (Coq_cons (Coq_xI (Coq_xI Coq_xH))
                               Coq_nil)
                     Coq_nil
                     Coq_nil
                    (Coq_cons (Seq (SeqCtr Coq_nil
                                          (Coq_cons (StatelessOp AddOp
                                                                (ConstantArg(Zpos Coq_xH))
                                                                (ConstantArg Z0)
                                                                (Coq_xO Coq_xH))
                                                     Coq_nil)))
                               Coq_nil))
```
It perfectly matches the expanded definition of `let example_program_1 =` above

Now if we run the compile script from the translation directory it will compile the p4c compiler and then output to first+second .out with the s-expression.
TODO: I need to fix the last header output to give the number, add the trailing nils, and clean the code. Maybe clean by making it more in line with the rocq things like process first arg of this thing or something.