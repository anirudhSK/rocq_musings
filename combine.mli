
type nat =
| O
| S of nat

type ('a, 'b) prod =
| Pair of 'a * 'b

type 'a list =
| Nil
| Cons of 'a * 'a list

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

val add : nat -> nat -> nat

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val eq_dec : positive -> positive -> sumbool
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val eq_dec : z -> z -> sumbool
 end

val shift_pos : positive -> positive -> positive

val two_power_pos : positive -> z

val zeq : z -> z -> sumbool

val natwordsize : positive -> nat

val modulus : positive -> z

type bit_int = z
  (* singleton inductive, whose constructor was mkint *)

val p_mod_two_p : positive -> nat -> z

val z_mod_modulus : positive -> z -> z

val repr : positive -> z -> bit_int

type uint8 = bit_int

type header =
  positive
  (* singleton inductive, whose constructor was HeaderCtr *)

type state = positive
  (* singleton inductive, whose constructor was StateCtr *)

type ctrl = positive
  (* singleton inductive, whose constructor was CtrlCtr *)

type functionArgument =
| CtrlPlaneArg of ctrl
| HeaderArg of header
| ConstantArg of uint8
| StatefulArg of state

type binaryOp =
| AddOp
| SubOp
| AndOp
| OrOp
| XorOp
| MulOp
| DivOp
| ModOp

type hdrOp =
| StatefulOp of binaryOp * functionArgument * functionArgument * state
| StatelessOp of binaryOp * functionArgument * functionArgument * header

type matchPattern = (header, uint8) prod list

type seqRule =
| SeqCtr of matchPattern * hdrOp list

type parRule =
| ParCtr of matchPattern * hdrOp list

type matchActionRule =
| Seq of seqRule
| Par of parRule

type transformer = matchActionRule list

type caracaraProgram =
| CaracaraProgramDef of header list * state list * ctrl list * transformer

val h_b : header

val myAction1_op : hdrOp

val the_table_0_seq_rule : seqRule

val the_table_0_rule : matchActionRule

val headers_to_check : header list

val state_vars_to_check : state list

val ctrl_stmts_to_check : ctrl list

val transformer_first : transformer

val example_program_1 : caracaraProgram
