type nat =
| O
| S of nat
[@@deriving sexp]

type ('a, 'b) prod =
| Pair of 'a * 'b
[@@deriving sexp]

type 'a list =
| Nil
| Cons of 'a * 'a list
[@@deriving sexp]

type 'a sig0 = 'a
[@@deriving sexp]

type sumbool =
| Left
| Right
[@@deriving sexp]

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

type positive =
| XI of positive
| XO of positive
| XH
[@@deriving sexp]

type z =
| Z0
| Zpos of positive
| Zneg of positive
[@@deriving sexp]

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q -> XI (add p q)
       | XO q -> XO (add p q)
       | XH -> XI p)
    | XH -> (match y with
             | XI q -> XO (succ q)
             | XO q -> XI q
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> XI (add_carry p q)
       | XO q -> XO (add_carry p q)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q -> XO (add_carry p q)
       | XO q -> XI (add p q)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q -> XI (succ q)
       | XO q -> XO (succ q)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val eq_dec : positive -> positive -> sumbool **)

  let rec eq_dec p x0 =
    match p with
    | XI p0 -> (match x0 with
                | XI p1 -> eq_dec p0 p1
                | _ -> Right)
    | XO p0 -> (match x0 with
                | XO p1 -> eq_dec p0 p1
                | _ -> Right)
    | XH -> (match x0 with
             | XH -> Left
             | _ -> Right)
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q -> double (pos_sub p q)
       | XO q -> succ_double (pos_sub p q)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q -> pred_double (pos_sub p q)
       | XO q -> double (pos_sub p q)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q -> Zneg (XO q)
       | XO q -> Zneg (Pos.pred_double q)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val eq_dec : z -> z -> sumbool **)

  let eq_dec x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Left
             | _ -> Right)
    | Zpos p -> (match y with
                 | Zpos p0 -> Pos.eq_dec p p0
                 | _ -> Right)
    | Zneg p -> (match y with
                 | Zneg p0 -> Pos.eq_dec p p0
                 | _ -> Right)
 end

(** val shift_pos : positive -> positive -> positive **)

let shift_pos n z0 =
  Pos.iter (fun x -> XO x) z0 n

(** val two_power_pos : positive -> z **)

let two_power_pos x =
  Zpos (shift_pos x XH)

(** val zeq : z -> z -> sumbool **)

let zeq =
  Z.eq_dec

(** val natwordsize : positive -> nat **)

let natwordsize =
  Pos.to_nat

(** val modulus : positive -> z **)

let modulus =
  two_power_pos

type bit_int = z [@@deriving sexp]
  (* singleton inductive, whose constructor was mkint *)

(** val p_mod_two_p : positive -> nat -> z **)

let rec p_mod_two_p p = function
| O -> Z0
| S m ->
  (match p with
   | XI q -> Z.succ_double (p_mod_two_p q m)
   | XO q -> Z.double (p_mod_two_p q m)
   | XH -> Zpos XH)

(** val z_mod_modulus : positive -> z -> z **)

let z_mod_modulus wordsize = function
| Z0 -> Z0
| Zpos p -> p_mod_two_p p (natwordsize wordsize)
| Zneg p ->
  let r = p_mod_two_p p (natwordsize wordsize) in
  (match zeq r Z0 with
   | Left -> Z0
   | Right -> Z.sub (modulus wordsize) r)

(** val repr : positive -> z -> bit_int **)

let repr =
  z_mod_modulus

type uint8 = bit_int [@@deriving sexp]

type header = positive [@@deriving sexp]
  (* singleton inductive, whose constructor was HeaderCtr *)

type state = positive [@@deriving sexp]
  (* singleton inductive, whose constructor was StateCtr *)

type ctrl = positive [@@deriving sexp]
  (* singleton inductive, whose constructor was CtrlCtr *)

type functionArgument =
| CtrlPlaneArg of ctrl
| HeaderArg of header
| ConstantArg of uint8
| StatefulArg of state
[@@deriving sexp]

type binaryOp =
| AddOp
| SubOp
| AndOp
| OrOp
| XorOp
| MulOp
| DivOp
| ModOp
[@@deriving sexp]

type hdrOp =
| StatefulOp of binaryOp * functionArgument * functionArgument * state
| StatelessOp of binaryOp * functionArgument * functionArgument * header
[@@deriving sexp]

type matchPattern = (header, uint8) prod list [@@deriving sexp]

type seqRule =
| SeqCtr of matchPattern * hdrOp list
[@@deriving sexp]

type parRule =
| ParCtr of matchPattern * hdrOp list
[@@deriving sexp]

type matchActionRule =
| Seq of seqRule
| Par of parRule
[@@deriving sexp]

type transformer = matchActionRule list [@@deriving sexp]

type caracaraProgram =
| CaracaraProgramDef of header list * state list * ctrl list * transformer
[@@deriving sexp]


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