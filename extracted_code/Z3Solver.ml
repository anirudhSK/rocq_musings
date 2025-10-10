open Char
open Z3

(* Trusted Procedures *)
let coq_Z_to_int (n : BinNums.coq_Z) : int =
  let rec pos_to_int_ (n : BinNums.positive) (i : int) : int =
    match n with
    | Coq_xH -> 1 lsl i
    | Coq_xO n_ -> (pos_to_int_ n_ (i+1))
    | Coq_xI n_ -> (1 lsl i) + (pos_to_int_ n_ (i+1)) in
  let pos_to_int (n : BinNums.positive) : int = (pos_to_int_ n 0) in
  match n with
  | Z0 -> 0
  | Zpos n_ -> pos_to_int n_
  | Zneg n_ -> 0 - (pos_to_int n_)

let int_to_coq_uint8 (n : int) : BinNums.coq_Z =
  let rec int_to_pos (n : int) : BinNums.positive =
    if (n = 1) then Coq_xH
    else if (n mod 2 = 0) then
      Coq_xO (int_to_pos (n lsr 1))
    else
      Coq_xI (int_to_pos (n lsr 1)) in

  if (n = 0) then Z0
  else
    Zpos (int_to_pos n)

(* Trusted Procedure *)
let rec coq_str_to_str (s : String.string) : string =
  let bool_to_bit (b : Datatypes.bool) (idx : int) : int =
    match b with
    | Coq_true -> 1 lsl idx
    | Coq_false -> 0 in
  let ascii_to_char (c : Ascii.ascii) : string =
    match c with
    | Ascii (b7, b6, b5, b4, b3, b2, b1, b0) -> Char.escaped (Char.chr (
      (bool_to_bit b7 7) +
      (bool_to_bit b6 6) +
      (bool_to_bit b5 5) +
      (bool_to_bit b4 4) +
      (bool_to_bit b3 3) +
      (bool_to_bit b2 2) +
      (bool_to_bit b1 1) +
      (bool_to_bit b0 0)
    )) in
  match s with
  | EmptyString -> ""
  | String (c, rest) -> (ascii_to_char c) ^ (coq_str_to_str rest)

let char_to_ascii (c : char) : Ascii.ascii =
  let get_bit (code: int) (idx: int) : Datatypes.bool =
    match ((code lsr idx) land 1) with
    | 0 -> Coq_false
    | 1 -> Coq_true
    | _ -> raise (Failure "&0x1 should only result in 0 or 1.") in
  let code : int = Char.code c in
  Ascii (get_bit code 7, get_bit code 6, get_bit code 5, get_bit code 4,
         get_bit code 3, get_bit code 2, get_bit code 1, get_bit code 0)

let rec str_to_coq_str (s : string) : String.string =
  match s with
  | "" -> EmptyString
  | _ ->
    let c = Stdlib.String.get s 0 in
    let rest = Stdlib.String.sub s 1 (Stdlib.String.length s - 1) in
    String.String ((char_to_ascii c), (str_to_coq_str rest))

(* Recursively convert a coq_SmtBoolExpr to a Z3 expression *)
(* TODO: This function is trusted, so needs to be checked via other means like fuzzing *)
let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx; z3_expr_from_coq_smt_bool_expr e2 ctx]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx)
  | SmtExpr.SmtBoolEq (a1, a2) -> Z3.Boolean.mk_eq ctx (z3_expr_from_coq_smt_arith_expr a1 ctx) (z3_expr_from_coq_smt_arith_expr a2 ctx)
and z3_expr_from_coq_smt_arith_expr (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtConst n -> Z3.Arithmetic.Integer.mk_numeral_i ctx (coq_Z_to_int n)
  | SmtExpr.SmtArithVar name -> Z3.Arithmetic.Integer.mk_const ctx (Z3.Symbol.mk_string ctx (coq_str_to_str name))
  | SmtExpr.SmtConditional (cond, e1, e2) ->
      Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr cond ctx) (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitAdd (e1, e2) -> Z3.Arithmetic.mk_add ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitSub (e1, e2) -> Z3.Arithmetic.mk_sub ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitAnd (e1, e2) -> Z3.BitVector.mk_and ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitOr (e1, e2)  -> Z3.BitVector.mk_or ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitXor (e1, e2) -> Z3.BitVector.mk_xor ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitNot e        -> Z3.BitVector.mk_not ctx (z3_expr_from_coq_smt_arith_expr e ctx)
  | SmtExpr.SmtBitMul (e1, e2) -> Z3.Arithmetic.mk_mul ctx [z3_expr_from_coq_smt_arith_expr e1 ctx; z3_expr_from_coq_smt_arith_expr e2 ctx]
  | SmtExpr.SmtBitDiv (e1, e2) -> Z3.Arithmetic.mk_div ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)
  | SmtExpr.SmtBitMod (e1, e2) -> Z3.Arithmetic.Integer.mk_mod ctx (z3_expr_from_coq_smt_arith_expr e1 ctx) (z3_expr_from_coq_smt_arith_expr e2 ctx)

let sat_check solver =
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.SATISFIABLE ->
    (
      let model = Solver.get_model solver in
      match model with
      | Some m ->
        (
          let variables = Model.get_const_decls m in
          let valuations = Stdlib.List.fold_left
            (fun acc const ->
              let name = Z3.Symbol.to_string (Z3.FuncDecl.get_name const) in
              match Z3.Model.get_const_interp m const with
              | Some v ->
                if Z3.Expr.is_numeral v then
                  let x = Z3.Arithmetic.Integer.get_big_int v in
                  if (not ((Z.gt x (Z.of_int 255))
                        || (Z.lt x Z.zero))) then
                    let value = Z.to_int x in
                    Interface.VMap (
                      str_to_coq_str name,
                      Interface.int8_t (int_to_coq_uint8 value),
                      acc
                    )
                  else
                    raise (Failure ("Expects uint8 but got OoB value for " ^ name))
                else
                  raise (Failure ("Expects uint8 but got non-numeral value for " ^ name))
              | None -> raise (Failure ("Z3 failed to return valuation for " ^ name)))
            VMap_DNE
            variables in
          SmtTypes.SmtSat (Interface.coq_TraverseMap valuations)
        )
      | None -> raise (Failure "Z3 returned SAT, but no valuation.")
    )
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown

(* Process an SmtBoolExpr from SmtExpr to generate a query for Z3 using the OCaml Z3 API *)
let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in 
  Solver.add solver [z3_expr_from_coq_smt_bool_expr expr ctx];

  (* Check satisfiability of the constraints added to the solver *)
  sat_check solver
