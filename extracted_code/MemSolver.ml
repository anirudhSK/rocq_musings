open CrMem

module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

let rec parse_bool_expr
  (_e : coq_Z3Bool)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
  | Z3_T -> Z3.Boolean.mk_true ctx
  | Z3_F -> Z3.Boolean.mk_false ctx
  | Z3_Neg e1 -> Z3.Boolean.mk_not ctx (parse_bool_expr e1 ctx vars)
  | Z3_Conj (e1, e2) -> Z3.Boolean.mk_and ctx
      [parse_bool_expr e1 ctx vars; parse_bool_expr e2 ctx vars]
  | Z3_Disj (e1, e2) -> Z3.Boolean.mk_or ctx
      [parse_bool_expr e1 ctx vars; parse_bool_expr e2 ctx vars]
  | Z3_Eq (e1, e2) -> Z3.Boolean.mk_eq ctx
      (parse_expr e1 ctx vars)
      (parse_expr e2 ctx vars)
and parse_expr
  (_e : coq_Z3Expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
  | Z3Arith e -> parse_arith_expr e ctx vars
  | Z3Ptr e -> parse_ptr_expr e ctx vars
  | Z3Array e -> parse_array_expr e ctx vars
  | Z3Nil ->
    print_endline("something has gone horribly wrong :(((");
    Z3.BitVector.mk_numeral ctx "0" 8
and parse_arith_expr
  (_e : arith_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
  | Z3_u8 n -> Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int n)) 8
  | Z3_u32 n -> Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int n)) 32
  | Z3_u8_var name -> (
    let name_str = (Shim.pos_to_str name) ^ "0" in
    match StringMap.find_opt name_str !vars with
    | Some s_var -> s_var
    | None ->
        let s_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 8 in
        vars := StringMap.add name_str s_var !vars;
        s_var)
  | Z3_u32_var name -> (
    let name_str = (Shim.pos_to_str name) ^ "0" in
    match StringMap.find_opt name_str !vars with
    | Some s_var -> s_var
    | None ->
        let s_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 32 in
        vars := StringMap.add name_str s_var !vars;
        s_var)
  | Z3_bitadd (e1, e2) -> Z3.BitVector.mk_add ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_arr_ld (e1, e2) -> Z3.Z3Array.mk_select ctx
    (parse_array_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
and parse_array_expr
  (_e : arr_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
    (* TODO: handle array length *)
  | Z3_arr_init _ ->
    (* The LLM made this and I don't know what it does: *)
    let arr_sort = Z3.Z3Array.mk_sort ctx
      (Z3.BitVector.mk_sort ctx 32)  (* index is 32-bit *)
      (Z3.BitVector.mk_sort ctx 8) in (* values are 8-bit *)
    Z3.Expr.mk_fresh_const ctx "arr_init" arr_sort
  | Z3_arr_var name -> (
    let name_str = (Shim.pos_to_str name) ^ "1" in
    match StringMap.find_opt name_str !vars with
    | Some a_var -> a_var
    | None ->
      let a_var = Z3.Z3Array.mk_const ctx
        (Z3.Symbol.mk_string ctx name_str)
        (Z3.BitVector.mk_sort ctx 32)
        (Z3.BitVector.mk_sort ctx 8) in
      vars := StringMap.add name_str a_var !vars;
      a_var)
  | Z3_arr_st (e1, e2, e3) -> Z3.Z3Array.mk_store ctx
      (parse_array_expr e1 ctx vars)
      (parse_arith_expr e2 ctx vars)
      (parse_arith_expr e3 ctx vars)
and parse_ptr_expr
  (_e : ptr_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  let _ = vars in
  Z3.BitVector.mk_numeral ctx "0" 8

let mem_solve (b : coq_Z3Bool) : coq_Z3Res =
  let _ = b in

  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  let z3_expr = parse_bool_expr b ctx tracked_vars in
  Z3.Solver.add solver [z3_expr];

  (* print out solver's state for debugging *)
  (* print_endline("Z3 Solver State:");
  print_endline(Z3.Solver.to_string solver);
  print_endline(""); *)

  match Z3.Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> Z3Unsat
  | Z3.Solver.UNKNOWN -> Z3Unknown
  | Z3.Solver.SATISFIABLE -> (
    print_endline("sat");
    Z3Unknown
  )
