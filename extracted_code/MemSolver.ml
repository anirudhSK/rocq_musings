open CrMem
open CrVal

module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

let rec parse_bool_expr
  (_e : bool_expr)
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
  | Z3_Lt (e1, e2) -> Z3.BitVector.mk_ult ctx
      (parse_arith_expr e1 ctx vars)
      (parse_arith_expr e2 ctx vars)
and parse_expr
  (_e : coq_Z3Expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
  | Z3Arith e -> parse_arith_expr e ctx vars
  | Z3Ptr e -> parse_ptr_expr e ctx vars
  | Z3Array e -> parse_array_expr e ctx vars
  | Z3Bool e -> parse_bool_expr e ctx vars
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
  | Z3_arith_ite (c, e1, e2) ->
    let v1 = (parse_arith_expr e1 ctx vars) in
    let v2 = (parse_arith_expr e2 ctx vars) in
    Z3.Boolean.mk_ite ctx (parse_bool_expr c ctx vars) v1 v2
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

(* Helper to extract value from Z3 model for scalar variables *)
let eval_scalar_var (m : Z3.Model.model) (name : string) (z3_var : Z3.Expr.expr) : coq_CrVal option =
  match Z3.Model.eval m z3_var true with
  | Some value ->
      (match Z3.Expr.get_sort value with
      | sort when Z3.Sort.get_sort_kind sort = Z3enums.BV_SORT ->
          let bv_size = Z3.BitVector.get_size sort in
          let num_str = Z3.BitVector.numeral_to_string value in
          let num_val = 
            try int_of_string num_str
            with _ -> 0
          in
          (* Strip the "0" suffix for display *)
          let display_name = 
            if Stdlib.String.ends_with ~suffix:"0" name then
              Stdlib.String.sub name 0 (Stdlib.String.length name - 1)
            else
              name
          in
          Printf.printf "| var( \027[1m%s\027[0m ) := %d\n" display_name num_val;
          if bv_size = 8 then
            Some (IntVal (CrUInt8 (Shim.int_to_coq_uint8 num_val)))
          else if bv_size = 32 then
            Some (IntVal (CrUInt32 (Shim.int_to_coq_uint8 num_val)))
          else
            None
      | _ -> None)
  | None -> None

(* Helper to build sval map from scalar variables (suffix "0") *)
let build_sval_map (m : Z3.Model.model) (var_bindings : (string * Z3.Expr.expr) list) 
  : (string * coq_CrVal) list =
  Stdlib.List.fold_left
    (fun acc (name, z3_var) ->
      if Stdlib.String.ends_with ~suffix:"0" name then
        match eval_scalar_var m name z3_var with
        | Some value ->
            let base_name = Stdlib.String.sub name 0 (Stdlib.String.length name - 1) in
            (base_name, value) :: acc
        | None -> acc
      else
        acc)
    []
    var_bindings

(* Helper to build aval map from array variables (suffix "1") *)
let build_aval_map (m : Z3.Model.model) (var_bindings : (string * Z3.Expr.expr) list)
  : (string * coq_CrVal coq_Array) list =
  let _ = m in
  Stdlib.List.fold_left
    (fun acc (name, _z3_var) ->
      if Stdlib.String.ends_with ~suffix:"1" name then
        let base_name = Stdlib.String.sub name 0 (Stdlib.String.length name - 1) in
        (* For now, return Unallocated for all arrays *)
        (base_name, Unallocated) :: acc
      else
        acc)
    []
    var_bindings

(* Evaluate a Z3Bool expression under a concrete model *)
let rec eval_z3_bool_concrete
  (ctx : Z3.context)
  (m : Z3.Model.model)
  (vars : var_tracker)
  (expr : bool_expr) : bool =
  match expr with
  | Z3_T -> true
  | Z3_F -> false
  | Z3_Neg e -> not (eval_z3_bool_concrete ctx m vars e)
  | Z3_Conj (e1, e2) ->
      (eval_z3_bool_concrete ctx m vars e1) && (eval_z3_bool_concrete ctx m vars e2)
  | Z3_Disj (e1, e2) ->
      (eval_z3_bool_concrete ctx m vars e1) || (eval_z3_bool_concrete ctx m vars e2)
  | Z3_Eq (e1, e2) ->
      let z3_e1 = parse_expr e1 ctx vars in
      let z3_e2 = parse_expr e2 ctx vars in
      let v1_opt = Z3.Model.eval m z3_e1 true in
      let v2_opt = Z3.Model.eval m z3_e2 true in
      (match v1_opt, v2_opt with
       | Some v1, Some v2 -> 
           (* Convert both values to strings and compare *)
           let s1 = Z3.Expr.to_string v1 in
           let s2 = Z3.Expr.to_string v2 in
           Stdlib.String.equal s1 s2
       | _ -> false)
  | Z3_Lt (e1, e2) ->
      let z3_e1 = parse_arith_expr e1 ctx vars in
      let z3_e2 = parse_arith_expr e2 ctx vars in
      let v1_opt = Z3.Model.eval m z3_e1 true in
      let v2_opt = Z3.Model.eval m z3_e2 true in
      (match v1_opt, v2_opt with
       | Some v1, Some v2 -> 
           (* Get the numerical values from bit-vectors and compare *)
           (try
              let n1 = int_of_string (Z3.BitVector.numeral_to_string v1) in
              let n2 = int_of_string (Z3.BitVector.numeral_to_string v2) in
              n1 < n2
            with _ -> false)
       | _ -> false)

let sat_check 
  (solver : Z3.Solver.solver) 
  (ctx : Z3.context)
  (tracked_vars : var_tracker)
  (p1 : coq_IM_Program)
  (p2 : coq_IM_Program) : coq_Z3Res =
  match Z3.Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> Z3Unsat
  | Z3.Solver.UNKNOWN -> Z3Unknown
  | Z3.Solver.SATISFIABLE -> (
    let model = Z3.Solver.get_model solver in
    match model with
    | Some m -> (
      Printf.printf "┌ SAT Valuation\n";
      let var_bindings = StringMap.bindings !tracked_vars in
      
      (* Build maps for sval and aval *)
      let sval_map = build_sval_map m var_bindings in
      let aval_map = build_aval_map m var_bindings in
      
      (* Check which part failed *)
      let outputs_expr = CrMem.query_outputs p1 p2 in
      let bounds_expr = CrMem.query_bounds p1 p2 in
      
      let outputs_holds = eval_z3_bool_concrete ctx m tracked_vars outputs_expr in
      let bounds_holds = eval_z3_bool_concrete ctx m tracked_vars bounds_expr in
      
      Printf.printf "| \027[1mOutputs equal:\027[0m %s\n" (if outputs_holds then "\027[32mtrue\027[0m" else "\027[31mfalse\027[0m");
      Printf.printf "| \027[1mBounds equal:\027[0m %s\n" (if bounds_holds then "\027[32mtrue\027[0m" else "\027[31mfalse\027[0m");
      
      Printf.printf "└\n";
      
      (* Create sval function *)
      let sval (var : var_id) : coq_CrVal =
        let var_name = Shim.pos_to_str var in
        match Stdlib.List.assoc_opt var_name sval_map with
        | Some value -> value
        | None -> UninitVal
      in
      
      (* Create aval function *)
      let aval (var : var_id) : coq_CrVal coq_Array =
        let var_name = Shim.pos_to_str var in
        match Stdlib.List.assoc_opt var_name aval_map with
        | Some value -> value
        | None -> Unallocated
      in
      
      Z3Sat (sval, aval))
    | None -> raise (Failure "Z3 returned SAT, but no model."))

let mem_solve (p1 : coq_IM_Program) (p2 : coq_IM_Program) : coq_Z3Res =
  let b = CrMem.query_expression p1 p2 in
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  let z3_expr = parse_bool_expr b ctx tracked_vars in
  Z3.Solver.add solver [z3_expr];

  sat_check solver ctx tracked_vars p1 p2
