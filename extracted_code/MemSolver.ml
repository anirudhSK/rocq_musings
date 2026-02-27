open CrMem
open CrVal

module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

let u8_sfx = 0
let u16_sfx = 1
let u32_sfx = 2
let u64_sfx = 3
let arr_sfx = 4
let suffixes = [|
  "000";
  "001";
  "010";
  "011";
  "100";
|]

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
    print_endline("Met nil expression");
    Z3.BitVector.mk_numeral ctx "0" 8
and parse_arith_expr
  (_e : arith_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
  | Z3_int8 n -> Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int n)) 8
  | Z3_int32 n -> Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int n)) 32
  | Z3_int8_var name -> (
    let name_str = (Shim.pos_to_str name) ^ suffixes.(u8_sfx) in
    match StringMap.find_opt name_str !vars with
    | Some s_var -> s_var
    | None ->
        let s_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 8 in
        vars := StringMap.add name_str s_var !vars;
        s_var)
  | Z3_int32_var name -> (
    let name_str = (Shim.pos_to_str name) ^ suffixes.(u32_sfx) in
    match StringMap.find_opt name_str !vars with
    | Some s_var -> s_var
    | None ->
        let s_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 32 in
        vars := StringMap.add name_str s_var !vars;
        s_var)
  | Z3_bv_add (e1, e2) -> Z3.BitVector.mk_add ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_sub (e1, e2) -> Z3.BitVector.mk_sub ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_shl (e1, e2) -> Z3.BitVector.mk_shl ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_ashr (e1, e2) -> Z3.BitVector.mk_ashr ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_and (e1, e2) -> Z3.BitVector.mk_and ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_or (e1, e2) -> Z3.BitVector.mk_or ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_bv_xor (e1, e2) -> Z3.BitVector.mk_xor ctx
    (parse_arith_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
(* TODO: rename such that it mirrors Z3 *)
  | Z3_bv_not e1 -> Z3.BitVector.mk_not ctx (parse_arith_expr e1 ctx vars)
  | Z3_arr_sel (e1, e2) -> Z3.Z3Array.mk_select ctx
    (parse_array_expr e1 ctx vars)
    (parse_arith_expr e2 ctx vars)
  | Z3_arith_ite (c, e1, e2) ->
    Z3.Boolean.mk_ite ctx
      (parse_bool_expr c ctx vars)
      (parse_arith_expr e1 ctx vars)
      (parse_arith_expr e2 ctx vars)
and parse_array_expr
  (_e : arr_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  match _e with
    (* TODO: handle array length *)
  | Z3_arr_init _ ->
    let arr_sort = Z3.Z3Array.mk_sort ctx
      (Z3.BitVector.mk_sort ctx 32)  (* index is 32-bit *)
      (Z3.BitVector.mk_sort ctx 8) in (* values are 8-bit *)
    Z3.Expr.mk_fresh_const ctx "arr_init" arr_sort
  | Z3_arr_var name -> (
    let name_str = (Shim.pos_to_str name) ^ suffixes.(arr_sfx) in
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
  | Z3_arr_ite (c, e1, e2) ->
      Z3.Boolean.mk_ite ctx
        (parse_bool_expr c ctx vars)
        (parse_array_expr e1 ctx vars)
        (parse_array_expr e2 ctx vars)
and parse_ptr_expr
  (_e : ptr_expr)
  (ctx : Z3.context)
  (vars : var_tracker) : Z3.Expr.expr =
  (* TODO: get around to doing this *)
  let _ = vars in
  print_endline("dummy pointer handler called");
  Z3.BitVector.mk_numeral ctx "0" 64

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
            Some (IntVal (CrUInt32 (Shim.int_to_coq_uint32 num_val)))
          else
            None
      | _ -> None)
  | None -> None

(* Helper suffix list and stripping for scalar variables. *)
let scalar_suffixes =
  [| suffixes.(u8_sfx); suffixes.(u16_sfx); suffixes.(u32_sfx); suffixes.(u64_sfx) |]

(* Given a variable name, return the base name if it ends with a known scalar suffix. *)
let strip_scalar_suffix (name : string) : string option =
  let open Stdlib in
  let name_len = String.length name in
  let rec find_suffix i =
    if i >= Array.length scalar_suffixes then
      None
    else
      let sfx = scalar_suffixes.(i) in
      let sfx_len = String.length sfx in
      if sfx_len <= name_len
         && String.sub name (name_len - sfx_len) sfx_len = sfx
      then
        Some (String.sub name 0 (name_len - sfx_len))
      else
        find_suffix (i + 1)
  in
  find_suffix 0

(* Helper to build sval map from scalar variables (suffixes defined in [scalar_suffixes]). *)
let build_sval_map (m : Z3.Model.model) (var_bindings : (string * Z3.Expr.expr) list) 
  : (string * coq_CrVal) list =
  Stdlib.List.fold_left
    (fun acc (name, z3_var) ->
      match strip_scalar_suffix name with
      | Some base_name -> (
          match eval_scalar_var m name z3_var with
          | Some value -> (base_name, value) :: acc
          | None -> acc)
      | None -> acc)
    []
    var_bindings

(* Helper to build aval map from array variables (suffix matching arr_sfx).
   We extract the Z3 function interpretation of each array, read out
   the explicitly-defined entries, and build a coq_MemBlock. *)
let build_aval_map (_ctx : Z3.context) (m : Z3.Model.model) (var_bindings : (string * Z3.Expr.expr) list)
  : (string * coq_CrVal coq_Array) list =
  Stdlib.List.fold_left
    (fun acc (name, z3_var) ->
      if Stdlib.String.ends_with ~suffix:suffixes.(arr_sfx) name then
        let base_name = Stdlib.String.sub name 0
          (Stdlib.String.length name - Stdlib.String.length suffixes.(arr_sfx)) in
        (* Try to extract the array interpretation from the model *)
        let arr =
          match Z3.Model.eval m z3_var true with
          | Some arr_expr ->
            (* Read entries by walking the Z3 expression for store chains.
               Z3 array models are typically: (store (store ... (const v) i1 v1) i2 v2)
               We collect all index-value pairs, plus the default value from
               a (const ...) base if present. *)
            let rec extract_stores expr acc_entries =
              if Z3.Z3Array.is_store expr then
                let args = Z3.Expr.get_args expr in
                match args with
                | [base_arr; idx_expr; val_expr] ->
                  let idx =
                    try int_of_string (Z3.BitVector.numeral_to_string idx_expr)
                    with _ -> -1 in
                  let v =
                    try int_of_string (Z3.BitVector.numeral_to_string val_expr)
                    with _ -> 0 in
                  if idx >= 0 then
                    extract_stores base_arr ((idx, v) :: acc_entries)
                  else
                    extract_stores base_arr acc_entries
                | _ -> (acc_entries, None)
              else
                (* Check if the base is a const array — extract default value *)
                let default_val =
                  try
                    let decl = Z3.Expr.get_func_decl expr in
                    let dk = Z3.FuncDecl.get_decl_kind decl in
                    if dk = Z3enums.OP_CONST_ARRAY then
                      match Z3.Expr.get_args expr with
                      | [default_expr] ->
                        let v = int_of_string (Z3.BitVector.numeral_to_string default_expr) in
                        Some v
                      | _ -> None
                    else None
                  with _ -> None
                in
                (acc_entries, default_val)
            in
            let (entries, default_val) = extract_stores arr_expr [] in
            if entries = [] && default_val = None then
              Unallocated
            else
              (* Determine length as max index + 1 *)
              let max_idx = Stdlib.List.fold_left
                (fun mx (i, _) -> max mx i) 0 entries in
              let len = max_idx + 1 in
              (* Initialize PMap with the default value if we have one *)
              let init_status = match default_val with
                | Some v -> Init (IntVal (CrUInt8 (Shim.int_to_coq_uint8 v)))
                | None -> Uninit
              in
              let bytes = Stdlib.List.fold_left
                (fun pmap (i, v) ->
                  let key = Shim.int_to_pos (i + 1) in (* PMap keys are 1-indexed positives *)
                  let cval = IntVal (CrUInt8 (Shim.int_to_coq_uint8 v)) in
                  Maps.PMap.set key (Init cval) pmap)
                (Maps.PMap.init init_status)
                entries in
              Allocated { arr_len = Shim.int_to_coq_uint32 len; arr_bytes = bytes }
          | None -> Unallocated
        in
        (base_name, arr) :: acc
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
           let sort1 = Z3.Expr.get_sort v1 in
           let sort2 = Z3.Expr.get_sort v2 in
           if Z3.Sort.get_sort_kind sort1 = Z3enums.BV_SORT &&
              Z3.Sort.get_sort_kind sort2 = Z3enums.BV_SORT
           then
             (try
                let n1 = int_of_string (Z3.BitVector.numeral_to_string v1) in
                let n2 = int_of_string (Z3.BitVector.numeral_to_string v2) in
                n1 = n2
              with _ -> false)
           else
             Z3.Sort.equal sort1 sort2 && Z3.Expr.equal v1 v2
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
      let aval_map = build_aval_map ctx m var_bindings in
      
      (* Print array valuations *)
      Stdlib.List.iter (fun (name, arr) ->
        match arr with
        | Unallocated ->
          Printf.printf "| arr( \027[1m%s\027[0m ) := <unallocated>\n" name
        | Allocated { arr_len; arr_bytes } ->
          let len = Shim.coq_Z_to_int arr_len in
          Printf.printf "| arr( \027[1m%s\027[0m ) := [" name;
          for i = 0 to len - 1 do
            let key = Shim.int_to_pos (i + 1) in
            let v = match Maps.PMap.get key arr_bytes with
              | Init (IntVal (CrUInt8 n)) -> Shim.coq_Z_to_int n
              | _ -> 0
            in
            if i > 0 then Printf.printf ", ";
            Printf.printf "%d" v
          done;
          Printf.printf "] (len=%d)\n" len
      ) aval_map;
      
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

      let fmode = match (outputs_holds, bounds_holds) with
      | (false, true) -> ValueMismatch
      | (true, false) -> BoundsMismatch
      | (false, false) -> FullMismatch
      | (true, true) -> raise (Failure "a cosmic ray must have flipped a bit")
      in
      
      Z3Sat (sval, aval, fmode))
    | None -> raise (Failure "Z3 returned SAT, but no model."))

let mem_solve (p1 : coq_IM_Program) (p2 : coq_IM_Program) : coq_Z3Res =
  let b = CrMem.query_expression p1 p2 in
  let ctx = Z3.mk_context [] in
  let solver = Z3.Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  print_endline("casting query to z3 expression...");
  let z3_expr = parse_bool_expr b ctx tracked_vars in
  print_endline("adding query to solver...");
  Z3.Solver.add solver [z3_expr];

  print_endline("running query...");
  sat_check solver ctx tracked_vars p1 p2
