open Char
open Z3

(* LLM's recommended type format for uniquely tracking variables *)
module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

(* Values are typed but all bitvectors are kept 64-bit; an operation's type just
   masks its result to that width (mirroring the concrete [mk_int] mask).
   [coq_CrIntType] extracts to [coq_CrWidth]. *)
let ty_bits (t : CrVal.coq_CrIntType) : int =
  match t with CrVal.W8 -> 8 | CrVal.W16 -> 16 | CrVal.W32 -> 32 | CrVal.W64 -> 64
let mask_to ctx (bits : int) (ze : Z3.Expr.expr) : Z3.Expr.expr =
  if bits >= 64 then ze
  else Z3.BitVector.mk_and ctx ze
         (Z3.BitVector.mk_numeral ctx (string_of_int ((1 lsl bits) - 1)) 64)

let width_to_ty (bits : int) : CrVal.coq_CrIntType =
  match bits with 8 -> CrVal.W8 | 16 -> CrVal.W16 | 32 -> CrVal.W32 | _ -> CrVal.W64

(* The width statically readable off the head of an arith expr (a constant, a
   cast's [to] type, or a width-tagged binop).  [None] when it isn't locally
   determined (a bare variable, [SmtUninit], a pointer, ...). *)
let static_arith_width (e : SmtExpr.coq_SmtArithExpr) : int option =
  match e with
  | SmtExpr.SmtArithConst (_, ty) -> Some (ty_bits ty)
  | SmtExpr.SmtCast (_, to_, _) -> Some (ty_bits to_)
  | SmtExpr.SmtBitAdd (ty, _, _) | SmtExpr.SmtBitSub (ty, _, _)
  | SmtExpr.SmtBitAnd (ty, _, _) | SmtExpr.SmtBitOr (ty, _, _)
  | SmtExpr.SmtBitXor (ty, _, _) | SmtExpr.SmtBitMul (ty, _, _)
  | SmtExpr.SmtBitDiv (ty, _, _) | SmtExpr.SmtBitMod (ty, _, _) -> Some (ty_bits ty)
  | _ -> None

(* Variables ([SmtArithVar]) carry no width of their own; their width is fixed by
   the typed operation that consumes them.  This pre-pass walks the query and
   records, per variable name, the width of its enclosing op, so the SAT model can
   be reconstructed at the right [CrIntType] instead of defaulting to u64.  A
   well-typed program uses each variable at a single width; we keep the first
   width seen and leave genuinely-unconstrained variables (e.g. a header copied
   straight to output) absent, to be defaulted later. *)
let collect_var_widths (expr : SmtExpr.coq_SmtBoolExpr) : (string, int) Hashtbl.t =
  let tbl : (string, int) Hashtbl.t = Hashtbl.create 64 in
  let note (name : string) (w : int) =
    if not (Hashtbl.mem tbl name) then Hashtbl.replace tbl name w in
  let rec arith (e : SmtExpr.coq_SmtArithExpr) (expected : int option) : unit =
    match e with
    | SmtExpr.SmtArithVar name ->
        (match expected with
         | Some w -> note (Shim.coq_str_to_str name) w
         | None -> ())
    | SmtExpr.SmtArithConst (_, _) | SmtExpr.SmtUninit -> ()
    | SmtExpr.SmtConditional (cond, e1, e2) ->
        boolean cond; arith e1 expected; arith e2 expected
    | SmtExpr.SmtCast (from_, _to, e1) -> arith e1 (Some (ty_bits from_))
    | SmtExpr.SmtBitAdd (ty, e1, e2) | SmtExpr.SmtBitSub (ty, e1, e2)
    | SmtExpr.SmtBitAnd (ty, e1, e2) | SmtExpr.SmtBitOr (ty, e1, e2)
    | SmtExpr.SmtBitXor (ty, e1, e2) | SmtExpr.SmtBitMul (ty, e1, e2)
    | SmtExpr.SmtBitDiv (ty, e1, e2) | SmtExpr.SmtBitMod (ty, e1, e2) ->
        let w = Some (ty_bits ty) in arith e1 w; arith e2 w
    | SmtExpr.SmtBitNot e1 -> arith e1 expected
    (* A slice's operand carries its own width, not the slice's; don't force it. *)
    | SmtExpr.SmtBitSlice (_, _, e1) -> arith e1 None
    | SmtExpr.SmtBitsToInt bits ->
        Stdlib.List.iter boolean (Shim.listify_coq_list bits)
    | SmtExpr.SmtArrSel (m, e1, e2) -> mem m; arith e1 None; arith e2 None
    | SmtExpr.SmtPtrConst _ | SmtExpr.SmtPtrVar _ -> ()
  and boolean (e : SmtExpr.coq_SmtBoolExpr) : unit =
    match e with
    | SmtExpr.SmtTrue | SmtExpr.SmtFalse -> ()
    | SmtExpr.SmtBoolNot e1 -> boolean e1
    | SmtExpr.SmtBoolAnd (e1, e2) | SmtExpr.SmtBoolOr (e1, e2) ->
        boolean e1; boolean e2
    | SmtExpr.SmtBoolEq (e1, e2) | SmtExpr.SmtBoolLt (e1, e2) ->
        (* A comparison has no width tag, but the two sides share a width, so a
           statically-known side fixes a bare variable on the other. *)
        let w = match static_arith_width e1 with
          | Some _ as s -> s
          | None -> static_arith_width e2 in
        arith e1 w; arith e2 w
    | SmtExpr.SmtBoolVar _ -> ()  (* a lone bit; width is irrelevant (defaults u64) *)
  and mem (e : SmtExpr.coq_SmtArrExpr) : unit =
    match e with
    | SmtExpr.SmtArrInit -> ()
    | SmtExpr.SmtArrSt (m, e1, e2, e3) ->
        mem m; arith e1 None; arith e2 None; arith e3 None
  in
  boolean expr; tbl

let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx vars)
  | SmtExpr.SmtBoolEq (a1, a2) -> Z3.Boolean.mk_eq ctx (z3_expr_from_coq_smt_arith_expr a1 ctx vars) (z3_expr_from_coq_smt_arith_expr a2 ctx vars)
  | SmtExpr.SmtBoolLt (a1, a2) -> Z3.BitVector.mk_ult ctx (z3_expr_from_coq_smt_arith_expr a1 ctx vars) (z3_expr_from_coq_smt_arith_expr a2 ctx vars)
  | SmtExpr.SmtBoolVar name -> (
      (* A free bit (e.g. a symbolic packet bit) is a 1-bit bitvector const;
         the boolean holds when that bit is set.  It shares [vars] so the model
         reconstructs it as a 0/1 numeral. *)
      let name_str = Shim.coq_str_to_str name in
      let bit =
        match StringMap.find_opt name_str !vars with
        | Some z3_var -> z3_var
        | None ->
            let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 1 in
            vars := StringMap.add name_str z3_var !vars;
            z3_var in
      Z3.Boolean.mk_eq ctx bit (Z3.BitVector.mk_numeral ctx "1" 1))
and z3_expr_from_coq_smt_arith_expr (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match expr with
  | SmtExpr.SmtArithConst (v, ty) ->
      mask_to ctx (ty_bits ty)
        (Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int v)) 64)
  | SmtExpr.SmtUninit -> Z3.BitVector.mk_numeral ctx "0" 64
  | SmtExpr.SmtArithVar name -> (
    let name_str = Shim.coq_str_to_str name in
    match StringMap.find_opt name_str !vars with
    | Some z3_var -> z3_var
    | None ->
        let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 64 in
        vars := StringMap.add name_str z3_var !vars;
        z3_var)
  | SmtExpr.SmtBitsToInt bits ->
      (* Concat the bits MSB-first into a width-|bits| bitvector, then zero-extend
         to 64.  Concat and zero-extend are free in bit-blasting, so this avoids
         the ripple-carry adders an arithmetic assembly would generate. *)
      let bit_bv b =
        Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr b ctx vars)
          (Z3.BitVector.mk_numeral ctx "1" 1)
          (Z3.BitVector.mk_numeral ctx "0" 1) in
      let rec concat_bits = function
        | [] -> Z3.BitVector.mk_numeral ctx "0" 64
        | [b] -> bit_bv b
        | b :: rest -> Z3.BitVector.mk_concat ctx (bit_bv b) (concat_bits rest) in
      let ocaml_bits = Shim.listify_coq_list bits in
      let w = Stdlib.List.length ocaml_bits in
      if w = 0 then Z3.BitVector.mk_numeral ctx "0" 64
      else if w >= 64 then concat_bits ocaml_bits
      else Z3.BitVector.mk_zero_ext ctx (64 - w) (concat_bits ocaml_bits)
  | SmtExpr.SmtBitSlice (lo, hi, e) ->
      (* Bits [lo, hi) LSB-indexed, right-aligned: mirrors [CrVal.slice_val]
         ([(e >> lo) & ones(hi-lo)] in a 64-bit container). *)
      let ze = z3_expr_from_coq_smt_arith_expr e ctx vars in
      let lo_i = Shim.coq_nat_to_int lo in
      let hi_i = Shim.coq_nat_to_int hi in
      let w = hi_i - lo_i in
      if w <= 0 then Z3.BitVector.mk_numeral ctx "0" 64
      else
        mask_to ctx w
          (Z3.BitVector.mk_lshr ctx ze
             (Z3.BitVector.mk_numeral ctx (string_of_int lo_i) 64))
  | SmtExpr.SmtConditional (cond, e1, e2) ->
      Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr cond ctx vars) (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars)
  | SmtExpr.SmtCast (_from, to_, e) ->
      (* A cast masks its operand into the [to] width (the [from] check is a
         Coq-semantics concern; Z3 just resizes within the 64-bit container). *)
      mask_to ctx (ty_bits to_) (z3_expr_from_coq_smt_arith_expr e ctx vars)
  | SmtExpr.SmtBitAdd (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_add ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitSub (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_sub ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitAnd (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_and ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitOr  (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_or ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitXor (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_xor ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitNot e            -> Z3.BitVector.mk_not ctx (z3_expr_from_coq_smt_arith_expr e ctx vars)
  | SmtExpr.SmtBitMul (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_mul ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtBitDiv (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_udiv ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  (* Unsigned remainder ([mk_urem]) to match the concrete [ModOp], which is
     [Integers.modu] (unsigned); [mk_smod]/[mk_srem] would disagree on operands
     with the high bit set and make the equivalence check unsound. *)
  | SmtExpr.SmtBitMod (ty, e1, e2) -> mask_to ctx (ty_bits ty) (Z3.BitVector.mk_urem ctx (z3_expr_from_coq_smt_arith_expr e1 ctx vars) (z3_expr_from_coq_smt_arith_expr e2 ctx vars))
  | SmtExpr.SmtArrSel (_, _, _) ->
      (* TODO: Implement pointer load from memory *)
      Z3.BitVector.mk_numeral ctx "0" 64
  | SmtExpr.SmtPtrConst ptr -> (
      match ptr with
      | CrVal.CrPtr addr -> Z3.BitVector.mk_numeral ctx (string_of_int (Shim.coq_Z_to_int addr)) 64
      | CrVal.CrNilPtr -> Z3.BitVector.mk_numeral ctx "0" 64)
  | SmtExpr.SmtPtrVar name -> (
      let name_str = Shim.coq_str_to_str name in
      match StringMap.find_opt name_str !vars with
      | Some z3_var -> z3_var
      | None ->
          let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 64 in
          vars := StringMap.add name_str z3_var !vars;
          z3_var)

(* Gets all variable assignments and folds them into a valuation (linked list).
   [var_widths] (from [collect_var_widths]) gives each variable's [CrIntType];
   a variable absent from it is genuinely unconstrained, so it defaults to u64. *)
let to_vmap (var_widths : (string, int) Hashtbl.t)
    (m : Z3.Model.model) (acc : Shim.coq_ValueMap) (name : string) (z3_var : Z3.Expr.expr) : Shim.coq_ValueMap =
  match Z3.Model.eval m z3_var true with
  | Some v ->
    if Z3.Expr.is_numeral v then
      let bv_size = Z3.BitVector.get_size (Z3.Expr.get_sort v) in
      let var_str = Z3.BitVector.numeral_to_string v in
      (* All bitvectors are 64-bit in the encoding; the variable's CrIntType is
         recovered from how it is used in the query (pointer reconstruction lives
         in the memory solver, not here).  The numeral is reconstructed via
         arbitrary precision — a full-width value overflows a native int. *)
      ignore bv_size;
      let bits = match Hashtbl.find_opt var_widths name with Some b -> b | None -> 64 in
      Printf.printf "| var( %s ) : u%d := %s\n" name bits var_str;
      let cr_val = CrVal.IntVal (Shim.str_to_coq_uint64 var_str, width_to_ty bits) in
      Shim.VMap (
        Shim.str_to_coq_str name,
        cr_val,
        acc)
    else
      raise (Failure ("Expects uint but got non-numeral value for " ^ name))
  | None -> raise (Failure ("Z3 failed to return valuation for " ^ name))

let sat_check solver tracked_vars var_widths =
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown
  | Z3.Solver.SATISFIABLE -> (
    let model = Solver.get_model solver in
    match model with
    | Some m -> (
      Printf.printf "┌ SAT Valuation\n";
      let var_bindings = StringMap.bindings !tracked_vars in
      let valuations = Stdlib.List.fold_left
        (fun acc (name, z3_var) -> to_vmap var_widths m acc name z3_var)
        Shim.VMap_DNE
        var_bindings in
      Printf.printf "└\n";
      SmtTypes.SmtSat (Shim.coq_TraverseMap valuations))
    | None -> raise (Failure "Z3 returned SAT, but no valuation."))

let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  let var_widths = collect_var_widths expr in
  let z3_expr = z3_expr_from_coq_smt_bool_expr expr ctx tracked_vars in
  Solver.add solver [z3_expr];

  sat_check solver tracked_vars var_widths
