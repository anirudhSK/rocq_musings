open Char
open Z3

(* LLM's recommended type format for uniquely tracking variables *)
module CoqStringOrd = struct
  type t = Stdlib.String.t
  let compare = Stdlib.String.compare
end
module StringMap = Stdlib.Map.Make(CoqStringOrd)
type var_tracker = Z3.Expr.expr StringMap.t ref

(* ------------------------------------------------------------------ *)
(* A [CrVal] is a value AND a type tag, so an arith expression lowers to the
   PAIR [(value, tag)]:

     tag 0 = ErrorVal, 1 = UninitVal, 2..5 = IntVal at W8/W16/W32/W64

   Values stay 64-bit and unmasked; only op *results* are masked, mirroring
   [mk_int], so a variable's value may exceed its nominal width -- which is what
   [eval_smt_arith] permits, since comparisons test full values.

   A new constructor must lower its tag as well as its value.  Dropping the tag
   makes [SmtQuery.smt_query_sound_some] false rather than imprecise; see
   SOUNDNESS.md on the type-tag encoding. *)
let tag_bits = 3
let tag_err = 0
let tag_uninit = 1

let ty_bits (t : CrVal.coq_CrIntType) : int =
  match t with CrVal.W8 -> 8 | CrVal.W16 -> 16 | CrVal.W32 -> 32 | CrVal.W64 -> 64
let ty_tag (t : CrVal.coq_CrIntType) : int =
  match t with CrVal.W8 -> 2 | CrVal.W16 -> 3 | CrVal.W32 -> 4 | CrVal.W64 -> 5
let tag_to_ty (n : int) : CrVal.coq_CrIntType option =
  match n with
  | 2 -> Some CrVal.W8 | 3 -> Some CrVal.W16
  | 4 -> Some CrVal.W32 | 5 -> Some CrVal.W64
  | _ -> None

let mask_to ctx (bits : int) (ze : Z3.Expr.expr) : Z3.Expr.expr =
  if bits >= 64 then ze
  else Z3.BitVector.mk_and ctx ze
         (Z3.BitVector.mk_numeral ctx (string_of_int ((1 lsl bits) - 1)) 64)

let mk_tag ctx (n : int) = Z3.BitVector.mk_numeral ctx (string_of_int n) tag_bits
let tag_eq ctx t n = Z3.Boolean.mk_eq ctx t (mk_tag ctx n)
(* Tags 2..5 are the [IntVal] ones; everything else is Uninit or Error. *)
let tag_is_int ctx t =
  Z3.Boolean.mk_and ctx
    [Z3.BitVector.mk_uge ctx t (mk_tag ctx 2);
     Z3.BitVector.mk_ule ctx t (mk_tag ctx 5)]

let cell_bits = tag_bits + 64
let pack_cell ctx v t = Z3.BitVector.mk_concat ctx t v
let cell_value ctx c = Z3.BitVector.mk_extract ctx 63 0 c
let cell_tag ctx c = Z3.BitVector.mk_extract ctx (cell_bits - 1) 64 c

module PhysTbl = Hashtbl.Make (struct
  type t = Obj.t
  let equal = ( == )
  let hash = Hashtbl.hash
end)

let memo_bool : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
(* An arith node memoises the (value, tag) pair it lowers to. *)
let memo_arith : (Z3.Expr.expr * Z3.Expr.expr) PhysTbl.t = PhysTbl.create 1024
let memo_arr : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
let memo_find (t : 'a PhysTbl.t) (k : 'k) : 'a option = PhysTbl.find_opt t (Obj.repr k)
let memo_add (t : 'a PhysTbl.t) (k : 'k) (v : 'a) : unit = PhysTbl.replace t (Obj.repr k) v
(* Assumptions emitted while lowering, conjoined with the goal in [solve].
   Context-bound like the memo tables, so reset alongside them. *)
let side_constraints : Z3.Expr.expr list ref = ref []
(* The single Z3 term every [SmtArrInit] lowers to; see [get_undeclared_arr]. *)
let undeclared_arr : Z3.Expr.expr option ref = ref None
let reset_lowering_memo () =
  PhysTbl.reset memo_bool; PhysTbl.reset memo_arith; PhysTbl.reset memo_arr;
  side_constraints := []; undeclared_arr := None

let arr_lens : (string, int) Hashtbl.t = Hashtbl.create 16

let collect_arr_lens (expr : SmtExpr.coq_SmtBoolExpr) : unit =
  Hashtbl.reset arr_lens;
  let seen_b : unit PhysTbl.t = PhysTbl.create 1024 in
  let seen_a : unit PhysTbl.t = PhysTbl.create 1024 in
  let seen_m : unit PhysTbl.t = PhysTbl.create 256 in
  let fresh (t : unit PhysTbl.t) (k : Obj.t) : bool =
    if PhysTbl.mem t k then false else (PhysTbl.add t k (); true) in
  let rec arith (e : SmtExpr.coq_SmtArithExpr) : unit =
    if fresh seen_a (Obj.repr e) then
    match e with
    | SmtExpr.SmtArithVar _ | SmtExpr.SmtArithConst (_, _) | SmtExpr.SmtUninit -> ()
    | SmtExpr.SmtConditional (cond, e1, e2) -> boolean cond; arith e1; arith e2
    | SmtExpr.SmtCast (_, _, e1) -> arith e1
    | SmtExpr.SmtBitAdd (_, e1, e2) | SmtExpr.SmtBitSub (_, e1, e2)
    | SmtExpr.SmtBitAnd (_, e1, e2) | SmtExpr.SmtBitOr (_, e1, e2)
    | SmtExpr.SmtBitXor (_, e1, e2) | SmtExpr.SmtBitMul (_, e1, e2)
    | SmtExpr.SmtBitDiv (_, e1, e2) | SmtExpr.SmtBitMod (_, e1, e2) -> arith e1; arith e2
    | SmtExpr.SmtBitNot e1 -> arith e1
    | SmtExpr.SmtBitSlice (_, _, e1) -> arith e1
    | SmtExpr.SmtBitsToInt bits -> Stdlib.List.iter boolean (Shim.listify_coq_list bits)
    | SmtExpr.SmtArrSel (m, idx) -> mem m; arith idx
  and boolean (e : SmtExpr.coq_SmtBoolExpr) : unit =
    if fresh seen_b (Obj.repr e) then
    match e with
    | SmtExpr.SmtTrue | SmtExpr.SmtFalse | SmtExpr.SmtBoolVar _ -> ()
    | SmtExpr.SmtBoolNot e1 -> boolean e1
    | SmtExpr.SmtBoolAnd (e1, e2) | SmtExpr.SmtBoolOr (e1, e2) -> boolean e1; boolean e2
    | SmtExpr.SmtBoolEq (e1, e2) | SmtExpr.SmtBoolLt (e1, e2) -> arith e1; arith e2
    | SmtExpr.SmtArrEq (_, a1, a2) -> mem a1; mem a2
  and mem (e : SmtExpr.coq_SmtArrExpr) : unit =
    if fresh seen_m (Obj.repr e) then
    match e with
    | SmtExpr.SmtArrInit -> ()
    | SmtExpr.SmtArrVar (name, len) ->
        Hashtbl.replace arr_lens (Shim.coq_str_to_str name)
          (int_of_string (Shim.coq_Z_to_str len))
    | SmtExpr.SmtArrSt (m, idx, v) -> mem m; arith idx; arith v
    | SmtExpr.SmtArrIte (c, m1, m2) -> boolean c; mem m1; mem m2
  in
  boolean expr

let tag_vars : Z3.Expr.expr StringMap.t ref = ref StringMap.empty

let mem_sort ctx =
  Z3.Z3Array.mk_sort ctx (Z3.BitVector.mk_sort ctx 64)
                         (Z3.BitVector.mk_sort ctx cell_bits)

(* The one Z3 term every [SmtArrInit] lowers to.  They must share it:
   [eval_smt_mem] sends them all to the single value [Unallocated], but two
   [mk_fresh_const]s are freely unequal under [mk_eq].  Fresh rather than named
   so it cannot collide with an [SmtArrVar]; context-bound, hence reset with the
   memo tables.  Redundant with [memo_arr] today -- see memo-memo.txt, which
   also explains why this is the one node where a memo miss changes the answer
   rather than costing time.  Guarded by [TestEquality]'s "witness: two
   undeclared regions agree". *)
let get_undeclared_arr ctx =
  match !undeclared_arr with
  | Some z -> z
  | None ->
      let z = Z3.Expr.mk_fresh_const ctx "arr_undeclared" (mem_sort ctx) in
      undeclared_arr := Some z; z

let rec z3_expr_from_coq_smt_bool_expr (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match memo_find memo_bool expr with Some z -> z | None ->
  let z = (match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolAnd (e1, e2) -> Z3.Boolean.mk_and ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolOr (e1, e2) -> Z3.Boolean.mk_or ctx [z3_expr_from_coq_smt_bool_expr e1 ctx vars; z3_expr_from_coq_smt_bool_expr e2 ctx vars]
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (z3_expr_from_coq_smt_bool_expr e ctx vars)
  | SmtExpr.SmtBoolEq (a1, a2) ->
      let (v1, t1) = lower_arith a1 ctx vars in
      let (v2, t2) = lower_arith a2 ctx vars in
      Z3.Boolean.mk_and ctx
        [Z3.Boolean.mk_eq ctx t1 t2;
         Z3.Boolean.mk_or ctx
           [Z3.Boolean.mk_not ctx (tag_is_int ctx t1);
            Z3.Boolean.mk_eq ctx v1 v2]]
  | SmtExpr.SmtBoolLt (a1, a2) ->
      let (v1, t1) = lower_arith a1 ctx vars in
      let (v2, t2) = lower_arith a2 ctx vars in
      Z3.Boolean.mk_and ctx
        [Z3.Boolean.mk_eq ctx t1 t2;
         tag_is_int ctx t1;
         Z3.BitVector.mk_ult ctx v1 v2]
  | SmtExpr.SmtBoolVar name -> (
      (* A free bit (e.g. a symbolic packet bit) is a 1-bit bitvector const;
         the boolean holds when that bit is set.  It shares [vars] so the model
         reconstructs it as a 0/1 numeral.  No tag: [eval_smt_bool] reads it as
         "nonzero", and a non-IntVal valuation entry reads as false, which a
         0/1 reconstruction already satisfies. *)
      let name_str = Shim.coq_str_to_str name in
      let bit =
        match StringMap.find_opt name_str !vars with
        | Some z3_var -> z3_var
        | None ->
            let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 1 in
            vars := StringMap.add name_str z3_var !vars;
            z3_var in
      Z3.Boolean.mk_eq ctx bit (Z3.BitVector.mk_numeral ctx "1" 1))
  | SmtExpr.SmtArrEq (_, a1, a2) ->
      Z3.Boolean.mk_eq ctx
        (z3_arr_from_coq_smt_arr_expr a1 ctx vars)
        (z3_arr_from_coq_smt_arr_expr a2 ctx vars)) in
  memo_add memo_bool expr z; z

(* Lower an arith expression to its (value, tag) pair.  Every case mirrors the
   corresponding case of [SmtExpr.eval_smt_arith], including where that yields
   ErrorVal. *)
and lower_arith (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr * Z3.Expr.expr =
  match memo_find memo_arith expr with Some z -> z | None ->
  let bv64 n = Z3.BitVector.mk_numeral ctx n 64 in
  let binop_at ty e1 e2 (f : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr) =
    let (v1, t1) = lower_arith e1 ctx vars in
    let (v2, t2) = lower_arith e2 ctx vars in
    let ok = Z3.Boolean.mk_and ctx
               [tag_eq ctx t1 (ty_tag ty); tag_eq ctx t2 (ty_tag ty)] in
    (mask_to ctx (ty_bits ty) (f v1 v2),
     Z3.Boolean.mk_ite ctx ok (mk_tag ctx (ty_tag ty)) (mk_tag ctx tag_err)) in
  let z = (match expr with
  | SmtExpr.SmtArithConst (v, ty) ->
      (mask_to ctx (ty_bits ty) (bv64 (Shim.coq_Z_to_str v)), mk_tag ctx (ty_tag ty))
  | SmtExpr.SmtUninit -> (bv64 "0", mk_tag ctx tag_uninit)
  | SmtExpr.SmtArithVar name ->
      (* [eval_smt_arith] passes an [IntVal] through with its own type and turns
         anything else into ErrorVal, so the tag is free over the [IntVal] tags
         plus ErrorVal -- never Uninit. *)
      let name_str = Shim.coq_str_to_str name in
      let v = (match StringMap.find_opt name_str !vars with
        | Some z3_var -> z3_var
        | None ->
            let z3_var = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name_str) 64 in
            vars := StringMap.add name_str z3_var !vars; z3_var) in
      let t_free = (match StringMap.find_opt name_str !tag_vars with
        | Some z3_var -> z3_var
        | None ->
            let z3_var = Z3.BitVector.mk_const ctx
                           (Z3.Symbol.mk_string ctx (name_str ^ "#tag")) tag_bits in
            tag_vars := StringMap.add name_str z3_var !tag_vars; z3_var) in
      (v, Z3.Boolean.mk_ite ctx (tag_is_int ctx t_free) t_free (mk_tag ctx tag_err))
  | SmtExpr.SmtBitsToInt bits ->
      let bit_bv b =
        Z3.Boolean.mk_ite ctx (z3_expr_from_coq_smt_bool_expr b ctx vars)
          (Z3.BitVector.mk_numeral ctx "1" 1)
          (Z3.BitVector.mk_numeral ctx "0" 1) in
      let rec concat_bits = function
        | [] -> bv64 "0"
        | [b] -> bit_bv b
        | b :: rest -> Z3.BitVector.mk_concat ctx (bit_bv b) (concat_bits rest) in
      let ocaml_bits = Shim.listify_coq_list bits in
      let w = Stdlib.List.length ocaml_bits in
      let v =
        if w = 0 then bv64 "0"
        else if w >= 64 then concat_bits ocaml_bits
        else Z3.BitVector.mk_zero_ext ctx (64 - w) (concat_bits ocaml_bits) in
      (v, mk_tag ctx (ty_tag CrVal.W64))
  | SmtExpr.SmtBitSlice (lo, hi, e) ->
      let (ze, te) = lower_arith e ctx vars in
      let lo_i = Shim.coq_nat_to_int lo in
      let hi_i = Shim.coq_nat_to_int hi in
      let w = hi_i - lo_i in
      let v =
        if w <= 0 then bv64 "0"
        else mask_to ctx w
               (Z3.BitVector.mk_lshr ctx ze (bv64 (string_of_int lo_i))) in
      (v, Z3.Boolean.mk_ite ctx (tag_is_int ctx te)
            (mk_tag ctx (ty_tag CrVal.W64)) (mk_tag ctx tag_err))
  | SmtExpr.SmtConditional (cond, e1, e2) ->
      let c = z3_expr_from_coq_smt_bool_expr cond ctx vars in
      let (v1, t1) = lower_arith e1 ctx vars in
      let (v2, t2) = lower_arith e2 ctx vars in
      (Z3.Boolean.mk_ite ctx c v1 v2, Z3.Boolean.mk_ite ctx c t1 t2)
  | SmtExpr.SmtCast (from_, to_, e) ->
      let (ze, te) = lower_arith e ctx vars in
      (mask_to ctx (ty_bits to_) ze,
       Z3.Boolean.mk_ite ctx (tag_eq ctx te (ty_tag from_))
         (mk_tag ctx (ty_tag to_)) (mk_tag ctx tag_err))
  | SmtExpr.SmtBitAdd (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_add ctx)
  | SmtExpr.SmtBitSub (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_sub ctx)
  | SmtExpr.SmtBitAnd (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_and ctx)
  | SmtExpr.SmtBitOr  (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_or ctx)
  | SmtExpr.SmtBitXor (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_xor ctx)
  | SmtExpr.SmtBitMul (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_mul ctx)
  | SmtExpr.SmtBitDiv (ty, e1, e2) ->
      (* Concrete [divu] yields 0 on a zero divisor ([Z.div _ 0 = 0]), whereas
         Z3's [bvudiv] by zero is all-ones; guard so the two agree, else the
         equivalence check is unsound at a zero divisor.  ([urem]/[modu] already
         agree -- both return the dividend on a zero divisor -- so [SmtBitMod]
         needs no such guard.) *)
      binop_at ty e1 e2 (fun z1 z2 ->
        Z3.Boolean.mk_ite ctx (Z3.Boolean.mk_eq ctx z2 (bv64 "0"))
          (bv64 "0") (Z3.BitVector.mk_udiv ctx z1 z2))
  (* Unsigned remainder ([mk_urem]) to match the concrete [ModOp], which is
     [Integers.modu] (unsigned); [mk_smod]/[mk_srem] would disagree on operands
     with the high bit set and make the equivalence check unsound. *)
  | SmtExpr.SmtBitMod (ty, e1, e2) -> binop_at ty e1 e2 (Z3.BitVector.mk_urem ctx)
  | SmtExpr.SmtBitNot e ->
      let (ze, te) = lower_arith e ctx vars in
      let nz = Z3.BitVector.mk_not ctx ze in
      let v =
        Stdlib.List.fold_left
          (fun acc ty ->
            Z3.Boolean.mk_ite ctx (tag_eq ctx te (ty_tag ty))
              (mask_to ctx (ty_bits ty) nz) acc)
          (bv64 "0") [CrVal.W64; CrVal.W32; CrVal.W16; CrVal.W8] in
      (v, Z3.Boolean.mk_ite ctx (tag_is_int ctx te) te (mk_tag ctx tag_err))
  | SmtExpr.SmtArrSel (m, idx) ->
      let za = z3_arr_from_coq_smt_arr_expr m ctx vars in
      let (zi, ti) = lower_arith idx ctx vars in
      let len = bv64 (Shim.coq_Z_to_str (SmtExpr.smt_arr_len m)) in
      let ok = Z3.Boolean.mk_and ctx
                 [tag_is_int ctx ti; Z3.BitVector.mk_ult ctx zi len] in
      let cell = Z3.Z3Array.mk_select ctx za zi in
      (Z3.Boolean.mk_ite ctx ok (cell_value ctx cell) (bv64 "0"),
       Z3.Boolean.mk_ite ctx ok (cell_tag ctx cell) (mk_tag ctx tag_err))) in
  memo_add memo_arith expr z; z

and z3_arr_from_coq_smt_arr_expr (expr : SmtExpr.coq_SmtArrExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match memo_find memo_arr expr with Some z -> z | None ->
  let z = (match expr with
  | SmtExpr.SmtArrInit -> get_undeclared_arr ctx
  | SmtExpr.SmtArrVar (name, len) -> (
      let name_str = Shim.coq_str_to_str name in
      match StringMap.find_opt name_str !vars with
      | Some z3_var -> z3_var
      | None ->
          let z3_var = Z3.Z3Array.mk_const ctx (Z3.Symbol.mk_string ctx name_str)
                         (Z3.BitVector.mk_sort ctx 64)
                         (Z3.BitVector.mk_sort ctx cell_bits) in
          (* A free array's cell tags are otherwise unconstrained, so a model
             could pick 6 or 7 -- bit patterns no [CrVal] denotes and that
             [to_amap] cannot reconstruct.  Pin them to 0..5 here rather than
             normalising in [SmtArrSel]: [SmtArrEq] lowers to [mk_eq] on whole
             arrays and so reads cells RAW, and a read-side fix would let it see
             differences no valuation can express.  Only 0..[len) needs pinning
             -- reads and stores are guarded to that range and [to_amap] reads no
             further, while beyond it both sides of an [SmtArrEq] are the same
             term.  Excluding these models loses nothing real: every [CrVal]
             carries a tag in 0..5. *)
          let n = Stdlib.int_of_string (Shim.coq_Z_to_str len) in
          for i = 0 to n - 1 do
            let cell = Z3.Z3Array.mk_select ctx z3_var
                         (Z3.BitVector.mk_numeral ctx (string_of_int i) 64) in
            side_constraints :=
              Z3.BitVector.mk_ule ctx (cell_tag ctx cell)
                (mk_tag ctx (ty_tag CrVal.W64)) :: !side_constraints
          done;
          vars := StringMap.add name_str z3_var !vars;
          z3_var)
  | SmtExpr.SmtArrSt (m, idx, v) ->
      let za = z3_arr_from_coq_smt_arr_expr m ctx vars in
      let (zi, ti) = lower_arith idx ctx vars in
      let (zv, tv) = lower_arith v ctx vars in
      let len = Z3.BitVector.mk_numeral ctx
                  (Shim.coq_Z_to_str (SmtExpr.smt_arr_len m)) 64 in
      let ok = Z3.Boolean.mk_and ctx
                 [tag_is_int ctx ti; Z3.BitVector.mk_ult ctx zi len] in
      Z3.Boolean.mk_ite ctx ok
        (Z3.Z3Array.mk_store ctx za zi (pack_cell ctx zv tv))
        za
  | SmtExpr.SmtArrIte (c, m1, m2) ->
      Z3.Boolean.mk_ite ctx
        (z3_expr_from_coq_smt_bool_expr c ctx vars)
        (z3_arr_from_coq_smt_arr_expr m1 ctx vars)
        (z3_arr_from_coq_smt_arr_expr m2 ctx vars)) in
  memo_add memo_arr expr z; z

(* Reconstruct one scalar variable from the model. *)
let to_vmap (m : Z3.Model.model) (acc : Shim.coq_ValueMap)
    (name : string) (z3_var : Z3.Expr.expr) : Shim.coq_ValueMap =
  match Z3.Model.eval m z3_var true with
  | Some v ->
    if Z3.Expr.is_numeral v then
      let var_str = Z3.BitVector.numeral_to_string v in
      (* The tag is absent for a packet bit ([SmtBoolVar]), which has none; such
         a variable is only ever read as nonzero/zero, so u64 is right. *)
      let ty =
        match StringMap.find_opt name !tag_vars with
        | None -> Some CrVal.W64
        | Some t ->
          (match Z3.Model.eval m t true with
           | Some tv when Z3.Expr.is_numeral tv ->
               tag_to_ty (int_of_string (Z3.BitVector.numeral_to_string tv))
           | _ -> Some CrVal.W64) in
      (match ty with
       | Some ty ->
         Printf.printf "| var( %s ) : u%d := %s\n" name (ty_bits ty) var_str;
         Shim.VMap (Shim.str_to_coq_str name,
                    CrVal.IntVal (Shim.str_to_coq_uint64 var_str, ty), acc)
       | None ->
         (* The tag says this is not an IntVal.  Cosmetic only, unlike the
            [to_amap] case: [eval_smt_arith] coerces every non-[IntVal] the
            valuation gives a variable to [ErrorVal] anyway, matching the
            [ite (tag_is_int t) t tag_err] the lowering wraps a free tag in.
            Printing "error" just says what the value will be read as.
            ([SmtArrSel] has no such coercion -- it returns the cell verbatim
            -- which is why a region's cells must reconstruct exactly.) *)
         Printf.printf "| var( %s ) := error\n" name;
         Shim.VMap (Shim.str_to_coq_str name, CrVal.ErrorVal, acc))
    else
      raise (Failure ("Expects uint but got non-numeral value for " ^ name))
  | None -> raise (Failure ("Z3 failed to return valuation for " ^ name))

(* Read a memory region back out of the model. *)
let to_amap (ctx : Z3.context) (m : Z3.Model.model)
    (acc : Shim.coq_ArrayMap) (name : string) (z3_var : Z3.Expr.expr) : Shim.coq_ArrayMap =
  let len = match Hashtbl.find_opt arr_lens name with Some l -> l | None -> 0 in
  let cells = ref [] in
  let bytes = ref (Maps.PMap.init CrVal.Uninit) in
  for i = len - 1 downto 0 do
    let idx = Z3.BitVector.mk_numeral ctx (string_of_int i) 64 in
    let cell = Z3.Z3Array.mk_select ctx z3_var idx in
    let get e = match Z3.Model.eval m e true with
      | Some x when Z3.Expr.is_numeral x -> Some (Z3.BitVector.numeral_to_string x)
      | _ -> None in
    match get (cell_value ctx cell), get (cell_tag ctx cell) with
    | Some vs, Some ts ->
        let cv = match tag_to_ty (int_of_string ts) with
          | Some ty ->
              cells := Printf.sprintf "%s:u%d" vs (ty_bits ty) :: !cells;
              CrVal.IntVal (Shim.str_to_coq_uint64 vs, ty)
          (* Tag 1 is the only [UninitVal].  Tag 0 is [ErrorVal] -- which
             cells hold routinely, since [byte_of_val] sends every non-[IntVal]
             there -- and 6/7 are normalised to [tag_err] on read, above.
             Collapsing all of them to [UninitVal] would report a valuation the
             query does not satisfy ([eqb ErrorVal UninitVal = false]). *)
          | None ->
              if int_of_string ts = tag_uninit
              then (cells := "-" :: !cells; CrVal.UninitVal)
              else (cells := "err" :: !cells; CrVal.ErrorVal) in
        (* Inner keys are offsets shifted by one; see [CrVal.offset_to_key]. *)
        bytes := Maps.PMap.set (Shim.int_to_pos (i + 1)) (CrVal.Init cv) !bytes
    | _ -> cells := "?" :: !cells
  done;
  Printf.printf "| mem( %s ) : len=%d := [%s]\n" name len
    (Stdlib.String.concat ", " !cells);
  Shim.AMap (Shim.str_to_coq_str name,
             CrVal.Allocated { CrVal.arr_len = Shim.int_to_coq_uint64 len;
                               CrVal.arr_bytes = !bytes },
             acc)

let sat_check ctx solver tracked_vars =
  match Solver.check solver [] with
  | Z3.Solver.UNSATISFIABLE -> SmtTypes.SmtUnsat
  | Z3.Solver.UNKNOWN -> SmtTypes.SmtUnknown
  | Z3.Solver.SATISFIABLE -> (
    let model = Solver.get_model solver in
    match model with
    | Some m -> (
      Printf.printf "┌ SAT Valuation\n";
      let var_bindings = StringMap.bindings !tracked_vars in
      (* [tracked_vars] now holds two sorts; split on the Z3 sort rather than on
         the name, so a region and a scalar can never be confused. *)
      let is_arr (_, z3_var) =
        Z3.Sort.get_sort_kind (Z3.Expr.get_sort z3_var) = Z3enums.ARRAY_SORT in
      let arr_bindings = Stdlib.List.filter is_arr var_bindings in
      let int_bindings =
        Stdlib.List.filter (fun b -> Stdlib.not (is_arr b)) var_bindings in
      let valuations = Stdlib.List.fold_left
        (fun acc (name, z3_var) -> to_vmap m acc name z3_var)
        Shim.VMap_DNE
        int_bindings in
      let arrays = Stdlib.List.fold_left
        (fun acc (name, z3_var) -> to_amap ctx m acc name z3_var)
        Shim.AMap_DNE
        arr_bindings in
      Printf.printf "└\n";
      SmtTypes.SmtSat (Shim.mk_valuation valuations arrays))
    | None -> raise (Failure "Z3 returned SAT, but no valuation."))

let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  collect_arr_lens expr;
  (* Entries cache Z3 expressions belonging to a specific context, so they must
     not survive into the next query, which builds a fresh one.  The tag consts
     are context-bound too. *)
  reset_lowering_memo ();
  tag_vars := StringMap.empty;
  let z3_expr = z3_expr_from_coq_smt_bool_expr expr ctx tracked_vars in
  Solver.add solver (z3_expr :: !side_constraints);

  sat_check ctx solver tracked_vars
