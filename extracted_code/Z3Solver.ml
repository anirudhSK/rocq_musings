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
let memo_arith : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
let memo_arr : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
let memo_find (t : 'a PhysTbl.t) (k : 'k) : 'a option = PhysTbl.find_opt t (Obj.repr k)
let memo_add (t : 'a PhysTbl.t) (k : 'k) (v : 'a) : unit = PhysTbl.replace t (Obj.repr k) v
(* The single Z3 term every [SmtArrInit] lowers to; see [get_undeclared_arr]. *)
let undeclared_arr : Z3.Expr.expr option ref = ref None
let reset_lowering_memo () =
  PhysTbl.reset memo_bool; PhysTbl.reset memo_arith; PhysTbl.reset memo_arr;
  undeclared_arr := None

(* ------------------------------------------------------------------ *)
(* The compiler pass, with the recursive knot tied here.

   [SmtCompile] provides [cstep_*], the compiler for ONE node given compilers
   for its children.  Tying that knot in Rocq -- which [SmtCompile.compile_bool]
   also does, and which the correctness theorem is stated about -- gives a
   structural [Fixpoint], and a structural fixpoint over a DAG visits a shared
   subterm once per PATH.  A transformer chain merges at every rule, so the
   paths are exponential in the chain length: compiling [bpf_O0] against itself
   that way did not finish in ten minutes, against 0.01s for the whole query
   before any of this existed.

   So the knot is tied here instead, over a cache.  Everything semantic stays in
   [SmtCompile.v]; what is trusted here is only that a cache hit returns what was
   stored, which is the same specification the lowering memos already carry.
   [SmtCompile.compile_bool_step] is the licence: [compile_*] satisfies these
   three equations, so any fixpoint that does is [compile_*].

   Keyed on PHYSICAL identity, for the reason memo-memo.txt records about the
   lowering memos: the polymorphic [Hashtbl] hashes a bounded prefix, so the
   merge nodes of a chain all collide, and resolving a collision runs structural
   [=], which walks the DAG as a tree.  That is worst exactly when the terms are
   most shared -- comparing a program against itself.

   NOT reset per call, unlike the lowering memos: these hold [SmtExpr] terms,
   which belong to no Z3 context, so a repeated query keeps its compilation. *)
let memo_cb : SmtExpr.coq_SmtBoolExpr PhysTbl.t = PhysTbl.create 1024
let memo_ca : SmtCompile.carith PhysTbl.t = PhysTbl.create 1024
let memo_cm : SmtExpr.coq_SmtArrExpr PhysTbl.t = PhysTbl.create 1024

let rec compile_b (e : SmtExpr.coq_SmtBoolExpr) : SmtExpr.coq_SmtBoolExpr =
  match PhysTbl.find_opt memo_cb (Obj.repr e) with
  | Some z -> z
  | None ->
      let z = SmtCompile.cstep_bool compile_b compile_a compile_m e in
      PhysTbl.replace memo_cb (Obj.repr e) z; z

and compile_a (e : SmtExpr.coq_SmtArithExpr) : SmtCompile.carith =
  match PhysTbl.find_opt memo_ca (Obj.repr e) with
  | Some z -> z
  | None ->
      let z = SmtCompile.cstep_arith compile_b compile_a compile_m e in
      PhysTbl.replace memo_ca (Obj.repr e) z; z

and compile_m (a : SmtExpr.coq_SmtArrExpr) : SmtExpr.coq_SmtArrExpr =
  match PhysTbl.find_opt memo_cm (Obj.repr a) with
  | Some z -> z
  | None ->
      let z = SmtCompile.cstep_arr compile_b compile_a compile_m a in
      PhysTbl.replace memo_cm (Obj.repr a) z; z

let compile_core (e : SmtExpr.coq_SmtBoolExpr) : SmtExpr.coq_SmtBoolExpr =
  compile_b e

let memo_lb : Datatypes.bool PhysTbl.t = PhysTbl.create 1024
let memo_la : Datatypes.bool PhysTbl.t = PhysTbl.create 1024
let memo_lm : Datatypes.bool PhysTbl.t = PhysTbl.create 1024

let rec lc_b e =
  match PhysTbl.find_opt memo_lb (Obj.repr e) with Some z -> z | None ->
    let z = SmtCompile.lcstep_bool lc_b lc_a lc_m e in
    PhysTbl.replace memo_lb (Obj.repr e) z; z
and lc_a e =
  match PhysTbl.find_opt memo_la (Obj.repr e) with Some z -> z | None ->
    let z = SmtCompile.lcstep_arith lc_b lc_a lc_m e in
    PhysTbl.replace memo_la (Obj.repr e) z; z
and lc_m a =
  match PhysTbl.find_opt memo_lm (Obj.repr a) with Some z -> z | None ->
    let z = SmtCompile.lcstep_arr lc_b lc_a lc_m a in
    PhysTbl.replace memo_lm (Obj.repr a) z; z

let length_consistent (e : SmtExpr.coq_SmtBoolExpr) : bool =
  match lc_b e with Datatypes.Coq_true -> true | Datatypes.Coq_false -> false

let arr_lens : (string, int) Hashtbl.t = Hashtbl.create 16

(* The same region declarations, kept in Rocq's types, in the order first seen
   and deduplicated by name.  [SmtCompile.regions_wf] turns this into the
   "every cell is a byte" conjunct; keeping the [string]/[uint64] the term
   already carries avoids round-tripping a name through [coq_str_to_str].

   Completeness matters in one direction only.  A region this misses loses its
   conjunct, so the solver may pick cells no [CrVal] denotes -- that is the
   unsound direction, and it is the same traversal [to_amap] already trusts for
   lengths.  A spurious entry is harmless: the conjunct stays vacuous in Rocq
   whatever region it names. *)
let arr_decls :
  (String.string, MyInts.uint64) Datatypes.prod Stdlib.List.t ref = ref []

let collect_arr_lens (expr : SmtExpr.coq_SmtBoolExpr) : unit =
  Hashtbl.reset arr_lens;
  arr_decls := [];
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
    | SmtExpr.SmtVarVal _ | SmtExpr.SmtVarTag _ -> ()
    | SmtExpr.SmtCellVal (m, idx) | SmtExpr.SmtCellTag (m, idx) -> mem m; arith idx
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
        let n = Shim.coq_str_to_str name in
        if Stdlib.not (Hashtbl.mem arr_lens n) then
          arr_decls := Datatypes.Coq_pair (name, len) :: !arr_decls;
        Hashtbl.replace arr_lens n (int_of_string (Shim.coq_Z_to_str len))
    | SmtExpr.SmtArrSt (m, idx, v) -> mem m; arith idx; arith v
    | SmtExpr.SmtStCell (m, idx, v, t) -> mem m; arith idx; arith v; arith t
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

(* ------------------------------------------------------------------ *)
(* Free variables.

   Created once per name and shared through [vars], so the model reader finds
   the same term the lowering built. *)
let get_var ctx (vars : var_tracker) (name : Stdlib.String.t) (width : int) =
  match StringMap.find_opt name !vars with
  | Some z -> z
  | None ->
      let z = Z3.BitVector.mk_const ctx (Z3.Symbol.mk_string ctx name) width in
      vars := StringMap.add name z !vars; z

let get_tag_var ctx (vars : var_tracker) (name : Stdlib.String.t) =
  ignore vars;
  match StringMap.find_opt name !tag_vars with
  | Some z -> z
  | None ->
      let z = Z3.BitVector.mk_const ctx
                (Z3.Symbol.mk_string ctx (name ^ "#tag")) 64 in
      tag_vars := StringMap.add name z !tag_vars;
      z

let get_region_var ctx (vars : var_tracker) (name : String.string)
    (_len : MyInts.uint64) =
  let name_str = Shim.coq_str_to_str name in
  match StringMap.find_opt name_str !vars with
  | Some z -> z
  | None ->
      let z = Z3.Z3Array.mk_const ctx (Z3.Symbol.mk_string ctx name_str)
                (Z3.BitVector.mk_sort ctx 64)
                (Z3.BitVector.mk_sort ctx cell_bits) in
      vars := StringMap.add name_str z !vars;
      z

(* ------------------------------------------------------------------ *)

let not_core what =
  raise (Failure ("Z3Solver: " ^ what ^ " is not in the core fragment -- \
                  SmtCompile.compile_bool should have eliminated it"))

let rec lower_bool (expr : SmtExpr.coq_SmtBoolExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match memo_find memo_bool expr with Some z -> z | None ->
  let z = (match expr with
  | SmtExpr.SmtTrue -> Z3.Boolean.mk_true ctx
  | SmtExpr.SmtFalse -> Z3.Boolean.mk_false ctx
  | SmtExpr.SmtBoolNot e -> Z3.Boolean.mk_not ctx (lower_bool e ctx vars)
  | SmtExpr.SmtBoolAnd (e1, e2) ->
      Z3.Boolean.mk_and ctx [lower_bool e1 ctx vars; lower_bool e2 ctx vars]
  | SmtExpr.SmtBoolOr (e1, e2) ->
      Z3.Boolean.mk_or ctx [lower_bool e1 ctx vars; lower_bool e2 ctx vars]
  | SmtExpr.SmtBoolEq (a1, a2) ->
      Z3.Boolean.mk_eq ctx (lower_arith a1 ctx vars) (lower_arith a2 ctx vars)
  | SmtExpr.SmtBoolLt (a1, a2) ->
      Z3.BitVector.mk_ult ctx (lower_arith a1 ctx vars) (lower_arith a2 ctx vars)
  | SmtExpr.SmtBoolVar name ->
      let name_str = Shim.coq_str_to_str name in
      let bit = get_var ctx vars name_str 1 in
      Z3.Boolean.mk_eq ctx bit (Z3.BitVector.mk_numeral ctx "1" 1)
  (* EXCEPTION 1 of 3.  Z3's array equality is extensional; [arr_agree_upto]
     compares [n] cells.  The two coincide because both sides of every merge the
     checker builds are rooted at the same [SmtArrVar] -- proved as
     [eval_general_program_symbolic_mem_rooted] -- and a bounded conjunction is
     quadratic and unusably slow.  See SOUNDNESS.md and memo-memo.txt. *)
  | SmtExpr.SmtArrEq (_, a1, a2) ->
      Z3.Boolean.mk_eq ctx (lower_arr a1 ctx vars) (lower_arr a2 ctx vars)) in
  memo_add memo_bool expr z; z

and lower_arith (expr : SmtExpr.coq_SmtArithExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match memo_find memo_arith expr with Some z -> z | None ->
  let bv64 n = Z3.BitVector.mk_numeral ctx n 64 in
  let bin f e1 e2 = f (lower_arith e1 ctx vars) (lower_arith e2 ctx vars) in
  let z = (match expr with
  | SmtExpr.SmtArithConst (v, _) -> bv64 (Shim.coq_Z_to_str v)
  | SmtExpr.SmtVarVal name -> get_var ctx vars (Shim.coq_str_to_str name) 64
  | SmtExpr.SmtVarTag name -> get_tag_var ctx vars (Shim.coq_str_to_str name)
  | SmtExpr.SmtBitAdd (_, e1, e2) -> bin (Z3.BitVector.mk_add ctx) e1 e2
  | SmtExpr.SmtBitSub (_, e1, e2) -> bin (Z3.BitVector.mk_sub ctx) e1 e2
  | SmtExpr.SmtBitAnd (_, e1, e2) -> bin (Z3.BitVector.mk_and ctx) e1 e2
  | SmtExpr.SmtBitOr  (_, e1, e2) -> bin (Z3.BitVector.mk_or ctx) e1 e2
  | SmtExpr.SmtBitXor (_, e1, e2) -> bin (Z3.BitVector.mk_xor ctx) e1 e2
  | SmtExpr.SmtBitMul (_, e1, e2) -> bin (Z3.BitVector.mk_mul ctx) e1 e2
  | SmtExpr.SmtBitMod (_, e1, e2) -> bin (Z3.BitVector.mk_urem ctx) e1 e2
  (* EXCEPTION 2 of 3.  [Integers.divu] is [Z.div], and [Z.div _ 0] is 0, where
     [bvudiv] by zero is all-ones.  One [ite] makes the node faithful, and it is
     provably the right one, so it is cheaper to keep here than to grow every
     compiled division by a guard the compiler cannot see is redundant. *)
  | SmtExpr.SmtBitDiv (_, e1, e2) ->
      bin (fun z1 z2 ->
        Z3.Boolean.mk_ite ctx (Z3.Boolean.mk_eq ctx z2 (bv64 "0"))
          (bv64 "0") (Z3.BitVector.mk_udiv ctx z1 z2)) e1 e2
  | SmtExpr.SmtBitNot e -> Z3.BitVector.mk_not ctx (lower_arith e ctx vars)
  | SmtExpr.SmtConditional (c, e1, e2) ->
      Z3.Boolean.mk_ite ctx (lower_bool c ctx vars)
        (lower_arith e1 ctx vars) (lower_arith e2 ctx vars)
  (* EXCEPTION 3 of 3.  [slice_val] is a shift and a mask, and the fragment has
     no shift node of its own; giving it one would buy nothing, since [lo] and
     [hi] are static so both operands are constants. *)
  | SmtExpr.SmtBitSlice (lo, hi, e) ->
      let ze = lower_arith e ctx vars in
      let lo_i = Shim.coq_nat_to_int lo in
      let w = Shim.coq_nat_to_int hi - lo_i in
      if w <= 0 then bv64 "0"
      else mask_to ctx w (Z3.BitVector.mk_lshr ctx ze (bv64 (string_of_int lo_i)))
  | SmtExpr.SmtBitsToInt bits ->
      let bit_bv b =
        Z3.Boolean.mk_ite ctx (lower_bool b ctx vars)
          (Z3.BitVector.mk_numeral ctx "1" 1) (Z3.BitVector.mk_numeral ctx "0" 1) in
      let rec concat_bits = function
        | [] -> bv64 "0"
        | [b] -> bit_bv b
        | b :: rest -> Z3.BitVector.mk_concat ctx (bit_bv b) (concat_bits rest) in
      let ocaml_bits = Shim.listify_coq_list bits in
      let w = Stdlib.List.length ocaml_bits in
      if w = 0 then bv64 "0"
      else if w >= 64 then concat_bits ocaml_bits
      else Z3.BitVector.mk_zero_ext ctx (64 - w) (concat_bits ocaml_bits)
  | SmtExpr.SmtCellVal (m, idx) ->
      cell_value ctx (Z3.Z3Array.mk_select ctx (lower_arr m ctx vars)
                        (lower_arith idx ctx vars))
  | SmtExpr.SmtCellTag (m, idx) ->
      Z3.BitVector.mk_zero_ext ctx (64 - tag_bits)
        (cell_tag ctx (Z3.Z3Array.mk_select ctx (lower_arr m ctx vars)
                         (lower_arith idx ctx vars)))
  | SmtExpr.SmtUninit -> not_core "SmtUninit"
  | SmtExpr.SmtArithVar _ -> not_core "SmtArithVar"
  | SmtExpr.SmtCast _ -> not_core "SmtCast"
  | SmtExpr.SmtArrSel _ -> not_core "SmtArrSel") in
  memo_add memo_arith expr z; z

and lower_arr (expr : SmtExpr.coq_SmtArrExpr) (ctx : Z3.context) (vars : var_tracker)
  : Z3.Expr.expr =
  match memo_find memo_arr expr with Some z -> z | None ->
  let z = (match expr with
  | SmtExpr.SmtArrInit -> get_undeclared_arr ctx
  | SmtExpr.SmtArrVar (name, len) -> get_region_var ctx vars name len
  | SmtExpr.SmtStCell (m, idx, v, t) ->
      let zt = Z3.BitVector.mk_extract ctx (tag_bits - 1) 0 (lower_arith t ctx vars) in
      Z3.Z3Array.mk_store ctx (lower_arr m ctx vars) (lower_arith idx ctx vars)
        (pack_cell ctx (lower_arith v ctx vars) zt)
  | SmtExpr.SmtArrIte (c, m1, m2) ->
      let a1 = lower_arr m1 ctx vars in
      let a2 = lower_arr m2 ctx vars in
      if Z3.Expr.equal a1 a2 then a1
      else Z3.Boolean.mk_ite ctx (lower_bool c ctx vars) a1 a2
  | SmtExpr.SmtArrSt _ -> not_core "SmtArrSt") in
  memo_add memo_arr expr z; z

(* Reconstruct one scalar variable from the model. *)
let to_vmap (m : Z3.Model.model) (acc : Shim.coq_ValueMap)
    (name : string) (z3_var : Z3.Expr.expr) : Shim.coq_ValueMap =
  let num e =
    match Z3.Model.eval m e true with
    | Some x when Z3.Expr.is_numeral x -> Some (Z3.BitVector.numeral_to_string x)
    | _ -> None in
  match num z3_var with
  | None -> raise (Failure ("Z3 failed to return valuation for " ^ name))
  | Some var_str ->
    let tag =
      match StringMap.find_opt name !tag_vars with
      | None -> ty_tag CrVal.W64
      | Some t -> (match num t with Some ts -> int_of_string ts | None -> ty_tag CrVal.W64) in
    let cv =
      match tag_to_ty tag with
      | Some ty -> CrVal.IntVal (Shim.str_to_coq_uint64 var_str, ty)
      | None -> if tag = tag_uninit then CrVal.UninitVal else CrVal.ErrorVal in
    Shim.VMap (Shim.str_to_coq_str name, cv, acc)

(* Read a memory region back out of the model. *)
let to_amap (ctx : Z3.context) (m : Z3.Model.model)
    (acc : Shim.coq_ArrayMap) (name : string) (z3_var : Z3.Expr.expr) : Shim.coq_ArrayMap =
  let len = match Hashtbl.find_opt arr_lens name with Some l -> l | None -> 0 in
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
          | Some ty -> CrVal.IntVal (Shim.str_to_coq_uint64 vs, ty)
          | None ->
              if int_of_string ts = tag_uninit
              then CrVal.UninitVal else CrVal.ErrorVal in
        (* Inner keys are offsets shifted by one; see [CrVal.offset_to_key]. *)
        bytes := Maps.PMap.set (Shim.int_to_pos (i + 1)) (CrVal.Init cv) !bytes
    | _ -> ()
  done;
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
      SmtTypes.SmtSat (Shim.mk_valuation valuations arrays))
    | None -> raise (Failure "Z3 returned SAT, but no valuation."))

let solve (expr : SmtExpr.coq_SmtBoolExpr) =
  if Stdlib.not (length_consistent expr) then
    raise (Failure "Z3Solver.solve: query is not length-consistent (an array \
                    merge joins regions of different declared lengths); \
                    SmtCompile.compile_bool is not sound on it");
  let core = compile_core expr in
  let ctx = mk_context [] in
  let solver = Solver.mk_solver ctx None in
  let tracked_vars = ref StringMap.empty in
  collect_arr_lens core;
  let core =
    SmtExpr.SmtBoolAnd
      (SmtCompile.regions_wf (Shim.coq_list_of_list !arr_decls), core) in
  reset_lowering_memo ();
  tag_vars := StringMap.empty;
  let z3_expr = lower_bool core ctx tracked_vars in
  Solver.add solver [z3_expr];

  sat_check ctx solver tracked_vars
