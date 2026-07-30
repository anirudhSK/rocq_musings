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
(* A [CrVal] is a value AND a tag, so an arith expression lowers to a PAIR.

   [eval_smt_arith] is the specification this encoding has to meet, and it is
   type-checked throughout: [eqb]/[ltb] require both operands to carry the same
   [CrIntType] and are false otherwise, [iv_binop_at ty] requires both operands
   to already be typed [ty] and yields [ErrorVal] otherwise, [cast from to]
   checks [from], and [UninitVal] and [ErrorVal] are values in their own right
   (with [eqb UninitVal UninitVal = true]).  An encoding that lowers everything
   to a bare 64-bit bitvector cannot express any of that: it lets Z3 satisfy a
   query in states the concrete semantics cannot reach, which makes
   [SmtQuery.smt_query_sound_some] -- the axiom [solve] is extracted to
   discharge -- false rather than merely imprecise.

   So each arith expression lowers to [(value, tag)]:

     tag 0 = ErrorVal, 1 = UninitVal, 2..5 = IntVal at W8/W16/W32/W64

   Values stay 64-bit and unmasked; only op *results* are masked, mirroring
   [mk_int].  (A variable's value may therefore exceed its nominal width, which
   is exactly what [eval_smt_arith] permits -- comparisons test full values.) *)
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

(* A memory cell is a [CrVal] too, so a region is an array from a 64-bit offset
   to a packed (tag, value) word -- packed rather than two parallel arrays so a
   store stays a single atomic [store]. *)
let cell_bits = tag_bits + 64
let pack_cell ctx v t = Z3.BitVector.mk_concat ctx t v
let cell_value ctx c = Z3.BitVector.mk_extract ctx 63 0 c
let cell_tag ctx c = Z3.BitVector.mk_extract ctx (cell_bits - 1) 64 c

(* Memo tables for the lowering, and the visited set for the pre-pass.

   Symbolic execution shares subterms aggressively -- every path merge points
   both branches at the same header expressions, and a deparser emits one
   header value once per emitted bit -- so a query is a DAG, not a tree.
   Walking it structurally re-expands that sharing: on the PktClass
   linear-vs-TSS query the DAG has ~390 distinct nodes but an unmemoised walk
   visits ~4.6 million, which cost about 7 seconds of Z3 FFI calls building
   nodes Z3 then hash-consed straight back down.  (The solve itself was
   instant.)  Memoising makes the walk proportional to the DAG.

   TWO THINGS ABOUT THESE TABLES ARE LOAD-BEARING.

   They are keyed on PHYSICAL identity, and using the polymorphic [Hashtbl]
   instead -- which keys on structural equality, and so would also share two
   subterms that are equal but distinct -- is a trap that cost 131 seconds on
   the eBPF query.  [Hashtbl.hash] inspects only a bounded prefix of a term, so
   the merge nodes a chain of transformers produces (all of them
   [SmtConditional] over a guard on the same header) hash alike and land in one
   bucket; resolving the collision runs structural [=], which walks the DAG as
   a tree and re-expands exactly the sharing the memo exists to exploit.  It is
   worst when the comparison is *easiest*: comparing a program against itself
   makes every subterm of the two states structurally equal, so every lookup
   collides.  `bpf_O0` against itself went 131s -> 0.01s on this one change.
   Physical equality makes a collision an O(1) pointer comparison and loses
   nothing real -- Z3 hash-conses the duplicates back together.

   And EVERY walk needs a table, not just the ones that build something:
   [collect_arr_lens] returns nothing and still has to memoise, because the
   blowup is in the traversal.  It did not, and on the eBPF query that pre-pass
   alone took 21 seconds against a solve of 0.02.

   Cleared per [solve]: a Z3 expression belongs to the context it was built in,
   so entries must never outlive one lowering.

   What is NOT worth doing, having been measured: dropping [SmtConditional]s
   and [SmtArrIte]s whose two arms are the same node.  Roughly 40% of the merge
   nodes in an eBPF query are of that form -- a transformer merges every
   variable, including the ones the rule did not write -- but rewriting them
   away first makes the solve very slightly *slower*.  Z3 already handles
   [ite c x x]. *)
module PhysTbl = Hashtbl.Make (struct
  type t = Obj.t
  (* [==] refines structural equality, so the structural hash stays a valid
     hash for it: equal keys still hash alike. *)
  let equal = ( == )
  let hash = Hashtbl.hash
end)

let memo_bool : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
(* An arith node memoises the (value, tag) pair it lowers to. *)
let memo_arith : (Z3.Expr.expr * Z3.Expr.expr) PhysTbl.t = PhysTbl.create 1024
let memo_arr : Z3.Expr.expr PhysTbl.t = PhysTbl.create 1024
let memo_find (t : 'a PhysTbl.t) (k : 'k) : 'a option = PhysTbl.find_opt t (Obj.repr k)
let memo_add (t : 'a PhysTbl.t) (k : 'k) (v : 'a) : unit = PhysTbl.replace t (Obj.repr k) v
let reset_lowering_memo () =
  PhysTbl.reset memo_bool; PhysTbl.reset memo_arith; PhysTbl.reset memo_arr

(* Each memory region variable's declared length, which the model
   reconstruction needs to know how many cells of a region to read back.
   Collected by a pre-pass over the query.

   (There used to be a second table here inferring each scalar variable's width
   from the ops that consume it, so the SAT model could be reconstructed at the
   right [CrIntType].  Tags make that guess unnecessary: the width is read off
   the model.) *)
let arr_lens : (string, int) Hashtbl.t = Hashtbl.create 16

(* The pre-pass is a walk over the same DAG the lowering walks, so it needs the
   same protection against re-expanding the sharing -- it just has nothing to
   return, so what it memoises is "already visited".  Without this it is the
   unmemoised structural walk all over again: on the eBPF -O0-vs-O2 query it
   was where all the time went, ahead of both the lowering and Z3. *)
let collect_arr_lens (expr : SmtExpr.coq_SmtBoolExpr) : unit =
  Hashtbl.reset arr_lens;
  (* One table per sort.  A constant constructor extracts to an immediate, so
     [SmtTrue], [SmtUninit] and [SmtArrInit] are all [Obj.repr 0] and would
     collide in a shared table.  They are leaves, so today nothing would be
     lost, but a constant constructor with children would silently prune a
     subtree. *)
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
    (* Load-bearing: since [check_sym_region_equal] became one [SmtArrEq], this
       is the ONLY path from the query to a region's array variable.  Drop this
       case and [arr_lens] comes back empty, so a SAT model reconstructs every
       region as zero cells. *)
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


(* Tag consts for scalar variables, kept beside [vars] so the model can be read
   back as a properly typed [CrVal]. *)
let tag_vars : Z3.Expr.expr StringMap.t ref = ref StringMap.empty

let mem_sort ctx =
  Z3.Z3Array.mk_sort ctx (Z3.BitVector.mk_sort ctx 64)
                         (Z3.BitVector.mk_sort ctx cell_bits)

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
      (* [CrVal.eqb]: equal tags, and equal values when the tag says IntVal.
         Two UninitVals are equal and two ErrorVals are equal (tags match, no
         value compared); anything with differing tags is not.  This is the
         type-first half of the match semantics, which the old untyped encoding
         simply did not have. *)
      let (v1, t1) = lower_arith a1 ctx vars in
      let (v2, t2) = lower_arith a2 ctx vars in
      Z3.Boolean.mk_and ctx
        [Z3.Boolean.mk_eq ctx t1 t2;
         Z3.Boolean.mk_or ctx
           [Z3.Boolean.mk_not ctx (tag_is_int ctx t1);
            Z3.Boolean.mk_eq ctx v1 v2]]
  | SmtExpr.SmtBoolLt (a1, a2) ->
      (* [CrVal.ltb]: false unless both are IntVal at the same type. *)
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
  (* [SmtArrEq n a1 a2] is "the two regions agree on cells 0..n-1", and this
     emits ONE extensional array equality, ignoring [n].  That is the same
     statement on the terms this checker builds, and only on those: both arrays
     are rooted at the same [SmtArrVar] (Coq-side proof:
     [SmtModuleQuery.eval_general_program_symbolic_mem_rooted]) and every
     [SmtArrSt] below is guarded in bounds, so outside 0..n-1 the two arrays are
     the same term and extensional equality adds nothing there.

     Two ways to break it, both of which make the checker report differences the
     concrete semantics cannot produce: unguard [SmtArrSt], or let [n] disagree
     with the [len] on the [SmtArrVar] at the root (they coincide because
     [CrVarLike.init_symbolic_mem] and [check_sym_region_equal] both take it
     from the same [mr_len]).  See SOUNDNESS.md. *)
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
  (* [iv_binop_at ty]: both operands must already be typed [ty], else ErrorVal;
     the result is masked into [ty] and typed [ty]. *)
  let binop_at ty e1 e2 (f : Z3.Expr.expr -> Z3.Expr.expr -> Z3.Expr.expr) =
    let (v1, t1) = lower_arith e1 ctx vars in
    let (v2, t2) = lower_arith e2 ctx vars in
    let ok = Z3.Boolean.mk_and ctx
               [tag_eq ctx t1 (ty_tag ty); tag_eq ctx t2 (ty_tag ty)] in
    (mask_to ctx (ty_bits ty) (f v1 v2),
     Z3.Boolean.mk_ite ctx ok (mk_tag ctx (ty_tag ty)) (mk_tag ctx tag_err)) in
  let z = (match expr with
  | SmtExpr.SmtArithConst (v, ty) ->
      (* Encode via an arbitrary-precision decimal string: a u64 constant can
         exceed OCaml's [max_int], so [coq_Z_to_int] would overflow. *)
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
      (* Concat the bits MSB-first into a width-|bits| bitvector, then zero-extend
         to 64.  Concat and zero-extend are free in bit-blasting, so this avoids
         the ripple-carry adders an arithmetic assembly would generate.
         [eval_smt_arith] wraps the fold in [mk_int u64], so the tag is W64. *)
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
      (* Bits [lo, hi) LSB-indexed, right-aligned: mirrors [CrVal.slice_val]
         ([(e >> lo) & ones(hi-lo)] in a 64-bit container).  [slice_val] is
         ErrorVal on a non-integer and otherwise re-types the result to u64. *)
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
      (* [CrVal.cast]: the operand must already be typed [from], else ErrorVal;
         the result is its bits masked into [to] and typed [to]. *)
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
      (* [CrVal.not] keeps the operand's own type, so the mask width is dynamic:
         pick it off the tag. *)
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
      (* Z3's [select] is total; [CrVal.ld_arr] is not.  It is Illegal -- which
         [eval_smt_arith] turns into ErrorVal -- on a non-integer offset or one
         past the region's declared length, so guard on both.  The bound comes
         from [SmtExpr.smt_arr_len], the same walk the Coq side uses. *)
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
  (* An undeclared region has length 0, so every [SmtArrSel] on it is guarded
     to ErrorVal and its contents are never observed.  A fresh constant is
     therefore as good as anything, and avoids constraining the model. *)
  | SmtExpr.SmtArrInit -> Z3.Expr.mk_fresh_const ctx "arr_undeclared" (mem_sort ctx)
  | SmtExpr.SmtArrVar (name, _len) -> (
      let name_str = Shim.coq_str_to_str name in
      match StringMap.find_opt name_str !vars with
      | Some z3_var -> z3_var
      | None ->
          let z3_var = Z3.Z3Array.mk_const ctx (Z3.Symbol.mk_string ctx name_str)
                         (Z3.BitVector.mk_sort ctx 64)
                         (Z3.BitVector.mk_sort ctx cell_bits) in
          vars := StringMap.add name_str z3_var !vars;
          z3_var)
  | SmtExpr.SmtArrSt (m, idx, v) ->
      (* [CrVal.st_arr] drops the write on a non-integer offset or one past the
         declared length, leaving the region unchanged.  Guard the store the
         same way rather than relying on Z3's total [store].  TWO things now
         depend on this, the second added when [check_sym_region_equal] became
         one [SmtArrEq]:
           - an unguarded write at a rejected offset would be visible to a later
             in-bounds read at the same numeric index, which the concrete run
             never performed;
           - it would also leave the two regions differing OUT of bounds, and
             extensional array equality sees every index -- so the checker would
             report a difference the concrete semantics cannot produce.  The old
             per-cell conjunction never looked past the declared length and so
             was blind to this.
         Regression test: TestEquality "out of bounds, the order stops
         mattering". *)
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

(* Reconstruct one scalar variable from the model.

   The variable's [CrIntType] is READ OFF ITS TAG rather than inferred from the
   ops that consume it, which is what the encoding buys beyond soundness: a
   variable whose tag the model set to Uninit/Error comes back as [UninitVal],
   and a variable nothing constrains comes back at whatever width the model
   chose.  (There used to be a pre-pass guessing the width from the first typed
   op that consumed a variable, defaulting to u64.)

   The value is stored UNMASKED, its full 64-bit model value.  It must NOT be
   masked to the tag's width: the returned valuation is the SAT witness, and
   [eval_smt_arith] operates on full 64-bit operands -- masking only ever
   happens on op *results*, via [mk_int] -- while comparisons test full values.
   Masking here could flip a match condition and stop the valuation from being
   a genuine witness. *)
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
         (* The tag says this is not an IntVal at all. *)
         Printf.printf "| var( %s ) := uninit\n" name;
         Shim.VMap (Shim.str_to_coq_str name, CrVal.UninitVal, acc))
    else
      raise (Failure ("Expects uint but got non-numeral value for " ^ name))
  | None -> raise (Failure ("Z3 failed to return valuation for " ^ name))

(* Read a memory region back out of the model.  Rather than walking the Z3
   array term's [store] chain, ask the model for [select a i] at each of the
   region's declared cells: the declared length is known ([arr_lens]), the
   region is exactly that long, and any cell past it is unobservable because
   [SmtArrSel] guards on the same bound.

   [eval_smt_mem] re-imposes the declared length via [region_with_len], so only
   the bytes here have to be right. *)
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
    (* A cell holds a whole CrVal, so read its tag as well as its value. *)
    match get (cell_value ctx cell), get (cell_tag ctx cell) with
    | Some vs, Some ts ->
        let cv = match tag_to_ty (int_of_string ts) with
          | Some ty ->
              cells := Printf.sprintf "%s:u%d" vs (ty_bits ty) :: !cells;
              CrVal.IntVal (Shim.str_to_coq_uint64 vs, ty)
          | None -> cells := "-" :: !cells; CrVal.UninitVal in
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
  Solver.add solver [z3_expr];

  sat_check ctx solver tracked_vars
