(* SmtSize -- how big is the formula that actually reaches Z3.

   [IrSize] counts IR syntax, which describes the input but predicts solve time
   poorly.  This counts the SMT term instead, measured at the one point every
   query passes through ([Z3Solver.solve]), after [SmtCompile] has rewritten it
   into the core fragment -- so it is the term that gets lowered, not the one
   the semantics built.

   TWO numbers, and the difference between them is the point.

   [dag] counts DISTINCT subterms, comparing by physical identity.  That is
   what Z3 effectively sees: [Z3Solver]'s lowering memoizes on the same notion
   of identity ([PhysTbl]), so a subterm reachable a thousand ways is lowered
   once and becomes one hash-consed Z3 node.

   [tree] counts the term as if it were unfolded -- every path counted
   separately.  Symbolic execution of a program with branches builds terms that
   share aggressively, so [tree] can be orders of magnitude larger than [dag],
   and quoting it would badly misrepresent the query.  It is here because the
   RATIO is the interesting quantity: it says how much of the apparent size is
   sharing.  It saturates rather than overflowing (see [add_sat]).

   Nothing here is on the timed path unless [enabled] is set; [bench_eq] turns
   it on for one extra untimed run and off again before it starts the clock. *)

type t = {
  queries : int;   (* Z3 invocations *)
  dag     : int;   (* distinct subterms, summed over queries *)
  tree    : int;   (* unfolded subterms, summed and saturating *)
  depth   : int;   (* deepest nesting, max over queries *)
}

let zero = { queries = 0; dag = 0; tree = 0; depth = 0 }

(* A tree count can in principle exceed what an int holds; saturate instead of
   wrapping, so a number that is merely enormous never reads as small. *)
let max_count = max_int / 4
let add_sat a b = if a > max_count - b then max_count else a + b

module PhysTbl = Hashtbl.Make (struct
  type t = Obj.t
  let equal = ( == )
  let hash = Hashtbl.hash
end)

(* One walk computes all three numbers.  [seen] maps a node to its (tree size,
   depth); its presence also marks the node counted for [dag].  Memoizing is
   what keeps this linear in the DAG rather than the tree. *)
let measure (e : SmtExpr.coq_SmtBoolExpr) : int * int * int =
  let seen : (int * int) PhysTbl.t = PhysTbl.create 4096 in
  let dag = ref 0 in
  let get k = PhysTbl.find_opt seen (Obj.repr k) in
  let put k v = PhysTbl.replace seen (Obj.repr k) v in
  (* [combine] folds a node's children into its own (tree, depth). *)
  let node children =
    let t = Stdlib.List.fold_left (fun a (ct, _) -> add_sat a ct) 1 children in
    let d =
      1 + Stdlib.List.fold_left (fun a (_, cd) -> Stdlib.max a cd) 0 children in
    (t, d)
  in
  let rec b (x : SmtExpr.coq_SmtBoolExpr) =
    match get x with
    | Some v -> v
    | None ->
      incr dag;
      let v =
        match x with
        | SmtExpr.SmtTrue | SmtExpr.SmtFalse | SmtExpr.SmtBoolVar _ ->
          node []
        | SmtExpr.SmtBoolNot e -> node [b e]
        | SmtExpr.SmtBoolAnd (e1, e2) | SmtExpr.SmtBoolOr (e1, e2) ->
          node [b e1; b e2]
        | SmtExpr.SmtBoolEq (e1, e2) | SmtExpr.SmtBoolLt (e1, e2) ->
          node [a e1; a e2]
        | SmtExpr.SmtArrEq (_, a1, a2) -> node [r a1; r a2]
      in
      put x v; v
  and a (x : SmtExpr.coq_SmtArithExpr) =
    match get x with
    | Some v -> v
    | None ->
      incr dag;
      let v =
        match x with
        | SmtExpr.SmtArithConst _ | SmtExpr.SmtUninit
        | SmtExpr.SmtArithVar _ | SmtExpr.SmtVarVal _
        | SmtExpr.SmtVarTag _ -> node []
        | SmtExpr.SmtBitsToInt bits ->
          node (Stdlib.List.map b (Shim.listify_coq_list bits))
        | SmtExpr.SmtBitSlice (_, _, e) -> node [a e]
        | SmtExpr.SmtConditional (c, t, f) -> node [b c; a t; a f]
        | SmtExpr.SmtCast (_, _, e) -> node [a e]
        | SmtExpr.SmtBitAdd (_, e1, e2) | SmtExpr.SmtBitSub (_, e1, e2)
        | SmtExpr.SmtBitAnd (_, e1, e2) | SmtExpr.SmtBitOr (_, e1, e2)
        | SmtExpr.SmtBitXor (_, e1, e2) | SmtExpr.SmtBitMul (_, e1, e2)
        | SmtExpr.SmtBitDiv (_, e1, e2) | SmtExpr.SmtBitMod (_, e1, e2) ->
          node [a e1; a e2]
        | SmtExpr.SmtBitNot e -> node [a e]
        | SmtExpr.SmtArrSel (ar, i) -> node [r ar; a i]
        | SmtExpr.SmtCellVal (ar, i) | SmtExpr.SmtCellTag (ar, i) ->
          node [r ar; a i]
      in
      put x v; v
  and r (x : SmtExpr.coq_SmtArrExpr) =
    match get x with
    | Some v -> v
    | None ->
      incr dag;
      let v =
        match x with
        | SmtExpr.SmtArrInit | SmtExpr.SmtArrVar _ -> node []
        | SmtExpr.SmtArrSt (ar, i, v) -> node [r ar; a i; a v]
        | SmtExpr.SmtArrIte (c, a1, a2) -> node [b c; r a1; r a2]
        | SmtExpr.SmtStCell (ar, i, v, t) -> node [r ar; a i; a v; a t]
      in
      put x v; v
  in
  let (tree, depth) = b e in
  (!dag, tree, depth)

(* ------------------------------------------------------------------ *)
(* The recording hook.  [Z3Solver.solve] calls [record] on every query it is
   about to lower; it costs a walk of the DAG, so it is off by default. *)

let enabled = ref false
let acc = ref zero

let reset () = acc := zero

let record (e : SmtExpr.coq_SmtBoolExpr) =
  if !enabled then begin
    let (d, t, dep) = measure e in
    let a = !acc in
    acc := { queries = a.queries + 1;
             dag = a.dag + d;
             tree = add_sat a.tree t;
             depth = Stdlib.max a.depth dep }
  end

let get () = !acc

(* The sharing factor: how many unfolded subterms each distinct one stands for.
   1.0 means no sharing at all. *)
let sharing (m : t) =
  if m.dag = 0 then 0.0
  else Stdlib.float_of_int m.tree /. Stdlib.float_of_int m.dag

let header = "queries,smt_dag,smt_tree,smt_depth,smt_sharing"

let to_csv (m : t) =
  Stdlib.Printf.sprintf "%d,%d,%d,%d,%.1f"
    m.queries m.dag m.tree m.depth (sharing m)
