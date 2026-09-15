(* SolveTime -- where the time in a query actually goes.

   [bench_eq] used to report one number per case, the wall time of a checker
   call.  That conflates two costs with very different characters:

     - BUILDING the query.  All OCaml and Rocq-extracted OCaml: rewriting the
       SmtExpr into the core fragment ([SmtCompile]), walking it for region
       declarations, and lowering it into Z3 AST nodes.  Roughly linear in the
       term's DAG, and the thing this project has repeatedly had to make fast
       -- memo-memo.txt records a 131s -> 0.01s from one change to how the
       lowering memoizes, which is entirely in this phase.
     - SOLVING it.  Z3's own search, which is not linear in anything and is
       where a hard query spends its time.

   Quoting only the sum hides which one a number is about, and the two respond
   to completely different work.  So [Z3Solver.solve] stamps a clock at each
   phase boundary and the totals accumulate here.

   Always on, unlike [SmtSize]: a handful of [gettimeofday] calls per query is
   tens of nanoseconds against a query measured in milliseconds, so there is no
   version of this that needs to be turned off, and a measurement that is only
   available in a special mode is one nobody takes. *)

type t = {
  queries    : int;    (* Z3 invocations *)
  lcb_ms     : float;  (* the length-consistency precondition check *)
  compile_ms : float;  (* SmtCompile: rewrite into the core fragment *)
  collect_ms : float;  (* collect_arr_lens, and building the region conjunct *)
  lower_ms   : float;  (* SmtExpr -> Z3 AST, plus Solver.add *)
  solve_ms   : float;  (* Solver.check, and reading a model back *)
}

let zero = {
  queries = 0; lcb_ms = 0.0; compile_ms = 0.0;
  collect_ms = 0.0; lower_ms = 0.0; solve_ms = 0.0;
}

let acc = ref zero

let reset () = acc := zero
let get () = !acc

let now () = Unix.gettimeofday ()

(* Milliseconds since the mark in [t0], which is then moved to now.  Each
   phase in [Z3Solver.solve] ends with one of these, so the marks tile the
   whole call with no gaps and no double counting. *)
let split (t0 : float ref) : float =
  let t = now () in
  let d = (t -. !t0) *. 1000.0 in
  t0 := t;
  d

let add_lcb t0     = let d = split t0 in acc := { !acc with lcb_ms     = !acc.lcb_ms     +. d }
let add_compile t0 = let d = split t0 in acc := { !acc with compile_ms = !acc.compile_ms +. d }
let add_collect t0 = let d = split t0 in acc := { !acc with collect_ms = !acc.collect_ms +. d }
let add_lower t0   = let d = split t0 in acc := { !acc with lower_ms   = !acc.lower_ms   +. d }

let add_solve t0 =
  let d = split t0 in
  acc := { !acc with solve_ms = !acc.solve_ms +. d; queries = !acc.queries + 1 }

(* Everything between [solve] being called and Z3 being asked anything.  This
   is the number that answers "how long before the solver even starts". *)
let build_ms (x : t) = x.lcb_ms +. x.compile_ms +. x.collect_ms +. x.lower_ms

let total_ms (x : t) = build_ms x +. x.solve_ms

(* A share of the total, for a table.  Zero total reads as zero rather than
   nan, since a case that never called the solver has no interesting ratio. *)
let pct (part : float) (whole : float) =
  if whole <= 0.0 then 0.0 else 100.0 *. part /. whole

(* Deliberately NOT "build_ms": bench_eq already emits a build_ms for the cost
   of reading the programs in, and two columns of that name in one row is how a
   reader -- or a csv.DictReader -- silently gets the wrong one. *)
let csv_header = "queries,lcb_ms,compile_ms,collect_ms,lower_ms,query_ms,z3_ms"

let to_csv (x : t) =
  Stdlib.String.concat ","
    [ Stdlib.string_of_int x.queries;
      Stdlib.Printf.sprintf "%.3f" x.lcb_ms;
      Stdlib.Printf.sprintf "%.3f" x.compile_ms;
      Stdlib.Printf.sprintf "%.3f" x.collect_ms;
      Stdlib.Printf.sprintf "%.3f" x.lower_ms;
      Stdlib.Printf.sprintf "%.3f" (build_ms x);
      Stdlib.Printf.sprintf "%.3f" x.solve_ms ]
