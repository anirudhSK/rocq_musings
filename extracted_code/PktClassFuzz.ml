(* Random FilterDatabase generation, for fuzzing [PktClass.linear_db] against
   [PktClass.tss_db].

   The two constructions are supposed to classify identically for EVERY filter
   database -- that is the claim the header comment of PktClass.v says the
   checker cannot discharge, because it only ever speaks about two SPECIFIC
   programs.  Fuzzing is the tractable approximation: generate a database,
   build both programs from it, and ask [modnet_equivalence_checker].  Each
   verdict is still a statement about all 2^192 input packets, so a suite of
   random databases covers a genuinely large space.

   Two properties a generated database must have, or the two constructions
   really do disagree and the fuzzer reports a bug that isn't one:

   - PRIORITIES MUST BE DISTINCT.  [linear_db] resolves a tie by first-match on
     the stably-sorted database, i.e. by position in the database.  [tss_db]
     resolves one by the merger, which only displaces the accumulator on a
     STRICTLY lower priority, i.e. by the order [PTree.elements] hands back the
     hash tables -- unrelated to database order.  Two equal-priority filters in
     different tables can therefore be broken different ways.  (Within one
     table both agree, since both are first-match on the same stable sort.)

   - PRIORITIES MUST BE IN 1..254.  They are written into a u8 header and
     compared there, and 255 is [make_table_transformer]'s "this table matched
     nothing" sentinel, which the merger must not mistake for a real match.

   Everything else is fair game.  In particular a filter's match patterns may
   be empty: [compute_h_out]/[compute_h_base] pick the accumulator and table
   slots from the largest header uid MENTIONED in the database, so a database
   that mentions few headers drags them down onto parser-written ones --
   harmless, because the only observable is the byte the deparser emits and
   both constructions copy the same [h_out] into it.

   Two further properties are not needed for CORRECTNESS but are what stop the
   campaign being a no-op, and both have a probe that measures them: filters
   are built around a witness packet so they are matchable at all ([relabel],
   and see the Generation section), and about half of each database's filters
   share one witness so that precedence is exercised ([reprioritise]).  Neither
   probe is decoration -- the first version of this generator satisfied neither
   and every one of its Equivalent verdicts was vacuous.

   One thing here is a COST control rather than a property of the databases: a
   filter's tuple shape is drawn from a pool of at most [ceil (sqrt nfilters)],
   so a database of n filters occupies at most that many tables rather than n.
   The query grows quadratically in the TABLE count and only linearly in the
   filter count, so without the bound a campaign pays for the table count and
   measures the filter count.  See [shape_pool]. *)

open BinNums
open Datatypes
open CrTransformer

(* ------------------------------------------------------------------ *)
(* A tiny splitmix64, rather than [Random].  The point of a fuzzer is that a
   failing seed reproduces, and the stdlib generator's sequence is not stable
   across OCaml versions. *)

type rng = { mutable st : int64 }

let rng_make (seed : int) : rng = { st = Int64.of_int seed }

let rng_next (r : rng) : int64 =
  r.st <- Int64.add r.st 0x9E3779B97F4A7C15L;
  let z = r.st in
  let z = Int64.mul (Int64.logxor z (Int64.shift_right_logical z 30))
            0xBF58476D1CE4E5B9L in
  let z = Int64.mul (Int64.logxor z (Int64.shift_right_logical z 27))
            0x94D049BB133111EBL in
  Int64.logxor z (Int64.shift_right_logical z 31)

(* Uniform-ish in [0, n). *)
let rng_int (r : rng) (n : int) : int =
  let v = Int64.shift_right_logical (rng_next r) 1 in
  Int64.to_int (Int64.rem v (Int64.of_int n))

let rng_pick (r : rng) (a : 'a array) : 'a = a.(rng_int r (Array.length a))

(* [List.init] does not promise an evaluation order, and the generated
   database has to be a function of the seed alone. *)
let mk_list (n : int) (f : int -> 'a) : 'a Stdlib.List.t =
  let rec go i acc =
    if i >= n then Stdlib.List.rev acc else go (i + 1) (f i :: acc) in
  go 0 []

(* ------------------------------------------------------------------ *)
(* The five fields.  A pattern is only meaningful against what
   [field_extractor] writes: the header must be one it populates and the
   MatchConst's CrIntType must be the width that extract wrote, because
   [CrVal.eqb]/[ltb] compare the CrIntType before the value. *)

type fieldspec = {
  fs_name   : string;
  fs_hdr    : CrIdentifiers.coq_Header;
  fs_ty     : CrVal.coq_CrIntType;
  (* The values a pattern on this field may use, and the pool a witness is
     drawn from.  Small, so filters overlap often. *)
  fs_consts : int array;
}

let f_src_ip = {
  fs_name = "src_ip"; fs_hdr = PktClass.h_src_ip; fs_ty = CrVal.u32;
  fs_consts = [| 0; 1; 7; 168496141; 4294967295 |];
}
let f_dst_ip = {
  fs_name = "dst_ip"; fs_hdr = PktClass.h_dst_ip; fs_ty = CrVal.u32;
  fs_consts = [| 0; 1; 7; 168496141; 4294967295 |];
}
let f_src_port = {
  fs_name = "src_port"; fs_hdr = PktClass.h_src_port; fs_ty = CrVal.u16;
  fs_consts = [| 0; 1; 80; 443; 65535 |];
}
let f_dst_port = {
  fs_name = "dst_port"; fs_hdr = PktClass.h_dst_port; fs_ty = CrVal.u16;
  fs_consts = [| 0; 1; 80; 443; 65535 |];
}
let f_protocol = {
  fs_name = "protocol"; fs_hdr = PktClass.h_protocol; fs_ty = CrVal.u8;
  fs_consts = [| 0; 1; 6; 17; 255 |];
}

(* How many conditions one field gets.  Weighted towards 1, with 0 and 2 to
   keep the shapes varied.  This is drawn per SHAPE, not per filter -- see
   [shape_pool]. *)
let field_lengths = [| 0; 1; 1; 1; 2; 2 |]

(* Mostly CmpEq -- exact match is what a tuple-space classifier is for -- with
   enough CmpLt/CmpGt that overlapping ranges show up. *)
let cmp_ops = [| CmpEq; CmpEq; CmpEq; CmpEq; CmpLt; CmpGt |]

let cmp_str = function CmpEq -> "==" | CmpLt -> "<" | CmpGt -> ">"

(* ------------------------------------------------------------------ *)
(* Generation.  Every step is an explicit [let] because OCaml evaluates
   arguments right to left, and the seed has to determine the database.

   A filter is built around a WITNESS: five field values drawn first, with
   every condition then chosen so the witness satisfies it.  That makes each
   filter matchable by construction, and it is the difference between a fuzzer
   and a fuzzer-shaped no-op.  Conditions drawn independently are usually
   self-contradictory -- two different constants required of one field,
   [src_port < 0], [dst_ip == src_ip] next to two different constants -- and a
   database of unmatchable filters classifies nothing, so BOTH programs emit
   only zeros and the checker reports Equivalent for a reason that has nothing
   to do with the two constructions agreeing.  That is the both-reject trap in
   CLAUDE.md, and [--mutate] is what measures it: with witness generation every
   database comes back NotEquivalent when relabelled, where independently drawn
   conditions managed about a quarter. *)

(* The fields, indexed; [peer_ix] is the same-width partner of each, or -1. *)
let fields = [| f_src_ip; f_dst_ip; f_src_port; f_dst_port; f_protocol |]
let peer_ix = [| 1; 0; 3; 2; -1 |]

type cond_doc = { cd_cmp : string; cd_rhs : string }

(* A witness value per field.  Drawn from the same constant pools the patterns
   use, so a generated condition usually has a choice of constants that the
   witness satisfies.  The two same-width pairs are given a decent chance of
   being EQUAL, because that is what makes a MatchHeader condition (src_ip ==
   dst_ip) available without making the filter unmatchable. *)
let gen_witness (r : rng) : int array =
  let w = Array.make 5 0 in
  for i = 0 to 4 do w.(i) <- rng_pick r fields.(i).fs_consts done;
  if rng_int r 3 = 0 then w.(1) <- w.(0);
  if rng_int r 3 = 0 then w.(3) <- w.(2);
  w

(* One condition on field [ix] that [w] satisfies.  [CmpLt]/[CmpGt] need a
   constant on the correct side of the witness; when the pool offers none the
   condition falls back to equality, which every witness satisfies. *)
let gen_cond (r : rng) (w : int array) (ix : int)
  : (((CrIdentifiers.coq_Header, coq_CmpOp) prod, coq_MatchValue) prod)
    * cond_doc =
  let fs = fields.(ix) in
  let p = peer_ix.(ix) in
  let v = w.(ix) in
  let drawn = rng_pick r cmp_ops in
  let want_peer = p >= 0 && w.(p) = v && rng_int r 6 = 0 in
  (* Constants the witness leaves on the correct side of [drawn].  [CmpLt] is
     (header < value) and [CmpGt] is (value < header) -- [eval_cmp_concrete]. *)
  let keep k =
    match drawn with CmpEq -> false | CmpLt -> k > v | CmpGt -> k < v in
  let usable =
    Stdlib.Array.of_list
      (Stdlib.List.filter keep (Stdlib.Array.to_list fs.fs_consts)) in
  let cmp, mv, rhs =
    if want_peer then
      (* Only as an equality: the witness makes the two fields equal, so
         [<]/[>] against the peer is the one shape it cannot satisfy. *)
      CmpEq, MatchHeader (fields.(p).fs_hdr), fields.(p).fs_name
    else
      (* No constant on the right side of the witness -- fall back to the
         equality, which every witness satisfies. *)
      let cmp = if Stdlib.Array.length usable = 0 then CmpEq else drawn in
      let k = if Stdlib.Array.length usable = 0 then v else rng_pick r usable in
      cmp, MatchConst (Shim.int_to_coq_uint64 k, fs.fs_ty), string_of_int k in
  (Coq_pair (Coq_pair (fs.fs_hdr, cmp), mv),
   { cd_cmp = cmp_str cmp; cd_rhs = rhs })

(* [n] conditions on field [ix], all satisfied by [w].  The COUNT is supplied
   by the caller rather than drawn here: it is what [GetTuple] hashes on, so it
   belongs to the filter's shape and not to this field. *)
let gen_field (r : rng) (w : int array) (ix : int) (n : int)
  : coq_MatchPattern * string =
  let fs = fields.(ix) in
  let conds = mk_list n (fun _ -> gen_cond r w ix) in
  let doc =
    Stdlib.String.concat ";"
      (Stdlib.List.map (fun (_, d) -> fs.fs_name ^ d.cd_cmp ^ d.cd_rhs) conds) in
  (Shim.coq_list_of_list (Stdlib.List.map (fun (c, _) -> c) conds),
   "[" ^ doc ^ "]")

(* One filter, at an already-chosen (distinct) priority, around witness [w] and
   in tuple shape [sh]. *)
let gen_filter (r : rng) (prio : int) (w : int array) (sh : int array)
  : PktClass.coq_PacketFilter * int * string =
  let si, si_d = gen_field r w 0 sh.(0) in
  let di, di_d = gen_field r w 1 sh.(1) in
  let sp, sp_d = gen_field r w 2 sh.(2) in
  let dp, dp_d = gen_field r w 3 sh.(3) in
  let pr, pr_d = gen_field r w 4 sh.(4) in
  let lbl = rng_int r 256 in
  let f = { PktClass.src_ip = si; dst_ip = di; src_port = sp; dst_port = dp;
            protocol = pr;
            (* [tss_db] overwrites this with the tuple hash and [linear_db]
               never reads it, so any positive will do. *)
            key = Coq_xH;
            priority = Shim.int_to_pos prio } in
  let doc =
    Printf.sprintf
      "prio=%-3d label=%-3d %s %s %s %s %s  (witness %d/%d/%d/%d/%d, \
       shape %d/%d/%d/%d/%d)"
      prio lbl si_d di_d sp_d dp_d pr_d w.(0) w.(1) w.(2) w.(3) w.(4)
      sh.(0) sh.(1) sh.(2) sh.(3) sh.(4) in
  (f, lbl, doc)

(* ------------------------------------------------------------------ *)
(* Tuple shapes, and why there are few of them.

   [GetTuple] hashes a filter on the LENGTHS of its five match patterns, so the
   shape is what decides which tuple-space table [tss_db] puts it in.  Drawing
   the five lengths independently per filter -- which is what this generator
   used to do -- gives 6^5 possible shapes, so n filters land in n DISTINCT
   tables essentially always.  That is the worst case for [tss_db] and not what
   a tuple-space classifier looks like: the query grows quadratically in the
   table count (n tables means n table modules, n mergers and a merger chain n
   deep) while it grows only linearly in the filter count at a fixed table
   count.  A campaign of small databases was paying for the table count and
   measuring the filter count.

   So the shapes come from a POOL of at most [ceil (sqrt nfilters)], and every
   filter draws from it.  The bound is deliberate rather than a constant: it
   keeps both quantities growing, so a bigger database exercises more tables AND
   more filters per table, while the query stays near-linear in the database
   size.  At 16 filters that is at most 4 tables rather than 16.

   It is an UPPER bound.  Two pool entries may coincide, and filters may not
   cover every entry, so the realised table count can be lower -- which is fine,
   fewer tables is the cheap direction.  What matters for coverage is that it is
   at least two whenever the database has two filters, since one table alone
   never exercises the merger; [ceil (sqrt n)] is >= 2 for every n >= 2. *)

(* Smallest [k] with [k*k >= n].  Integer-only: [sqrt] on a float and then
   [ceil] is off by one on perfect squares for some n. *)
let ceil_sqrt (n : int) : int =
  let rec go k = if k * k >= n then k else go (k + 1) in
  go 0

let gen_shape (r : rng) : int array =
  let sh = Array.make 5 0 in
  for i = 0 to 4 do sh.(i) <- rng_pick r field_lengths done;
  sh

(* [k] shapes, drawn left to right -- [Array.init] does not promise an order
   and this consumes the generator. *)
let shape_pool (r : rng) (k : int) : int array array =
  Stdlib.Array.of_list (mk_list k (fun _ -> gen_shape r))

(* [n] distinct priorities drawn from 1..254 -- see the header comment. *)
let distinct_priorities (r : rng) (n : int) : int Stdlib.List.t =
  let pool = Array.init 254 (fun i -> i + 1) in
  let lim = if n > 254 then 254 else n in
  for i = 0 to lim - 1 do
    let j = i + rng_int r (254 - i) in
    let t = pool.(i) in pool.(i) <- pool.(j); pool.(j) <- t
  done;
  mk_list lim (fun i -> pool.(i))

(* A database of [nfilters] filters, plus a human-readable rendering of it.
   The rendering is what makes a failure actionable: it is enough to retype the
   database as a Coq [FilterDatabase] next to [SimpleDB].

   Roughly half the filters are built around ONE shared witness rather than
   their own.  Filters that no single packet matches together never make the
   two constructions do anything interesting: whichever matches is the winner
   in both.  Sharing a witness guarantees the database has packets several
   filters match at once, which is where linear_db's first-match-on-sorted-list
   and tss_db's per-table best plus strictly-lower-wins merger have to agree
   the hard way -- and, since two filters sharing a witness usually draw
   different shapes from the pool, agree ACROSS tables.  "tss fuzz: precedence
   is what is being compared" measures that this is really happening.

   Shapes come from a pool of at most [ceil (sqrt nfilters)] -- see
   [shape_pool] for why that bound and not one shape per filter.

   [random_db_ntab] below is the same construction with the table count
   supplied by the caller instead of derived from [nfilters]; [random_db] is
   just [random_db_ntab] at the derived bound. *)
let random_db_ntab (r : rng) (nfilters : int) (ntab : int)
  : PktClass.coq_FilterDatabase * string =
  let prios = distinct_priorities r nfilters in
  let shared = gen_witness r in
  let pool = shape_pool r ntab in
  let ntab = Stdlib.Array.length pool in
  (* Explicitly left to right: [List.map] does not promise an order, and this
     function consumes the generator. *)
  let rec build = function
    | [] -> []
    | p :: rest ->
      let w = if rng_int r 2 = 0 then shared else gen_witness r in
      let sh = pool.(rng_int r ntab) in
      let f, lbl, doc = gen_filter r p w sh in
      let e = (Coq_pair (f, Shim.int_to_coq_uint8 lbl), doc) in
      e :: build rest in
  let entries = build prios in
  let db = Shim.coq_list_of_list (Stdlib.List.map (fun (e, _) -> e) entries) in
  let doc =
    Stdlib.String.concat "\n"
      (Stdlib.List.mapi (fun i (_, d) -> Printf.sprintf "  f%d: %s" i d) entries) in
  (db, doc)

let random_db (r : rng) (nfilters : int) : PktClass.coq_FilterDatabase * string =
  random_db_ntab r nfilters (ceil_sqrt nfilters)

(* ------------------------------------------------------------------ *)

let check_db (db : PktClass.coq_FilterDatabase) : SmtQuery.coq_EquivalenceResult =
  SmtModuleQuery.modnet_equivalence_checker
    (PktClass.linear_db db) (PktClass.tss_db db)

(* Every label bumped by one.  This is the fuzzer's negative control, and it is
   not optional: a suite of Equivalent verdicts means nothing on its own,
   because the checker calls two programs that both reject -- or that both emit
   nothing but zeros -- equivalent.  Checking [linear_db db] against
   [tss_db (relabel db)] asks the complementary question, whether this
   database's classification is OBSERVABLE at all; it must come back
   NotEquivalent whenever some packet matches some filter. *)
let relabel (db : PktClass.coq_FilterDatabase) : PktClass.coq_FilterDatabase =
  let rec go = function
    | Coq_nil -> Coq_nil
    | Coq_cons (Coq_pair (f, lbl), rest) ->
      let n = Shim.coq_Z_to_int lbl in
      Coq_cons (Coq_pair (f, Shim.int_to_coq_uint8 ((n + 1) mod 256)), go rest) in
  go db

let check_db_relabelled (db : PktClass.coq_FilterDatabase)
  : SmtQuery.coq_EquivalenceResult =
  SmtModuleQuery.modnet_equivalence_checker
    (PktClass.linear_db db) (PktClass.tss_db (relabel db))

(* Priorities inverted, 1..254 mirrored onto itself -- distinct stays distinct
   and the range is preserved, so the result is still a database the two
   constructions must agree on.  This is the second probe: [linear_db db]
   against [tss_db (reprioritise db)] comes back NotEquivalent exactly when
   some packet matches two filters with different labels, i.e. when this
   database exercises PRECEDENCE rather than just matching.  Unlike [relabel]
   it is a coverage measurement, not an assertion -- a database whose filters
   never overlap legitimately does not flip. *)
let reprioritise (db : PktClass.coq_FilterDatabase) : PktClass.coq_FilterDatabase =
  let rec go = function
    | Coq_nil -> Coq_nil
    | Coq_cons (Coq_pair (f, lbl), rest) ->
      let p = Shim.coq_Z_to_int (Zpos f.PktClass.priority) in
      let f' = { f with PktClass.priority = Shim.int_to_pos (255 - p) } in
      Coq_cons (Coq_pair (f', lbl), go rest) in
  go db

let check_db_reprioritised (db : PktClass.coq_FilterDatabase)
  : SmtQuery.coq_EquivalenceResult =
  SmtModuleQuery.modnet_equivalence_checker
    (PktClass.linear_db db) (PktClass.tss_db (reprioritise db))

let verdict_str = function
  | SmtQuery.Equivalent -> "Equivalent"
  | SmtQuery.NotEquivalent _ -> "NotEquivalent"
  | SmtQuery.NotEquivalentUnknown -> "NotEquivalentUnknown"
  | SmtQuery.NotEquivalentVariablesDiffer -> "NotEquivalentVariablesDiffer"

let is_equivalent = function SmtQuery.Equivalent -> true | _ -> false

(* A DIFFERENCE was demonstrated, with a witness valuation.  The probes below
   want this rather than [not is_equivalent]: NotEquivalentUnknown is the
   solver giving up, and counting it as a demonstrated difference would let a
   campaign of timeouts read as a campaign of evidence. *)
let is_different = function SmtQuery.NotEquivalent _ -> true | _ -> false

(* How many of [count] generated databases exercise precedence -- see
   [reprioritise].  A coverage number, not a pass/fail: it says how much of the
   campaign above is actually comparing the two ARBITRATION schemes rather than
   two ways of matching one filter. *)
let run_precedence_probe ~(seed : int) ~(count : int) ~(sizes : int array) ()
  : int =
  let flipped = ref 0 in
  for i = 0 to count - 1 do
    let r = rng_make (seed + i) in
    let n = sizes.(i mod Array.length sizes) in
    let db, _ = random_db r n in
    if is_different (check_db_reprioritised db) then incr flipped
  done;
  !flipped

(* Run [count] databases, sizes cycling through [sizes], and report how many
   disagreed.  Nothing is printed per database when they all come back
   Equivalent, so an expect test's expected output does not depend on the
   generator's exact sequence -- only a FAILURE prints, and it prints the
   database and the seed that produced it. *)
let run_campaign ?(verbose = false) ?(mutate = false) ~(seed : int)
    ~(count : int) ~(sizes : int array) () : int =
  let failures = ref 0 in
  for i = 0 to count - 1 do
    (* Reseeded per database, so database [i] of a campaign is reproducible on
       its own: `fuzz_tss --seed <seed+i> --count 1 --size <n>`. *)
    let r = rng_make (seed + i) in
    let n = sizes.(i mod Array.length sizes) in
    let db, doc = random_db r n in
    (* [mutate] inverts the expectation: relabelled, the two must DISAGREE. *)
    let v = if mutate then check_db_relabelled db else check_db db in
    let ok = if mutate then is_different v else is_equivalent v in
    if verbose then
      Printf.printf "db %d (seed %d, %d filters): %s%s\n%!"
        i (seed + i) n (verdict_str v)
        (if mutate then " (relabelled)" else "");
    if not ok then begin
      incr failures;
      Printf.printf
        "FAIL db %d: linear_db and tss_db%s are %s\n\
        \  reproduce: fuzz_tss --seed %d --count 1 --size %d%s\n%s\n%!"
        i (if mutate then " (relabelled)" else "") (verdict_str v)
        (seed + i) n (if mutate then " --mutate" else "") doc
    end
  done;
  !failures
