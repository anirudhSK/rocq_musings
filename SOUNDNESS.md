# Soundness status of the Caracara equivalence checkers

This document records which equivalence-checking results are proven in Rocq, which are
proof debt (the semantics is faithful, the lemma is not built yet), and which are model
debt (the semantics itself is deliberately approximate).

## What is actually checked

There are two checkers.

| Checker | Where | Compares | Status |
|---|---|---|---|
| `equivalence_checker_cr_dsl` (one transformer) | `SmtQuery.v` | final headers + state vars | **PROVEN (Qed)** — `equivalence_checker_cr_sound`, `equivalence_checker_cr_complete` |
| `modnet_equivalence_checker` (a network) | `SmtModuleQuery.v` | accept flag, output packet, bits read, memory contents, memory access extents | **PROVEN (Qed)** — `_sound` and `_complete` |

**There are no admits left in the project** (`grep -c Admitted *.v`). That is a statement
about proof debt only; the model debt below is untouched by it, and so is the gap between
the symbolic and concrete semantics described next.

## Trust assumptions

The solver is axiomatised in `SmtQuery.v`:

```coq
Parameter smt_query : SmtBoolExpr -> SmtResult.
Axiom smt_query_sound_some : forall e v, smt_query e = SmtSat v -> eval_smt_bool e v = true.
Axiom smt_query_sound_none : forall e, smt_query e = SmtUnsat -> forall v', eval_smt_bool e v' = false.
```

`Print Assumptions` on a network lemma should show these and nothing else. It is tighter
than that in practice: `modnet_equivalence_checker_sound` reports exactly `smt_query` and
`smt_query_sound_none`, and `_complete` exactly `smt_query` and `smt_query_sound_some` —
each direction uses one axiom. Anything beyond them is a new trust assumption.
`SmtModuleQuery.v` ends with the `Print Assumptions` calls that check this; they print
during `make`, so a new axiom shows up in the build log.

`Extraction.v` discharges `smt_query` with `Z3Solver.solve`. That is the real trust
boundary: the axioms are stated over `eval_smt_bool`, so every place the Z3 encoding and
`eval_smt_*` disagree is an unsoundness the Coq development cannot see. The known ones are
listed under "Model debt" below.

### The query compiler

That boundary used to be 254 lines of OCaml. `Z3Solver.solve` reconstructed `CrVal`'s type
discipline in bitvectors from scratch — masking to widths, the `(value, tag)` pair, the
type tests behind `eqb`/`ltb`/`iv_binop_at`, the `CrVal.not` width chain, the bounds
guards standing in for a partial `ld_arr`/`st_arr` — and nothing related any of it to the
definitions in `CrVal.v` it was reproducing. Getting it wrong there made
`smt_query_sound_some` **false** rather than merely imprecise; that happened once, with the
untyped lowering.

`SmtCompile.v` moves that work into Rocq. `solve` runs `compile_bool` before lowering, and
the result is in the **core fragment**: every arith term denotes `IntVal _ u64`, where the
rich operations *are* their bitvector counterparts (`mask_width W64` is the identity, so
`add_at u64` is `bvadd`; `eqb` on two `u64`s is bitvector equality; `ltb` is `bvult`). The
fragment is a subset of `SmtExpr`, not a new type, so there is one syntax, one evaluator,
and the obligation has one shape:

```coq
Theorem compile_correct : forall e v, lcb e = true ->
  eval_smt_bool (compile_bool e) v = eval_smt_bool e v.   (* plus arith/array components *)
```

Both sides are read by the same `eval_smt_bool` under the **same valuation** — there is no
encoding relation between two valuations to get right, which a separate core datatype would
have needed. `SmtVarVal`/`SmtVarTag` buy that by splitting a scalar in the syntax rather
than in the valuation.

**`compile_correct` is `Admitted`.** So this reduces and relocates the trust; it does not
discharge it. What is gained is real but should be stated precisely:

- the transformation is now written in a language with a semantics, against the definitions
  it has to agree with, instead of from memory in OCaml;
- the obligation is one statement instead of diffuse across 254 lines;
- `Z3Solver.ml`'s lowering is structural — one Z3 constructor per node — with three
  documented exceptions (`SmtArrEq`, `SmtBitDiv`, `SmtBitSlice`), each of which says why;
- a non-core constructor reaching the lowering raises rather than being lowered on a guess.

**The side constraints are gone**, and with them a real gap. `solve` used to assert the
goal *alongside* assumptions about the model — a region's cells being bytes, a scalar's tag
being in range — while `smt_query_sound_none` concludes about **every** valuation. An UNSAT
of goal-and-assumptions only rules out the valuations satisfying the assumptions, so the
axiom held only because those assumptions happened to be vacuous on the Rocq side, by a
coincidence between definitions in two languages.

Both are now inside the query. A scalar needs no constraint at all:
`compile_arith`'s `SmtArithVar` case wraps *both* halves in `is_int_tag`, so the term reads
zero exactly where `CrVal.val_of`/`tag_of` do, and a model is free to pick anything
unobservable. A region cannot be handled that way — `eval_smt_mem`'s `SmtArrVar` arm maps
`CrVal.to_byte` over an unbounded array, which is not a term — so it becomes the conjunct
`SmtCompile.regions_wf`, stated over the declared length. `regions_wf_true` (**`Qed`**)
proves it true under every `SmtValuation`, which is what makes conjoining it
axiom-preserving; `compile_query_correct` puts the two halves together. `solve` now asserts
precisely the formula the axioms are stated about.

What remains outside: `compile_correct` itself, and the `SmtArrEq` extensionality argument
(below, unchanged).

`compile_correct` assumes `lcb`: every array merge joins regions of equal declared length,
which is what makes the syntactic `smt_arr_len` agree with the denoted `arr_len`. It holds
of everything the checker builds (`eval_general_program_symbolic_mem_rooted`), and `solve`
checks it and refuses the query otherwise.

The empirical guard is `TestEquality`'s `witness:` tests: they solve a hand-built
`SmtBoolExpr` and re-check Z3's model against `eval_smt_bool` of the **original** term.
Since `solve` compiles internally, that is `compile_bool_correct` tested end to end.

## What equivalence means

Two runs of a network agree when either both rejected, or both accepted and

- the emitted packets are equal (`sym_out_equal`, comparing presence conditions as well as
  bit values, so differing output *lengths* count as differing);
- they read the same number of input bits (`check_sym_bits_read`);
- every declared memory region holds the same contents over its declared length
  (`check_sym_mem_equal`, one `SmtArrEq` per region);
- they required the same number of bytes of every declared region
  (`check_sym_mem_extent`, one past the highest offset touched).

The last two arrived with the memory merge. Contents are compared because a region is an
observable side effect — it is how a program talks to a map or to its caller's buffer —
unlike a header, which is internal scratch. Extents are compared for the same reason
`sh_bits_read` is: a program that reaches further into a region needs more of it to be
there, so it can fault where the other does not, even when everything else matches.

**"Both rejected" is an accepting case.** That makes the checker only as good as its notion
of validity: any imprecision in `gps_valid`, in *either* direction, is unsound.
Over-approximating acceptance compares outputs that concretely never happen;
under-approximating it hides real differences inside the both-rejected case. Two
consequences are baked into the semantics:

- `eval_deparser_concrete` is total rather than carrying an approximate validity condition
  (below);
- loads and stores are total: an individual out-of-bounds access yields `ErrorVal` / is
  dropped and clears nothing. The overrun is recorded in `sh_mem_extent` and turned into a
  rejection **once, at the end of the network**, by the memory-safety conjunct
  `eval_general_program_{concrete,symbolic}` fold into the final `gps_valid`
  (`mem_extents_in_bounds_concrete` / `mem_extents_in_bounds_smt`, exact mirrors of each
  other: same fold over `pmap_keys` of the extent map, `negb (CrVal.ltb …)` against
  `SmtBoolNot (SmtBoolLt …)`, same u64 bound from `region_len_map`).

  Doing it per-run rather than per-access is what keeps it expressible on both sides. A
  store is not atomic — `SmtArrSt` is guarded cell by cell and "all of these cells are in
  bounds" is not an `SmtBoolExpr` — so a rejecting *access* has no symbolic counterpart,
  while a rejecting *run* is just one more conjunct on a flag that is already a formula.

  Two consequences follow from the both-rejected disjunct and are worth stating plainly.
  A pair of programs that **both** overrun now compares `Equivalent` whatever they emit;
  and the verdict of a fixed out-of-bounds pair no longer exercises the `SmtArrSel` /
  `SmtArrSt` bounds guards at all, which is why those moved to the `witness:` tests
  ("an out-of-bounds read is ErrorVal", "an out-of-bounds write leaves the region alone")
  rather than resting on `TestEquality`'s test 26. The guards remain load-bearing for a
  *data-dependent* offset, where the run is invalid only on the valuations that actually
  overrun and the region conjuncts still run on the rest.

### Why a deparser is total

Emitting a header that holds no integer — `UninitVal` from a header never written,
`ErrorVal` from a type-mismatched op — writes zero bits rather than failing.

An earlier version guarded the emit and returned `None` on a non-integer header.
`eval_deparser_symbolic` has no counterpart to such a guard: symbolically a header is an
`SmtArithExpr`, and deciding whether it denotes an `IntVal` needs a path-sensitive
analysis over `SmtConditional` plus the type-agreement rules of `iv_binop_at`. While the
guard existed, the symbolic side treated every deparse as accepting, so the two semantics
disagreed — and by the rule above, that disagreement is unsound in *either* direction, not
merely conservative. Soundness forces the symbolic validity to be exact, and the cheapest
exact option is to have no validity condition on either side. It also restores the
invariant `DeparserCommuteLemmas` is written against: a deparser never fails, so the
commutation is a plain equality.

The cost is a lost diagnostic — emitting a never-written header silently produces zeros.
Reinstating the guard requires an exact symbolic counterpart: either a static
well-formedness check that makes the guard vacuous, or a
`hdr_valid : SmtArithExpr -> SmtBoolExpr` folded into `gps_valid` the way the parser folds
`spr_accept`.

The practical corollary for tests: a program that rejects every packet is equivalent to any
other program that rejects every packet, and a program that emits a zeroed byte is
equivalent to any other that does. It is easy to write two "equivalent" programs that are
both simply broken. `TestModuleSemantics` therefore checks concrete outputs, contents and
extents, not only checker verdicts.

## Proof debt

Both network lemmas are proved. What remains is not a missing lemma but a missing
*connection*, described next — do not read "no admits" as "the semantics is verified".

### What the network proofs do and do not say

Read the statements carefully before leaning on them. Both relate the checker's verdict to
`concretize_sym_modnet_state` applied to the **symbolic** final states — the states the
checker itself reasoned about. Neither says anything about `eval_general_program_concrete`.
So together they close the gap between *what the solver reported* and *what the two
symbolic states do under a valuation*; they do not close the gap between the symbolic and
concrete semantics. Anyone reading "the network checker is proven sound and complete" as
"the symbolic semantics is faithful" is reading more than is there.

That second gap is `ConcreteToSymbolicLemmas.v`'s subject at the transformer level
(`commute_sym_vs_conc_transfomer_hdr` / `_sv`). Its analogues now exist for **memory**
(`MemCommuteLemmas.v` — value, op, op list, match-action rule, transformer), for the
**deparser** (`DeparserCommuteLemmas.v`) and for the **parser**
(`ParserCommuteLemmas.v` — `run_parser_commute`, `eval_parser_commute`), all
`Closed under the global context`. What is still missing is the **network** analogue:
the induction over `eval_network_from_*` that assembles them, which is the single
admitted lemma `eval_general_program_commute`. TODO.md 1.1 item 5 has the shape it has
to take.

Its conclusion is `gps_agree`, which is structural equality on every field of a
`GeneralConcreteState` **except the two memory maps, compared pointwise**. That is not a
convenience. An equality of records is false: `sh_mem_extent` starts as `PMap.init` and
every access adds a key, so a symbolic merge binds keys for every branch's regions where
a concrete run binds only the branch that ran, and `PMap.map` preserves trees. The two
differ while `!!` agrees at every key, the surplus bindings all holding the map's own
default. It costs nothing — this lemma's conclusion never compares maps, only
`ld_arr ((sh_mem ...) !! ...)`, `(sh_mem_extent ...) !! ...`, the two tapes and the flag.

**Relating the two evaluators is what finds bugs in the model.** Both of the divergences
below were live in the semantics and invisible to every existing test and proof, because
until the commutation lemmas existed nothing compared a concrete run to a symbolic one:

- A zero-width `Peek` past the end of a chained parser's residual **accepted symbolically
  and rejected concretely**. `select_bits_valid` conjoined the presence of the peeked
  window, which is empty at width zero; it now measures from the cursor, which is what
  `select_bits_available_concrete` actually demands.
- `merge_header_maps` **dropped a header written only on the else branch of a `select`**,
  taking its keys from the then-branch alone. Same failure mode as model-debt item 2
  below, and contained only by the same seeding. It now folds over both key sets.
- A transformer **dropped a write to a state variable not in its declared `states`
  list**. Model-debt item 2 again, and the half of it that was never fixed: the header
  map is seeded from `collect_write_headers` (what the program *writes*), the state map
  from the module's declared states (what it *announces*), and nothing requires the
  targets to be among them. `CrVarLike.force_keys` now puts every written target in the
  domain without changing any value.

The first two are described in full in TODO.md 1.1.2, the third in 1.1.3.

Three things the proofs turned up that are worth knowing:

- **The `well_formed_general_program` and `is_linear_chain` hypotheses are used by
  neither direction.** They are still in both statements (they belong there once the
  concrete side is connected), but both results hold for any two programs the checker
  is handed. That is stronger than the statements advertise.
- **The two directions are not symmetric in what they need.** `_sound` has to turn an
  equality of loaded *values* into an equality of *loads*, which requires knowing both
  regions have the same shape; `_complete` runs the implication the easy way (differing
  values force differing loads outright) and needs no memory invariant at all. Only the
  write-tape invariant is shared.
- **Three invariants had to be established first**, all about the symbolic semantics rather
  than about the solver, and each easy to break by a careless change:
  - Every entry of `sh_write_tape` carries `cvc = SmtTrue`
    (`eval_general_program_symbolic_wt`). Without it the output-length conclusion is
    **false**, not merely unproven: `sym_out_equal` compares tapes of different lengths by
    asserting the surplus entries are absent, while `concretize_sym_modnet_state` maps over
    the raw list and does not shrink it. The invariant holds because
    `eval_deparser_symbolic` marks every emitted bit present, and nothing else appends.
    `_complete` needs it too, and for the mirror-image reason: without it a pair whose
    tapes differ only in a presence condition would be reported `NotEquivalent` while the
    concretized tapes agree on both length and bits.
  - Every region expression stays *rooted* at the state's initial expression for that key
    (`eval_general_program_symbolic_mem_rooted`): a store only wraps in `SmtArrSt` and a
    merge only in `SmtArrIte`, so the leaves never change. This was originally what let
    `_sound` turn an equality of *loaded values* into an equality of *loads*. Since
    `check_sym_region_equal` became a single `SmtArrEq`, whose semantics constrains the
    loads directly, neither lemma needs it — its remaining jobs are to justify the
    `SmtArrEq` lowering (Model debt item 4) and to bound the Z3 guard (below). Do not
    delete it on the grounds that no *checker* lemma cites it.
  - **`smt_arr_len` agrees with the length of the array a region denotes**
    (`eval_general_program_symbolic_arr_len_agrees`). This one is easy to overlook because
    `smt_arr_len` plays no part in the Coq semantics at all: `eval_smt_mem` bounds a read
    by the denoted `arr_len`, while `smt_arr_len` is a separate syntactic walk that exists
    only so `Z3Solver.ml` can emit the bounds guard Z3's total `select` otherwise lacks.
    Its `SmtArrIte` case takes one branch and discards the other, which is sound *only*
    under rootedness — and for a long time nothing connected the two, so a wrong length
    there would have silently admitted out-of-bounds reads the Coq semantics answers with
    `ErrorVal`. The lemma is proved from both halves of the rooted invariant and carries no
    axioms, so the invariant now has a call site and breaking it breaks the build.
    Cross-boundary regression test: `TestEquality`'s "out of bounds, the order stops
    mattering".

## Model debt

1. **Linear chains only.** The semantics assume `is_linear_chain` (`is_dag ∧ single_sink ∧
   no_fan_out ∧ no_fan_in`), which both network lemmas take as a hypothesis — though
   neither proof turns out to need it (see above), so today the assumption is really only
   load-bearing for the concrete-side connection that is still missing.
   Fan-out DAGs are not faithfully modelled. Memory makes this sharper than it was: memory is global
   mutable state threaded through `GeneralProgramState`, so with fan-out there would be a
   coherence question that the model simply does not pose.

2. **`update_all_varlike` cannot introduce a header — FIXED, in the initialization.**
   `CrVarLike.new_pmap_from_old` rebuilds a header map from the keys already in it, so
   `eval_transformer_smt` — which merges its rules through `update_all_varlike` — used to
   **drop any header first written inside a transformer**, while
   `eval_transformer_concrete` (which uses `update_varlike`, i.e. `PMap.set`) kept it. A
   network whose observable output landed in a header no parser populated then emitted
   bits concretely and nothing symbolically, and `modnet_equivalence_checker` compared two
   empty outputs and answered `Equivalent`.

   Fixed by seeding, not by widening the merge: `init_general_symbolic_state` and
   `init_general_concrete_state` now seed `sh_hdr_map` with the network's whole header
   interface (`CrVarLike.collect_write_headers` — transformer write targets, parser
   extractions and select reads, deparser emits). That fixes the DOMAIN, which is all
   this bug needed: it only makes the key present so the merge can see it.

   What each entry *holds* is a separate question, and the answer now depends on the
   header. A header some parser extracts is a **field register** and holds an arbitrary
   value of its own width on entry — `seed_header_syms` gives it
   `SmtCast u64 ty (SmtVarVal "hdr_<h>")`, unprefixed so both programs share it, and
   `seed_header_concrete` starts it at `mk_int ty 0` as one inhabitant. A header only a
   transformer writes is a temporary and still holds the map's default, for which the
   seeding remains observationally a no-op.

   This is a third instance of the three-sides-must-agree pattern, alongside memory
   bytes. `SmtCast u64 ty (SmtVarVal _)` denotes *only* `ty`-wide integers whatever the
   valuation, so the symbolic side **forces** `concrete_gp_state_is_valid`'s header
   clause instead of the solver having to be constrained into it — which is what keeps
   `smt_query_sound_none`, quantified over every valuation, true. The motivating case is
   ParserHawk's IPU pipelines, whose transition keys name fields a later node extracts;
   its model reads those as the register's initial contents
   (`initial_field{i} : BitVec(width)`), and under the old uninit seeding every such
   select was dead, silently pruning a transition. Regression test: `TestEquality`'s
   "hdr init: a register read before its extraction is free", which is `Equivalent`
   under uninit seeding and `NotEquivalent` under this one.

   Still unpinned: `mod_states`, whose transformer entries carry free state and control
   variables, and headers no parser extracts.

   Widening `update_all_varlike` was the alternative and is worse: the `CrVarLike` class
   gives that field the type `(A -> T) -> TransformerState T -> TransformerState T`, with
   no key list to extend, so it would change the class, all three instances and the `Qed`
   proofs resting on `update_all_varlike_lookup_unchanged`.

   Note what this does *not* buy: `SmtQuery.v`'s lemmas still carry
   `is_varlike_in_ps s h <> None` hypotheses. Those are now satisfiable for a network's
   headers by construction, but they are still hypotheses.

   **The same hole was open for STATE VARIABLES until now, and the seeding did not close
   it.** A transformer's `t_state_map` is seeded from the module's *declared* `states`
   list — what it announces — while the header map is seeded from what the program
   *writes*. Nothing requires a rule's targets to be among the declared states
   (`well_formed_module` asks for `list_norepet`, `Sorted`, `transformer_has_default` and
   `no_mem_ops_in_par`, and says nothing about containment), so a write to an undeclared
   state variable survived concretely and vanished symbolically — exactly the bug above,
   one map over. `CrVarLike.force_keys` now forces every target of
   `collect_module_state_targets` into the domain. It cannot set the default the way the
   header seed does: a declared state variable's entry is a free `SmtArithVar` standing
   for its value on entry, so each key is re-set to the value it already reads
   (`PMap.gsident`), which is the identity extensionally and differs only in the domain —
   which is the only thing `update_all_varlike` looks at.

3. **A region's entry contents were any `CrVal`, not bytes — FIXED, on all three
   sides.** A declared region's contents on entry are an input supplied by the model.
   The cell tags were pinned only to `0..5` (every `CrVal` tag), so a model could hand
   back a cell that was `ErrorVal` or `UninitVal`, and the value field was not bounded
   at all, so a cell tagged `u8` could hold more than a byte.

   Both are observable. `ld_val` casts every cell with `cast u8 _`, so one non-byte cell
   makes an entire multi-byte load `ErrorVal`; `CrVal.ltb` is false on `ErrorVal` in
   **both** directions, so `x > 100` and `x < 101` are both false and two programs that
   test opposite ways were reported `NotEquivalent` on a machine state that cannot
   occur. And `cast u8 u64` masks to the target width rather than truncating, so an
   unbounded value would make the byte assembly overlap neighbouring cells — a `u64`
   load and eight `u8` loads recombined would disagree. Both are exactly the shapes an
   `-O0`/`-O2` comparison puts side by side, which is how this surfaced.

   Fixed in lockstep, because the three sides have to agree or one of the
   `smt_query_sound_*` axioms becomes false: `eval_smt_mem`'s `SmtArrVar` arm coerces
   through `CrVal.to_byte`; `Z3Solver.ml` pins each cell of `0..len` to the `u8` tag
   with value `<= 255`; `CrVarLike.init_concrete_mem` builds zero-byte regions
   (`mk_region_zero`); and `concrete_gp_state_is_valid` requires it of the concrete
   states the results are about. Only the ENTRY contents are constrained — a cell can
   still become `ErrorVal` mid-run, which is real behaviour.

   The cost, stated plainly: a run that reads a region no one wrote is no longer a
   modelled input, so the results say nothing about it. That is the trade for having
   the model mean "real memory".

4. **Z3 encoding vs `eval_smt_*` — FIXED, by encoding the type tag.** `eval_smt_arith` is
   type-checked throughout: `eqb`/`ltb` require both operands to carry the same
   `CrIntType` and are false otherwise, `iv_binop_at ty` requires both to be typed `ty`
   and yields `ErrorVal` otherwise, `cast from to` checks `from`, and `UninitVal` and
   `ErrorVal` are values in their own right (`eqb UninitVal UninitVal = true`). The
   lowering used to compare and operate on bare 64-bit bitvectors, masking only *results*,
   with `ErrorVal`/`UninitVal` both becoming the numeral 0.

   That was not merely conservative — **it made `smt_query_sound_some` false for the actual
   solver**, and the tree carried a witness: `TestEquality`'s "tss basic" (linear-scan vs
   tuple-space-search, `PktClass.v`) returned `NotEquivalent` on a model that
   `eval_smt_bool` rejected and whose witness packet gave label 42 from *both* classifiers
   concretely.

   Fixed: `Z3Solver.ml` now lowers each arith expression to a **(value, tag)** pair, tag
   ∈ {0 = ErrorVal, 1 = UninitVal, 2..5 = IntVal at W8/W16/W32/W64}, and every case
   mirrors the corresponding case of `eval_smt_arith` — including where that yields
   `ErrorVal`. A memory cell is a `CrVal` too, so a region is an array from a 64-bit
   offset to a packed `(tag, value)` word. "tss basic" is back to `Equivalent`, and every
   surviving `NotEquivalent` in the suite has been checked to have a witness that
   `eval_smt_bool` agrees with.

   Two useful side effects: the SAT model's `CrIntType` is now *read off the tag* rather
   than guessed from the ops that consume a variable (the old `collect_var_widths`
   pre-pass is gone), and a variable the model leaves untyped comes back as a non-`IntVal`
   rather than a fabricated `u64`.

   **Reading a tag back is as load-bearing as lowering one, and it is not the identity
   on the raw bits.** Two ways this went wrong, both fixed:

   - *`to_amap` must distinguish `ErrorVal` from `UninitVal`.* It used to map every tag
     outside 2..5 to `UninitVal`. But tag 0 is `ErrorVal`, `eqb ErrorVal UninitVal =
     false`, and `eval_smt_arith`'s `SmtArrSel` arm returns the loaded cell **verbatim**
     (`Legal v' => v'`) — so the returned valuation did not satisfy the query Z3 had just
     answered. Not a corner case: `byte_of_val` sends every non-`IntVal` to `ErrorVal`
     (via `slice_val`'s catch-all), so storing an unwritten header fills its cells with
     `ErrorVal`, and *every* cell of a memory model printed as `-` was really `ErrorVal`.
   - *A free array's cell tags are unconstrained.* Nothing asserted `tag <= 5` for cells
     of an `SmtArrVar`, so a model could pick 6 or 7 — bit patterns no `CrVal` denotes
     and `to_amap` cannot reconstruct. `Z3Solver.solve` now emits a side constraint
     pinning cells `0..len` of each free array to 0..5.

     **Pin the array, do not normalise the read.** Folding `> 5` onto `tag_err` inside
     `SmtArrSel` looks equivalent and is not: `SmtArrEq` lowers to `mk_eq` on *whole
     arrays*, which compares cells RAW, so a read-side fix lets Z3 find differences no
     valuation can express. That regression is what the "a cell read back is the cell
     that is there" witness test in `TestEquality.ml` pins down — it went `SAT, WITNESS
     REJECTED` under the read-side version and is `UNSAT` under the pin.

     Excluding these models loses nothing real (every `CrVal` carries a tag in 0..5), so
     `smt_query_sound_none` is unaffected. Only `0..len` needs pinning: reads and stores
     are guarded to that range, `to_amap` reads no further, and beyond it both sides of
     an `SmtArrEq` are the same term.

   The **scalar** path is safe by construction and needs no such care: `eval_smt_arith`'s
   `SmtArithVar` arm coerces every non-`IntVal` to `ErrorVal`, exactly mirroring the
   `ite (tag_is_int t) t tag_err` the lowering wraps a free tag in. `to_vmap` printing
   "error" rather than "uninit" is cosmetic. The asymmetry with `SmtArrSel`, which has no
   such coercion, is the whole reason the array side is delicate.

   So: a new `SmtArrExpr` or `SmtArithExpr` constructor must lower its tag as well as its
   value, **and** every tag the model can hand back must reconstruct to the `CrVal` the
   lowering meant by it.

   **There is a harness for this now** — the `witness:` tests at the end of
   `TestEquality.ml`. They build an `SmtBoolExpr` directly, call `Z3Solver.solve`, and
   re-evaluate the same expression under the model it returned with `eval_smt_bool`.
   No program plumbing is involved, so a new expression form can be checked in a few
   lines. A verdict test cannot see this class of bug: the verdict is right and only the
   witness is wrong.

   It remains why the memory ops were built **total**: adding a partial operation whose
   partiality Z3 cannot see is precisely the imprecision the both-rejected disjunct turns
   unsound. Two places where the memory encoding deliberately lines the two up, and where
   a future change must keep them lined up:

   - `SmtArrSel` is guarded: `ld_arr` is `Illegal` — hence `ErrorVal` — on a non-integer
     offset or one past the region's declared length, while Z3's `select` is total, so the
     lowering conditions on both. The bound comes from `SmtExpr.smt_arr_len`, the same
     walk the Coq side uses.
   - `SmtArrSt` is guarded the same way, because `CrVal.st_arr` drops a rejected write and
     leaves the region unchanged. An unguarded total `store` would be visible to a later
     in-bounds read at the same numeric index, which the concrete run never performed —
     and, since `SmtArrEq` (next item), it would also leave the two regions differing out
     of bounds where extensional equality can see it.
   - **`SmtArrEq n a1 a2` lowers to ONE extensional array equality and ignores `n`.**
     The Coq semantics is cell-by-cell agreement over `n` cells; Z3's `=` on arrays
     compares every index. Those coincide only because of two facts about the terms this
     checker builds, and both are needed:
     - both arrays are rooted at the same `SmtArrVar`, so outside the declared length they
       are the same term — this is what `eval_general_program_symbolic_mem_rooted` is for
       now that neither network lemma needs it;
     - every `SmtArrSt` under them is guarded in bounds, per the previous item.

     `n` and the root's `len` coincide because `CrVarLike.init_symbolic_mem` and
     `SmtModuleQuery.check_sym_region_equal` both take them from the same `mr_len`. If they
     ever diverge, the lowering becomes strictly stronger than the semantics and the checker
     can report differences the concrete semantics cannot produce.
   - **A cell's value field is 64 bits wide although a cell only holds a byte.** Since a
     region became an array of bytes, every cell written by the semantics holds a `u8`, so
     56 of those bits are dead — and narrowing them to 8 is worth about **4.5x** on a
     memory-heavy query (a 766-instruction eBPF pair: 4.9s to 1.1s). It is not done,
     because it would be unsound as things stand. `SmtTypes.sv_arrs` is an arbitrary
     function: a valuation may map a cell to `IntVal v u8` with `v > 255`, nothing requires
     it to be built with `mk_int`, and `CrVal.ld_val` reads such a cell through
     `cast u8 u64`, which hands back the raw `v`. An 8-bit value field cannot represent
     that valuation, so `smt_query` would be answering over a strictly smaller model space
     than `smt_query_sound_none` quantifies over — the same shape of gap as the untyped
     lowering in item 3, just rarer.

     The fix is on the Coq side, not the solver's: make a cell read normalise to the
     cell's width (`ld_cell` masking a `u8` cell to 8 bits), which is what "a region is an
     array of bytes" ought to mean anyway. Then the 8-bit field is exact and the speedup
     is free. Worth doing before the eBPF programs get much bigger.

   `TestEquality`'s "out of bounds, the order stops mattering" test is the regression test
   for all three — it reports `Equivalent` only if every guard is present.

5. **First-match, type-first matching.** `eval_transformer_concrete` runs the first rule
   whose pattern holds, so list order is priority; `CrVal.eqb`/`ltb` compare the
   `CrIntType` before the value, so a `u64` header never matches a `u8` constant and both
   are false on `UninitVal`. Deliberate, pinned by `TestModuleSemantics`, and — since
   item 3 — implemented on the symbolic side too.

## Verification

```bash
rocq makefile -f _CoqProject *.v -o Makefile
make -j
perl sync_dune_modules.pl     # only if extraction produced new modules
dune build --profile release
dune runtest
```

Then confirm `grep -c Admitted *.v` reports nothing. The `Print Assumptions` check is
automatic — `SmtQuery.v` and `SmtModuleQuery.v` run it, so `make` prints each lemma's
axioms and anything beyond `smt_query` and its two soundness axioms is a new trust
assumption.
