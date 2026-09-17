# Soundness status of the Caracara equivalence checkers

Records which equivalence-checking results are proven in Rocq and which gaps are
deliberate model debt (the semantics itself is approximate, not merely unproven).

## What is actually checked

| Checker | Where | Compares | Status |
|---|---|---|---|
| `equivalence_checker_cr_dsl` (one transformer) | `SmtQuery.v` | final headers + state vars | **Qed** — `equivalence_checker_cr_sound`/`_complete` |
| `modnet_equivalence_checker` (a network) | `SmtModuleQuery.v` | accept flag, output packet, bits read, memory contents | **Qed** — `_sound`/`_complete` |

`grep -c Admitted *.v` is zero across the project. `Print Assumptions` on
`modnet_equivalence_checker_sound` reports exactly `smt_query` and
`smt_query_sound_none`; on `_complete`, exactly `smt_query` and `smt_query_sound_some`.
One solver axiom per direction, nothing else.

That is proof debt only. The model debt below is untouched by it: the semantics still
assumes a linear chain, `Par` still has no parallel semantics, and the front end that
produces these programs is outside this tree and unverified.

## Trust assumptions

The solver is axiomatised in `SmtQuery.v`:

```coq
Parameter smt_query : SmtBoolExpr -> SmtResult.
Axiom smt_query_sound_some : forall e v, smt_query e = SmtSat v -> eval_smt_bool e v = true.
Axiom smt_query_sound_none : forall e, smt_query e = SmtUnsat -> forall v', eval_smt_bool e v' = false.
```

`SmtModuleQuery.v` ends with the `Print Assumptions` calls that check this against the
two lemmas above; they print during `make`, so a new axiom shows up in the build log.

`Extraction.v` discharges `smt_query` with `Z3Solver.solve`. That is the real trust
boundary: the axioms are stated over `eval_smt_bool`, so anywhere the Z3 encoding and
`eval_smt_*` disagree is an unsoundness Coq cannot see. Known instances are under "Model
debt" below.

### The query compiler

`Z3Solver.ml`'s job used to be reconstructing `CrVal`'s type discipline in bitvectors by
hand — masking to widths, the `(value, tag)` pair, `eqb`/`ltb`/`iv_binop_at`'s type
checks — with nothing relating it to `CrVal.v`. Getting that wrong once made
`smt_query_sound_some` **false** (the untyped lowering, item 4 below).

`SmtCompile.v` moves that work into Rocq. `solve` runs `compile_bool` before lowering,
producing a term in the **core fragment**: every arith term denotes `IntVal _ u64`,
where `CrVal`'s rich operations *are* their bitvector counterparts. The fragment is a
subset of `SmtExpr`, so one syntax and one evaluator suffice:

```coq
Theorem compile_correct : forall e v, lcb e = true ->
  eval_smt_bool (compile_bool e) v = eval_smt_bool e v.   (* plus arith/array components *)
```

**`compile_correct` is `Qed`, axiom-free** — both sides are the same `eval_smt_bool`
under the same valuation, so no cross-encoding relation is needed. What remains on the
trust boundary is `Z3Solver.ml`'s lowering of the core fragment: one Z3 constructor per
node, three documented exceptions (`SmtArrEq`, `SmtBitDiv`, `SmtBitSlice`), and a raise
rather than a guess on a non-core constructor.

Two invariants a change to `SmtCompile.v` must preserve, both load-bearing for
`compile_correct`:
- the `reps` induction carries tag ∈ `0..5`, not just any word — without the bound two
  different tags could stand for the same `CrVal`;
- `SmtCellVal`/`SmtCellTag`/`SmtStCell` carry an `is_int_tag` guard on their index, the
  same guard `SmtArrSel` always had (three compiler cases the proof found unguarded).

`solve` also checks `lcb` and refuses a query that fails it — this is what guards the
`smt_arr_len = arr_len` agreement hypothesis (below). `compile_correct` needs no
side-constraint list: a scalar's `SmtArithVar` case wraps both halves in `is_int_tag`
inside `compile_arith`, and a region's byte-ness is the conjunct `SmtCompile.regions_wf`
(`regions_wf_true` is `Qed` under every valuation, so conjoining it is axiom-preserving).

`TestEquality`'s `witness:` tests are no longer the guard on `compile_bool` — that's
proved — they test what's left: the lowering and `solve`'s own plumbing.

## What equivalence means

Two runs of a network agree when either both rejected, or both accepted and:
- emitted packets are equal (`sym_out_equal`, comparing presence conditions, so
  differing output *lengths* count as differing);
- the same number of input bits were read (`check_sym_bits_read`);
- every **shared** memory region holds the same contents over its declared length
  (`check_sym_mem_equal`, one `SmtArrEq` per region — a region is an observable side
  effect, unlike a header, which is internal scratch).

### Which regions are compared

The two programs need not declare the same memory. `modnet_equivalence_checker` guards
memory with `mem_writes_shared`, not equality of the two declaration lists:
- **compared**: `CrModule.shared_region_decls` — regions both programs declare, at the
  same length;
- **must be in that set, or the verdict is `NotEquivalentVariablesDiffer`** before any
  query is built: every region either program can write (`collect_store_regions`, a
  static, over-approximating walk).

A read is not a side effect — a region only one side declares and reads is simply
absent from the comparison, since whatever a load produces is already compared wherever
it lands. A write is: if p1 stores to a region p2 doesn't declare, p2's `sh_mem` holds a
fresh `SmtArrInit` there with no relation to p1's, so comparing would silently drop a
real side effect. The same reasoning bars comparing a shared name at two different
lengths (`SmtArrVar n 4` vs `SmtArrVar n 8` are different-length prefixes of one byte
stream, not one property). Matching write sets are *not* required — p1 storing and p2
never touching a shared region is comparable and decided by the query, the right answer
since p1's store may put back what was already there (this is what makes dead-store
elimination not get flagged). `TestEquality`'s five `obs:` tests pin this; the two
`NotEquivalentVariablesDiffer` cases are what fail if the guard is dropped.

**Access extents are deliberately NOT compared.** A fourth conjunct used to compare
`sh_mem_extent` (one past the highest offset touched per region), on the theory that
reaching further into a region could fault where the other run doesn't. That doesn't
survive the region model: every conjunct above sits inside `check_sym_pkt_out`'s
**both-valid** branch, so by the time any of them run, `mem_extents_in_bounds_smt`
(folded into `gps_valid`) has already ruled out either side faulting — extent differences
are then unobservable (contents are already compared cell-by-cell). The conjunct cost
real precision: it flagged dead-load elimination and load hoisting as `NotEquivalent`
(`TestEquality`'s "mem: a dead load is not observable" is the regression), and for a map
region the verdict depended on the transpiler's layout rather than either source
program. It would earn its place back only if a region's length became dynamic (e.g.
XDP's `data_end`), where each extent would need comparing against a symbolic length
rather than against each other — `sh_mem_extent` stays in the state for that reason and
for `mem_extents_in_bounds`.

**"Both rejected" is accepting**, so the checker is only as good as `gps_valid`'s
precision in *either* direction — over-approximating hides real acceptance behind a
false reject, under-approximating hides real differences inside both-reject. Two
consequences baked into the semantics:
- `eval_deparser_concrete` is total (below), not an approximate validity condition;
- loads/stores are total: an out-of-bounds access yields `ErrorVal`/is dropped, and the
  overrun is recorded in `sh_mem_extent` and turned into rejection **once, at the end of
  the network** (`mem_extents_in_bounds_{concrete,smt}`, exact mirrors of each other),
  because a store is not atomic and "all cells in bounds" has no `SmtBoolExpr` shape
  per-access. One consequence: a fixed out-of-bounds pair no longer exercises the
  `SmtArrSel`/`SmtArrSt` bounds guards at all (moved to `witness:` tests); the guards stay
  load-bearing only for a *data-dependent* offset.

### Why a deparser is total

Emitting a header holding no integer (`UninitVal`/`ErrorVal`) writes zero bits rather
than failing. An earlier version guarded the emit and returned `None`; the symbolic side
has no counterpart (deciding whether an `SmtArithExpr` denotes an `IntVal` needs
path-sensitive analysis), so the two semantics disagreed — unsound in *either* direction
by the rule above. The cheapest exact fix is no validity condition on either side, which
also restores the invariant `DeparserCommuteLemmas` needs: a deparser never fails, so
commutation is a plain equality. Cost: a never-written header silently emits zeros, so
`TestModuleSemantics` checks concrete outputs and contents, not only checker verdicts.

## Which concrete initial states the results are about

Both network lemmas quantify over `c_i = concretize_sym_modnet_state s_i f`. `InitReachable.v`'s
`valid_iff_reachable` (**Qed**, axiom-free) says these are exactly the sensible concrete
initial states — not a thin slice.

Validity is **defined**, not described: `InitInputs` is five families of free input
(header registers, packet bits, region contents, each module's ctrl/state vars) held
raw, with the initializer applying the same normalizer the symbolic side does. A state
is valid when it's `init_general_concrete_state_with p ii` for some inputs `ii`. (An
earlier, pointwise-predicate shape of "valid" was not provable — `PMap` is not
extensional, so a predicate that only speaks pointwise about the maps can't conclude an
equality of records; every concretization of an initial state has an *empty*
`sh_mem_extent` tree, and a pointwise-valid state with a different tree there falls
outside the image regardless of the predicate.)

```coq
Theorem init_concretize_eq : forall p pf f,       (* every concretization is a builder state *)
  concretize_sym_modnet_state (init_general_symbolic_state pf p) f
  = init_general_concrete_state_with p (inputs_of pf f).

Theorem valid_is_reachable : forall p pf ci,      (* and every builder state a concretization *)
  concrete_gp_state_valid p ci ->
  exists f, ci = concretize_sym_modnet_state (init_general_symbolic_state pf p) f.
```

Three things worth knowing:
- **The conclusion is an equation**, which rewrites straight into
  `modnet_equivalence_checker_sound` with no congruence lemma needed. It survives because
  concretization commutes with every fold the initializer is built from, using
  `PTree.extensionality`.
- **Realizability audits the naming scheme.** Answering an arbitrary choice of inputs at
  every name at once is the claim that the seeded name families are pairwise distinct.
  `seed_parse_name` (an inverse for `CrVarLike.seed_name`) gives that. Every seeded name
  is built in one place (`CrVarLike.SeedVar`/`seed_name`); a module-local name starts
  with `mod_mark` (`$`), separating shared and module-local namespaces for every program.
- **`valid_is_reachable_pair`** is the form the checker needs: one valuation realizing a
  choice of inputs for each of two programs, given they agree on shared inputs and that
  the two prefixes name disjoint module-local variables (`prefixes_disjoint`, holds by
  computation for `"p1"`/`"p2"`).

## Proof status: symbolic-to-concrete

Both network lemmas relate the checker's verdict to `concretize_sym_modnet_state` of the
**symbolic** final states — what the checker itself reasoned about. Closing the gap to
`eval_general_program_concrete` is a separate connection, proved level by level:
`ConcreteToSymbolicLemmas.v` (transformer), `MemCommuteLemmas.v` (memory),
`DeparserCommuteLemmas.v`, `ParserCommuteLemmas.v`, and at the network level
`NetworkCommuteLemmas.v` (`program_commute_full`, then `program_commute_init`). All are
**`Qed`, `Closed under the global context`**, and
`SmtModuleQuery.eval_general_program_commute` — the induction over
`eval_network_from_*` that assembles them — is likewise `Qed` and axiom-free. So
`modnet_equivalence_checker_sound` now relates its verdict to **concrete execution**.

**The statement is for `s = init_general_symbolic_state pf p`, not arbitrary `s` — this
is forced, not convenient.** Over an arbitrary `s` the lemma is false: give `s` a read
tape whose first position is absent under `f` and second present, feed it to a parser
extracting one bit — the concrete run sees `present_bits` (one bit), reads it, accepts;
the symbolic run conjoins presence of position 0 and rejects. `gps_valid` then differs.
The restricted lemma carries `well_formed_general_program p` and `is_linear_chain p`,
which `modnet_equivalence_checker_sound` already had — this is what finally gives those
two hypotheses a use.

Its conclusion is `gps_agree`: structural equality on every field of a
`GeneralConcreteState` **except the two memory maps, compared pointwise**. Record
equality would be false — `sh_mem_extent` starts as `PMap.init` and a symbolic merge
binds keys for every branch's regions where a concrete run binds only the branch that
ran, so the trees differ while `!!` agrees everywhere. The lemma's conclusion never
compares maps directly, so this costs nothing.

Three things about the proof, each a place a plausible statement would have been false:
- **Rejection is absorbing.** After a rejection the two runs diverge and
  `eval_parser_commute` no longer applies, so accept flags can only be shown *jointly
  false*, not equal — every writer of the flag conjoins on both sides, which is exactly
  what carries the verdict half of the bridge through modules that run after a rejection.
- **Module-state KIND agreement, not domain agreement, is the invariant** —
  `module_update_gs_*` dispatch on module kind and stored-state kind together and take a
  no-op fallback on mismatch, so domain agreement alone would let the two sides' domains
  come apart. `ms_kind_agree` is what's actually preserved; `well_formed_parser` earns
  its place here (a rejecting run's concrete parser must still return `Some`).
- **A deparser sees packets the two sides disagree about representationally** — read
  tapes concretize through `present_bits` (a filter) while
  `concretize_sym_module_state`'s `DeparserMod` branch maps positionally. This goes
  through only because a deparser reads nothing but its header map.

Relating the two evaluators found three live bugs invisible to every prior test, each
now pinned by a regression:
- a zero-width `Peek` past a chained parser's residual accepted symbolically, rejected
  concretely (`select_bits_valid` measures from the cursor now, not the peeked window);
- `merge_header_maps` dropped a header written only on a `select`'s else-branch (now
  folds over both key sets — same failure mode as model-debt item 2, contained by seeding);
- a transformer dropped a write to a state variable outside its declared `states` list
  (`CrVarLike.force_keys` now forces every write target into the domain — model-debt
  item 2's other half, for state instead of headers).

Further things worth knowing:
- `well_formed_general_program`/`is_linear_chain` are used by **neither** direction of
  the network lemmas (both hold for any two programs the checker is handed) — stronger
  than the statements advertise, kept because the concrete-side connection needs them.
- `_sound` needs a memory-shape invariant to turn equal loaded *values* into equal
  *loads*; `_complete` runs the easy direction and needs none. Only the write-tape
  invariant is shared by both.
- Three symbolic-semantics invariants had to be established first, each easy to break by
  a careless change:
  - every `sh_write_tape` entry carries `cvc = SmtTrue`
    (`eval_general_program_symbolic_wt`) — without it the output-length conclusion is
    **false**, since `sym_out_equal` shrinks surplus tape entries by asserting them
    absent while concretization does not shrink the raw list;
  - every region expression stays *rooted* at its key's initial expression
    (`eval_general_program_symbolic_mem_rooted`: a store only wraps `SmtArrSt`, a merge
    only `SmtArrIte`) — no longer needed by either soundness proof directly (superseded
    by `check_sym_region_equal` being a single `SmtArrEq`), but still justifies the
    `SmtArrEq` lowering (model debt item 4) and bounds the Z3 guard, so do not delete it;
  - `smt_arr_len` agrees with the length of the array a region denotes
    (`eval_general_program_symbolic_arr_len_agrees`) — `smt_arr_len` is a syntactic walk
    used only so `Z3Solver.ml` can emit a bounds guard; its `SmtArrIte` case takes one
    branch and discards the other, sound only under rootedness. Regression:
    `TestEquality`'s "out of bounds, the order stops mattering".

## Model debt

1. **Linear chains only.** `is_linear_chain` (`is_dag ∧ single_sink ∧ no_fan_out ∧
   no_fan_in`) is a hypothesis of both network lemmas, though neither proof turns out to
   need it directly — it's load-bearing for the concrete-side connection above. Fan-out
   DAGs are not faithfully modelled; memory sharpens this, since memory is global
   mutable state and fan-out would pose a coherence question the model doesn't ask.

2. **Header/state-variable domains, fixed by seeding.** `CrVarLike.new_pmap_from_old`
   rebuilds a map from keys already present, so `eval_transformer_smt` used to drop any
   header first written inside a transformer while the concrete evaluator kept it — a
   network whose output landed in such a header compared two empty outputs as
   `Equivalent`. Fixed by seeding both initial states' `sh_hdr_map` with the network's
   whole header interface (`CrVarLike.collect_write_headers`), which fixes the domain
   without widening the merge. What each entry *holds*: a field register a parser
   extracts gets `SmtCast u64 ty (SmtVarVal "hdr_<h>")` (unprefixed — both programs share
   it) / `mk_int ty 0`; a transformer-only header keeps the map's default
   (`SmtUninit`/`UninitVal`). Regression: `TestEquality`'s "hdr init: a register read
   before its extraction is free". The same hole existed for state variables (seeded
   from *declared* `states`, not from write targets) — `CrVarLike.force_keys` closes it
   by forcing every `collect_module_state_targets` key into the domain via
   `PMap.gsident` (identity on value, changes only domain). Still unpinned: `mod_states`
   free vars, and headers no parser extracts.

3. **Region entry contents pinned to bytes, fixed on all three sides.** Previously any
   `CrVal` tag (`0..5`) and unbounded value were allowed as entry contents, so a model
   could hand back an `ErrorVal`/`UninitVal` cell or an out-of-range byte — both
   observable (`ld_val`'s `cast u8 _` turns one bad cell into a whole `ErrorVal` load;
   `ltb` is false on `ErrorVal` both ways, so opposite-direction comparisons could both
   report false on a state that can't occur). Fixed in lockstep — the three sides must
   agree or an `smt_query_sound_*` axiom breaks: `eval_smt_mem`'s `SmtArrVar` arm coerces
   through `CrVal.to_byte`; `Z3Solver.ml` pins cells `0..len` to `u8` tag, value ≤ 255;
   `CrVarLike.init_concrete_mem` builds zero-byte regions (`mk_region_zero`); and
   `concrete_gp_state_is_valid` requires it of concrete states the results are about.
   Only entry contents are constrained — a cell can still become `ErrorVal` mid-run.

4. **Z3 encoding vs `eval_smt_*`, fixed by encoding the type tag.** The lowering used to
   compare/operate on bare 64-bit bitvectors and collapse `ErrorVal`/`UninitVal` both to
   0 — not merely conservative, it made `smt_query_sound_some` **false** for the actual
   solver (witnessed by `TestEquality`'s "tss basic": `NotEquivalent` from Z3 on a model
   both classifiers concretely agreed on). Fixed: every arith expression lowers to a
   **(value, tag)** pair, tag ∈ {0=ErrorVal, 1=UninitVal, 2..5=IntVal at W8/W16/W32/W64},
   mirroring `eval_smt_arith` case-for-case including its `ErrorVal` results. A region is
   an array from offset to packed `(tag, value)` word.

   Two follow-on fixes, both load-bearing for any new expression form:
   - `to_amap` must map tag 0 back to `ErrorVal`, not `UninitVal` (they're `eqb`-distinct,
     and `SmtArrSel` returns loaded cells verbatim, so conflating them desyncs the
     returned valuation from what Z3 actually answered).
   - a free array's cell tags must be pinned to `0..5` (`Z3Solver.solve` emits this over
     cells `0..len`) — **on the array, not by normalising the read**: folding tag `> 5`
     into `SmtArrSel` looks equivalent but isn't, because `SmtArrEq` lowers to `mk_eq` on
     whole arrays compared raw, so a read-side fix would let Z3 find differences no
     valuation expresses. Regression: TestEquality's "a cell read back is the cell that
     is there" (`SAT, WITNESS REJECTED` under the read-side version, `UNSAT` under the
     pin). The scalar path needs no such care — `SmtArithVar`'s lowering already coerces
     via `ite (tag_is_int t) t tag_err`, matching `eval_smt_arith` exactly.

   `TestEquality.ml`'s `witness:` tests (build an `SmtBoolExpr`, solve it, re-evaluate the
   model with `eval_smt_bool`) are the harness for this class of bug — a verdict test
   can't see it, since the verdict is right and only the witness model is wrong. Memory
   ops are built **total** for the same reason: a partiality Z3 can't see is exactly what
   the both-rejected disjunct turns unsound, so both `SmtArrSel`/`SmtArrSt` are guarded to
   `SmtExpr.smt_arr_len` (the same walk item above depends on) and `SmtArrEq n a1 a2`
   lowers to ONE extensional equality that ignores `n` — sound only because both arrays
   are rooted at the same `SmtArrVar` and every `SmtArrSt` under them is guarded in
   bounds. `n` and the root's declared `len` must come from the same `mr_len`
   (`CrVarLike.init_symbolic_mem` and `SmtModuleQuery.check_sym_region_equal` both do);
   divergence would make the lowering strictly stronger than the semantics.

   Known unrealized optimization: a cell's value field is 64 bits though only a byte is
   ever stored; narrowing to 8 measured ~4.5x on a memory-heavy query (766-instruction
   eBPF pair: 4.9s → 1.1s). Not done — `SmtTypes.sv_arrs` is an arbitrary function, so a
   valuation could map a cell to `IntVal v u8` with `v > 255` that an 8-bit field
   couldn't represent, making `smt_query`'s model space strictly smaller than
   `smt_query_sound_none` quantifies over. The fix belongs on the Coq side (`ld_cell`
   masking a `u8` cell to 8 bits, making "a region is bytes" exact) before doing it.

   Regression covering all of the above: `TestEquality`'s "out of bounds, the order
   stops mattering" — reports `Equivalent` only if every guard is present.

5. **First-match, type-first matching.** `eval_transformer_concrete` runs the first rule
   whose pattern holds (list order is priority); `CrVal.eqb`/`ltb` compare `CrIntType`
   before value, so a `u64` header never matches a `u8` constant and both are false on
   `UninitVal`. Deliberate, pinned by `TestModuleSemantics`, implemented symbolically too
   (since item 4).

## Verification

```bash
rocq makefile -f _CoqProject *.v -o Makefile
make -j
perl sync_dune_modules.pl     # only if extraction produced new modules
dune build --profile release
dune runtest
```

`grep -c Admitted *.v` should report zero. The `Print Assumptions` check is automatic —
`SmtQuery.v` and `SmtModuleQuery.v` run it during `make`, so a new axiom shows up in the
build log.
