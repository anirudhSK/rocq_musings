# Caracara IR — working notes

Rocq/Coq formalization of a P4-like packet-processing IR, extracted to OCaml and discharged against Z3. One unified IR (parsers, transformers, deparsers, loads/stores over declared memory regions). The old standalone memory IR (`CrMem.v` etc.) is deleted — any reference to it is stale. Longer prose: `README.md`, `SOUNDNESS.md`, `memo-memo.txt`.

## Build & test

```bash
rocq makefile -f _CoqProject *.v -o Makefile   # after adding/removing a .v
make -j                                         # Coq check + extraction → extracted_code/
perl sync_dune_modules.pl                       # only if extraction produced new modules
dune build --profile release
dune runtest                                    # ppx_expect
dune promote                                    # accept intentional output diffs
```

`make` must run before `dune build` — `extracted_code/*.ml` are generated (gitignored).

Outside CI (need separate toolchain):
```bash
translation/tests/run.sh
translation/tests/p4c_bugs/run.sh
dune exec --profile release bench_eq -- --reps 3
```
First two need `(cd translation/p4c/build && make rocq p4test)`.

## Layout

- `Cr*.v` — IR syntax (`CrDsl`/`CrModule`/`CrParser`/`CrTransformer`/`CrDeparser`) and evaluators (`CrConcreteSemantics*`, `CrSymbolicSemantics*`). `CrGeneralProgramState` = shared state; `CrProgramState` = per-module state + `MemCtx`; `CrVarLike` = state construction.
- `Smt*.v` — `SmtExpr` (bool/arith/array), `SmtTypes` (`SmtValuation`), `SmtQuery` (checker + axioms), `SmtModuleQuery` (`modnet_equivalence_checker`), `SmtCompile` (query compiler).
- `InitReachable.v` — which concrete initial states the lemmas are about (`valid_iff_reachable`). Not extracted.
- `*Lemmas.v`, `CtrlPlaneInvariants.v` — proof development. `ConcreteTransformerLemmas.v` is the congruence layer (`cs_lookup_eq`).
- `Test*Programs.v`, `PktClass.v` — example programs for OCaml tests.
- `Extraction.v` — **the gate**: nothing reaches OCaml unless named in `Separate Extraction`.
- `extracted_code/` — generated except files un-ignored in `.gitignore` (that list is authoritative): `Test*.ml`, `Shim.ml`, `CrTypeIF.ml`, `Z3Solver.ml`, executables (`EqCheck`, `DumpSexp`, `RunParser`, `RunNet`, `FuzzTss`, `BenchEq`), `IrSize.ml`/`SmtSize.ml`/`SolveTime.ml`.
- `test/` — `.out`/`.ir` fixtures. Hash map layout: presence `[0,4)`, keys `[4,20)`, values `[20,52)`, "real map full" byte at 52 (key=4, value=8, 4 slots → 53 bytes). Array map: presence then values. `TestModuleSemantics.seed_map` / `MapInfo` in `translation/ect/pybpf/translate.py`.
- `translation/` — front ends (excluded from Coq build). `p4c` and `ect` submodules, `parserhawk/lower_table.py`, differential tests.
- `bench/` — equivalence benchmark programs by family; `bench_eq` reads only `.ir`.

## Critical rules

**`extracted_code/dune` modules lists** — never hand-edit. `sync_dune_modules.pl` regenerates from `*.mli` files and `.gitignore` un-ignore lines. A hand-written `.ml` not un-ignored is silently dropped on next sync. Adding/removing an executable requires editing `sync_dune_modules.pl`, `extracted_code/dune`, and `.gitignore`.

**Sexp encoding** (`CrTypeIF.ml`): `net_edges` is hand-written as an explicit edge list (derived converters would stub as `<fun>`). `positive`/`nat`/`Z` emit decimal and accept decimal or Coq encoding. `sc_pattern` (`list bool`) uses derived converters — plain `Coq_cons` chain, NOT `0b` literals (that sugar was removed in `1a04afc`). Pattern is **MSB-first** (`bits_to_Z` folds head as high bit); front-ends build the chain from the LSB out.

**`run_net`**: runs a program concretely. One-shot: `run_net <prog.ir> [<region>:<off>:<width>:<val> ...]`. `--serve` mode: co-process for external tests (used by `translation/ect/tests/irrunner.py`). Not part of `EqCheck`.

**`fuzz_tss`**: priorities must be DISTINCT in 1..254 (255 = "no match" sentinel). Filters are generated around a witness packet — do not change to independent draws (the `--mutate` expect test measures this). Do not delete the `--prec` test (coverage number, not a verdict).

**`dump_sexp`**: three subcommands: `--pkt [idx]`, `--parser [idx]`, `--modprog NAME`.

**Adding a module test program**: two steps — add to `mod_test_program_list` in `TestModulePrograms.v`; look up with `Shim.find_modprog "name"`. Do not mirror the name→key encoding in OCaml.

**`string_to_pos` is NOT the inverse of `pos_to_string`** — do not round-trip.

**`Local Open Scope string_scope.`** is required around any Rocq list of string literals.

**Memo tables**: compiler tables (`memo_cb`/`memo_ca`/`memo_cm`) must NOT be reset per call — they hold `SmtExpr` terms that belong to no Z3 context. Lowering tables (`memo_bool`/`memo_arith`/`memo_arr`) MUST be reset per call (`reset_lowering_memo ()` at top of `solve`) — Z3 expressions belong to the context they were built in. A new expression sort needs a new lowering table + a line in the reset. `reset_lowering_memo` also clears `undeclared_arr`.

**No `side_constraints` list** — both former constraints are now inside the query (`SmtCompile.regions_wf` for region byte-ness; tag/value coercion inside `compile_arith`'s `SmtArithVar` case). Do not add one back.

**`SmtArrInit` must be memoised** — `mk_fresh_const` is generative; a memo miss produces two unequal Z3 terms that must be one. The "witness: two undeclared regions agree" test catches this.

**Every DAG walk must use physical-identity memo tables** — structural `Hashtbl` blows up (hash collision → walks as tree). `collect_arr_lens` also needs a visited set.

**Both-reject is "equivalent"** — `check_sym_pkt_out` accepts when both runs reject. Catch with concrete-output tests (`TestModuleSemantics`), not just verdicts.

**Rejection is a STATE, not `None`** — `run_parser_concrete`/`eval_network_from_concrete` return `None` only on non-termination, not on rejection. A rejected run keeps running and returns `Some` with `gps_valid = false`. Do not add a short-circuit.

**`check_sym_region_equal` emits ONE `SmtArrEq`**, not a cell-by-cell conjunction. The Z3 lowering emits `mk_eq`, which is correct only because both arrays are rooted at the same `SmtArrVar` (`eval_general_program_symbolic_mem_rooted`) and every `SmtArrSt` is guarded in bounds.

**`gps_valid` must be exact** — over- or under-approximation is unsound due to the both-reject disjunct. `eval_deparser_concrete` is total for this reason.

**Match semantics**: first-match, type-first. `CrVal.eqb`/`ltb` compare `CrIntType` before value; both are false on `UninitVal`.

**Read tape concretizes through `present_bits`; write tape positionally** — the asymmetry is forced. Do not merge these paths. `ParserCommuteLemmas.pprefix` is the invariant.

**Three symbolic parser invariants** (do not change):
- `select_bits_valid` measures from the CURSOR, not the peeked window.
- `merge_header_maps` folds over BOTH key sets.
- `run_target_symbolic` is a top-level definition, not a local `let`.

## The core fragment

`Z3Solver.ml` does not know `CrVal`. `solve` runs `SmtCompile.compile_bool` first, rewriting to the core fragment (every arith term denotes `IntVal _ u64`, every node has one Z3 counterpart). **A lowering case picks one Z3 constructor and passes children down** — any case building an `ite`, mask, or comparison belongs in `SmtCompile.v`. Three exceptions with comments: `SmtArrEq`, `SmtBitDiv`, `SmtBitSlice`.

**A non-core constructor reaching the lowering raises** (`SmtArithVar`, `SmtCast`, `SmtUninit`, `SmtArrSt`).

**A new `SmtArithExpr` constructor needs a `compile_arith` case, not a lowering case.**

**Do not inline the `cstep_*`/`lcstep_*` split back to direct `compile_bool` calls** — a structural fixpoint over a DAG visits shared subterms once per PATH.

**`compile_correct` is `Qed`** with no axioms. Two invariants a change to `SmtCompile.v` must preserve:
- The `reps` induction carries tag ∈ 0..5 (not just any word).
- `SmtCellVal`/`SmtCellTag`/`SmtStCell` carry an `is_int_tag` guard on their index.

**`solve` checks `lcb` and refuses a query that fails it** (guards the `smt_arr_len` = `arr_len` agreement hypothesis).

**`SmtArrSel`'s bounds guard lives in `SmtCompile.v`** (`compile_arith` wraps in `SmtConditional`); the lowering emits a bare `select`. Regression: "an out-of-bounds read is ErrorVal, not a cell".

## Memory

`LoadOp`/`StoreOp` name a `MemRegion` statically; offset is a runtime `Operand`. No pointer values. Regions declared with lengths in bytes on `GeneralCaracaraProgramDef`.

**Region entry contents are bytes on all three sides**: `eval_smt_mem` uses `CrVal.to_byte`; `Z3Solver.ml` pins cells 0..len to u8 tag, value ≤ 255; `init_concrete_mem` uses `mk_region_zero`. These must move together — loosening one side makes a soundness theorem false.

**Width-`ty` access covers `it_bytes ty` consecutive cells, little-endian.** `ld_val`/`st_val` decompose; `ld_arr`/`st_arr` are single-cell. Symbolic mirrors: `smt_ld_val`/`smt_st_val` mirror node-for-node.

**A store is not atomic** — out-of-bounds cells are dropped, in-bounds cells are written.

**Memory lives on `GeneralProgramState`** (`sh_mem`, `sh_mem_extent`), not `TransformerState`. Threaded through transformers as `MemCtx`.

**Every evaluator exists twice** — `eval_transformer_concrete_mem` (threads memory, used by network) and `eval_transformer_concrete` (memory-free, domain of `CaracaraProgram`). Do not delete the memory-free pair: it is the only evaluator whose soundness is stated over concrete execution.

**Out-of-bounds access yields `ErrorVal`/is dropped and records the overrun in `sh_mem_extent`; rejection happens at the sink.** `sh_mem_extent` = one past highest offset touched per region. Undeclared region default = 0, so any access is an overrun.

**`sh_mem_extent` is NOT an equivalence criterion** — it was removed because it rejected dead-load elimination, load hoisting, and speculation. Regression: "mem: a dead load is not observable" expects `Equivalent`.

**Memory ops are barred from `ParRule`** (`CrDslProperties.no_mem_ops_in_parb`).

## Proof status

- Both checkers are **`Qed`**. They relate the verdict to `concretize_sym_modnet_state` of SYMBOLIC final states (solver-to-symbolic gap, not symbolic-to-concrete). See `SOUNDNESS.md`.
- Symbolic-to-concrete commutation exists at every level: `ConcreteToSymbolicLemmas.v`, `MemCommuteLemmas.v`, `DeparserCommuteLemmas.v`, `ParserCommuteLemmas.v`, `NetworkCommuteLemmas.v`. **No admits.** `Print Assumptions` shows one solver axiom only.
- `eval_general_program_commute` is stated for `init_general_symbolic_state` only — not arbitrary `s`. Do not generalise.
- `InitReachable.valid_iff_reachable` is `Qed`. Validity is defined as the image of the concrete initializer. `valid_is_reachable_pair` is the form the checker needs.
- Seeded names are built in one place: `CrVarLike.seed_name` over `SeedVar`. Add a seeded name by adding a `SeedVar` constructor, not by string concatenation.
- `gps_agree` is POINTWISE, not record equality — do not "simplify" to `=`. `sh_mem_extent` trees differ between symbolic and concrete runs.
- Solver axiomatised in `SmtQuery.v`: `smt_query_sound_some`/`smt_query_sound_none`. `SmtModuleQuery.v` ends with `Print Assumptions` calls that print during `make`.
- `smt_arr_len` is syntactic only (not part of Coq semantics). Its `SmtArrIte` case reads one branch — sound only because both branches are rooted at the same region.
- **Linear chain only** (`is_linear_chain` = `is_dag ∧ single_sink ∧ no_fan_out ∧ no_fan_in`). Fan-out DAGs are not faithfully modelled.
- **A write to a key not already in the map is DROPPED symbolically.** Two seeds close this: headers via `collect_write_headers`, transformer state via `force_keys` over `collect_module_state_targets`. `force_keys` must not set the default.
- **Initial header map seeded with the whole network header interface** (`collect_write_headers`). Do not simplify to `PMap.init`.
- Header seeding: extracted headers get `SmtCast u64 ty (SmtVarVal "hdr_<h>")`/`mk_int ty 0`; transformer-only headers get `SmtUninit`/`UninitVal`. Split by `collect_header_types`. Names are UNPREFIXED (both programs share one variable per header).
- Arith expressions compile to `(value, tag)` pairs in `SmtCompile.v`. Tag encoding: 0=ErrorVal, 1=UninitVal, 2..5=W8/W16/W32/W64. `regions_wf` pins array cells to u8 tag — do not normalise inside `SmtArrSel` instead.
- `TestEquality.ml`'s `witness:` tests are the guard on the lowering and `solve` plumbing. Add one when adding an expression form.

Update `SOUNDNESS.md` alongside any proof work.
