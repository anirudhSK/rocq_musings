### 1.1. Prove `modnet_equivalence_checker_sound` over concrete execution

The checker's soundness now comes in two halves, deliberately kept apart so the
remaining work is one named lemma rather than a reopened proof:

- `modnet_equivalence_checker_sound_symbolic` — **proved**, `Qed`, assumes only
  `smt_query` + `smt_query_sound_none`. Relates the verdict to
  `concretize_sym_modnet_state` of the two SYMBOLIC final states. This is the
  solver-to-symbolic gap.
- `eval_general_program_commute` — **admitted**. The symbolic-to-concrete gap.
- `modnet_equivalence_checker_sound` — **proved from those two** (~35 lines).

So `Print Assumptions modnet_equivalence_checker_sound` reports exactly three
things, and the only one that is not a deliberate trust assumption is the bridge.

**The bridge is a relation, not an equality, and that is not laziness:**

```coq
gps_valid c_f = gps_valid (concretize_sym_modnet_state s_f f) /\
(gps_valid c_f = true -> c_f = concretize_sym_modnet_state s_f f)
```

On a rejecting run the two evaluators genuinely disagree about headers,
`sh_bits_read` and the residual while agreeing on the verdict. The concrete side
stops at the failed bounds check; the symbolic side keeps going structurally and
records the failure in `pr_accept`. The conclusion is a disjunction on validity
and its first branch compares nothing but the flag, so verdict agreement is
exactly enough. Do not try to strengthen this to a plain equality.

**The second half is weakened too, for a different reason.** It used to say
`c_f = concretize_sym_modnet_state s_f f`, an equality of
`GeneralConcreteState` records, and that is false on the memory maps for a
`PMap` representation reason rather than a semantic one. It now concludes
`gps_agree`, which compares those two maps pointwise; item 5 has the
counterexample.

#### What the bridge needs, in dependency order

1. **Deparser commutation — DONE.** `DeparserCommuteLemmas.eval_deparser_commute`,
   `Closed under the global context`. It went through easily because the deparser
   is built on the `slice_val`/`SmtBitSlice` correspondence that `eval_smt_arith`
   already establishes node for node, rather than on its own bit extraction. Keep
   that pattern.
2. **Bitstream groundwork — DONE** (`ParserCommuteLemmas.v`). See 1.1.1.
3. **Transformer commutation with memory threaded — DONE**
   (`MemCommuteLemmas.v`, all `Closed under the global context`). Five levels:

   - **Value / memory context.** `concretize_mem_ctx`, then
     `smt_ld_val_commute`, `smt_st_val_commute`, `bump_extent_commute`,
     `bump_extent_span_commute`, `concretize_mem_ctx_store`. This is exactly
     what 1.4 step 2 asks for. `CrVal.ld_val`/`st_val` and their `smt_*`
     mirrors were written node for node so this would go through; until now
     that mirroring was a convention held up by comments, with nothing forcing
     the two sides to agree. It is a theorem now.
   - **One op.** `eval_hdr_op_assign_mem_commute`, all seven `HdrOp`
     constructors including `LoadOp`/`StatefulLoadOp`/`StoreOp`.
   - **An op list.** `eval_hdr_op_list_mem_commute`, by induction.
   - **A match-action rule.** `ma_rule_commute_mem` / `_extent` / `_hdr` /
     `_sv`, through the seq and par cases.
   - **A transformer.** `transformer_commute_mem` / `_extent` / `_hdr` /
     `_sv` / `_ctrl`.

   **The op level needed no new header-map machinery**, contrary to the
   expectation recorded here earlier. `HelperLemmas.commute_lookup_eval` (for
   operands) and `ConcreteToSymbolicLemmas.commute_update_eval_varlike` (for
   the write back) are both *unconditional*; the `is_varlike_in_ps` side
   conditions belong to the rule and transformer levels, not below them.

   **The first three levels state whole memory contexts, the last two state
   one key at a time**, and the break is forced: `concretize_mem_ctx` is
   `PMap.map`, which commutes with the `PMap.set`s an op performs, but a merge
   rebuilds the map by folding `PMap.set` over an explicit key list and so
   leaves every other key reading the map's *default*. That is also the
   granularity `ConcreteToSymbolicLemmas` already uses for headers and state
   variables. Lifting per-key results to whole-state equality is item 5's job,
   once, at the module level — not four times here.

   **The memory-free lemmas do not carry over to the rule and transformer
   levels**, which is why those are restated rather than applied. The merge
   shape is identical but what is being merged is not: `eval_hdr_op_list_smt`
   sends a load to `smt_error` where `eval_hdr_op_list_smt_mem` sends it to
   `smt_ld_val` of the region, so the two build different terms for any action
   that touches memory. What *is* shared is the argument around them.

   Four supporting notes for whoever works nearby:

   - Rewriting `eval_smt_arith` one NODE at a time is necessary, not
     fastidious: `cbn`/`simpl` reduces the whole term including
     `SmtArithConst` leaves, and once a constant has become
     `mk_int u64 (unsigned (mask_width W64 z))` the `eval_const_mask_u64`
     rewrite no longer matches. `MemCommuteLemmas` opens with a block of
     one-node equations (`eval_bitadd`, `eval_cast_node`, …) for this.
   - The `*_mem` list folds destructure their accumulator with a `let`, so an
     induction needs cons equations first (`hdr_op_list_smt_mem_cons` and its
     concrete twin) or the accumulator is not syntactically a pair after one
     step and the IH will not apply.
   - **A merge is only correct at the keys it does not enumerate because the
     defaults agree there**, which is a fact about the branch, not about the
     merge: memory is only ever written with `PMap.set`, which leaves the
     default alone (`eval_hdr_op_list_smt_mem_default`,
     `ma_rule_smt_mem_default`). Widen the key list or add a write that
     replaces a whole map and this is the obligation that breaks.
   - Stating the switch lemmas with the `option` `find_first_match` returns on
     the right — rather than as `ConcreteToSymbolicLemmas`' separate
     some-match and no-match lemmas — is what makes the induction step
     uniform: the recursive call is the same lemma at the tail, not a
     different one depending on how the search turned out. It roughly halves
     these proofs.
4. **Parser commutation — DONE** (`ParserCommuteLemmas.v`, all
   `Closed under the global context`). `run_parser_commute` and
   `eval_parser_commute`.

   The conclusion is a RELATION, not an equality, and at the parser level for
   the same reason it is one at the top: the two runs see packets of different
   lengths. The concrete one reads `present_bits (p_packet ps) f`, a prefix of
   the symbolic packet and strictly shorter wherever a merge left padding, so
   the symbolic bounds check can pass where the concrete one fails. When it
   does, the symbolic run reads padding and carries on down a path the concrete
   run does not have — it still rejects, because `slice_valid` conjoins the
   presence of everything consumed into the guard, but its headers, residual
   and `pr_bits_read` are whatever that phantom path produced.

   The loop invariant that makes this work is **`p_cursor <= k`**, where `k` is
   the length of the present prefix. It holds because every step in lockstep
   has passed the concrete bounds check. Everything else follows from it:
   in-prefix reads agree bit for bit, and an out-of-prefix read always contains
   position `k`, which is absent, so the guard goes false.

   Three supporting pieces that did not exist and had to be built:

   - `run_parser_concrete_fuel_mono`. Each evaluator sizes its fuel from the
     packet it was handed, so the two runs do not start with the same budget.
     `ParserTerminationLemmas` proves fuel is *adequate*, which is a different
     statement.
   - `CrVal.cast_u64_mk_int` (and `mask_width_unsigned_mask_W64` under it).
     The comment on `apply_extract_symbolic` asserts that
     `SmtCast u64 of (SmtBitsToInt ...)` denotes `mk_int of (bits_to_Z ...)`.
     Nothing backed it. It is a theorem now.
   - `run_target_symbolic`, factored out of `run_parser_symbolic`'s local
     `let`. A nameless let-bound lambda cannot appear in a lemma statement,
     and the proof needs to say "this step accepts nothing when the guard is
     false" about exactly that term.

   **Two real divergences between the two semantics turned up here**, both
   fixed rather than hypothesised around. See 1.1.2.
5. **Network fold induction** over `eval_network_from_*`. The one piece still
   open. Everything it has to assemble is now proved:
   `MemCommuteLemmas.transformer_commute_*`,
   `DeparserCommuteLemmas.eval_deparser_commute`, and item 4's
   `eval_parser_commute`.

   **The bridge's conclusion has been corrected** and the statement in
   `SmtModuleQuery.v` is the one to prove:

   ```coq
   (gps_valid c_f = true -> gps_agree c_f (concretize_sym_modnet_state s_f f))
   ```

   `gps_agree` is structural equality on every field except the two memory
   maps, which are compared pointwise. That exception is forced, and for a
   `PMap` representation reason rather than a semantic one: `sh_mem_extent`
   starts as `PMap.init` — an empty tree — and every access adds a key, so a
   transformer whose rule 1 touches region A and rule 2 touches region B leaves
   the concrete map bound at whichever rule ran and the symbolic map bound at
   both, `eval_transformer_smt_mem` folding over every branch's keys. `PMap.map`
   preserves trees, so the records differ while `!!` agrees everywhere — the
   surplus bindings all hold the map's own default. Only the extent map
   demonstrably needs it; `sh_mem` is weakened alongside so the bridge does not
   have to smuggle in the argument that an undeclared region is an overrun.

   It costs nothing: `modnet_equivalence_checker_sound` never compares maps, and
   its proof now transports each conjunct through `gps_agree` instead of
   rewriting one state equality — done, `Qed`, same three assumptions as before.

   **So the per-key-to-whole-state question this item used to pose is settled:
   do not lift.** `MemCommuteLemmas` and the memory-free development stop at
   per-key statements because per-key is all that is true above a merge;
   carrying `PTree.extensionality` up to whole-map equality would be proving
   something false.

   Two prerequisites turned up on starting it. The first is done; the second
   is a design fork worth deciding before writing any more.

   **Done — the concrete evaluators are congruences for pointwise memory
   agreement** (`MemCommuteLemmas.v` §6, up to
   `eval_transformer_concrete_mem_cong`). This is forced by the weakening
   above and the plan did not anticipate it: after one module the concrete
   memory is no longer literally `PMap.map` of the symbolic one, only equal at
   every key, so the induction cannot take a second step unless the concrete
   evaluator is blind to the difference. It is, because memory is only ever
   touched through `!!` and `PMap.set` — nothing reads the key set. The one
   exception is `mem_extents_in_bounds_concrete`, which folds over
   `pmap_keys`; it is only used once, at the very end, and needs its own
   argument (extra keys hold the default `0`, and `negb (ltb len 0)` is
   `true`, so they cannot change the `forallb`).

   **Open — how to compare a transformer's MODULE state.** `gps_agree` asks
   for `mod_states c1 = mod_states c2`, and for a transformer that means the
   three `TransformerState` maps have to be equal, not just pointwise equal.
   They are not, for the same representation reason as the memory maps: the
   concrete side writes with `update_varlike` (`PMap.set`, which adds keys)
   and the symbolic side with `update_all_varlike`, which rebuilds from the
   keys already present and so can never add one. Two routes, and both need
   the domain invariant below:

   - **Whole-state equality.** Needs the key sets to match, i.e. that
     `update_all_varlike` preserves the domain. Not derivable from the
     `CrVarLike` class — `update_all_varlike` is an abstract *field* with no
     body — so it has to be proved once per instance. All three are
     `new_pmap_from_old`, i.e. `PTree.map`, so each proof is short.
   - **Extensional `ts_agree`**, mirroring what `gps_agree` already does for
     memory, plus congruence of the concrete transformer in its state
     argument. Also per-instance, but most of the pieces exist:
     `PMapHelperLemmas.lookup_varlike_*_PMap_concrete` and
     `lookup_update_*_*`, and the file notes that cross-type updates are
     definitional.

   **Take the second.** It is uniform with how `gps_agree` already treats
   memory, it reuses lemmas that are already there, and it does not require
   adding fields to a class that three instances and ~840 lines of `SmtQuery`
   proofs depend on.

   **The domain invariant** either route needs: *every key a module writes is
   already present in its maps*. It holds by construction — headers by
   `init_general_symbolic_state` seeding `sh_hdr_map` with
   `collect_write_headers`, state variables by `force_keys` over
   `collect_module_state_targets` (see 1.1.3) — but it has to be threaded
   through the network recursion explicitly, the way
   `ParserCommuteLemmas` threads `pprefix`.

   Then the induction itself:

   - It is **relational**, over two runs at once, not an invariant over one, so
     `fold_left_opt_inv` will not carry it — that lemma is invariant-shaped.
     `no_fan_out` (from `is_linear_chain`) gives
     `|downstream_modules net m| <= 1`, so the fold over downstream modules is
     at most one step; prove a destructuring lemma under that hypothesis rather
     than a relational analogue of the fold.
   - A module-level lemma per kind, dispatching to the three commutation
     results above. The `_ , _ =>` kind-mismatch fallback needs no work:
     `concretize_sym_module_state` preserves the constructor, so both semantics
     take the same branch.
   - The last node-level correspondence,
     `mem_extents_in_bounds_concrete rs (PMap.map (fun e => eval_smt_arith e f) ext)
     = eval_smt_bool (mem_extents_in_bounds_smt rs ext) f`. The two are exact
     mirrors by construction — same `forallb`/`fold_right` over the same
     `pmap_keys`, `negb (CrVal.ltb …)` against `SmtBoolNot (SmtBoolLt …)`, same
     u64 bound — so this is a fold correspondence, not new theory.
   - Two hypotheses the bridge will have to gain:
     `well_formed_general_program p` (for `eval_parser_commute`'s totality) and
     `is_linear_chain p` (for the fold). Both are already hypotheses of
     `modnet_equivalence_checker_sound`, so its proof only has to pass them
     through. Note this finally gives those two hypotheses a use — SOUNDNESS.md
     records that neither direction currently needs them.

   One thing to check rather than assume when writing it: `gps_agree` keeps
   **structural** equality on `sh_hdr_map` and `mod_states`, which holds only
   because `init_general_symbolic_state` seeds the header map with
   `collect_write_headers`. A parser's merged header map is a union over
   branches, so without the seeding a header written on one branch alone would
   be a key on the symbolic side only. If the induction turns up a case where
   that is not enough, those two fields weaken the same way the memory maps
   did — but do not weaken them pre-emptively.

#### 1.1.1. Presence and the read tape

`concretize_sym_modnet_state` concretizes read tapes through `present_bits`
(keep the positions whose `cvc` holds under `f`) and write tapes positionally.
That asymmetry is forced, in both directions:

- **Read tapes must filter.** `merge_bitstream` pads the shorter branch to the
  longer one with `cvc` false. Concretized positionally, those padding positions
  become ordinary present bits, and a chained parser downstream reads them as
  real data and ACCEPTS where the symbolic run rejects. That is a wrong verdict,
  not merely an unprovable lemma.
- **Write tapes must not.** `wt_unconditional` says every emitted bit carries
  `cvc := SmtTrue`, and `sym_out_equal_sound` — which the proved half runs on —
  compares them positionally.

The cost of filtering is that the concrete packet is SHORTER than the symbolic
one wherever padding was dropped, so the two bounds checks can disagree. Only in
the harmless direction (symbolic passes and extracts garbage, then the absent
`cvc` kills the guard; concrete fails the check and rejects — both reach
`accept = false`), which is precisely why the bridge is a relation.

For the parser proof to be tractable the dropped positions have to be a SUFFIX,
so that the concrete packet is a prefix of the positional concretization rather
than a compaction of scattered survivors. That is the presence-prefix invariant
— the read-tape analogue of `wt_unconditional`.

**Done**, in `ParserCommuteLemmas.v`, all `Closed under the global context`:

- `present_bits` algebra (`_nil`, `_cons`, `_app`, `_absent`, `_map_ext`) and
  `smt_bool_ite_eval`.
- `merge_bitstream_present_true` / `_false` — a merged residual's present bits
  are exactly the SELECTED branch's. **Needs no invariant at all**: the padding
  is absent under the selecting valuation wherever it lands, so `List.filter`
  removes it regardless of shape. This is the bitstream half of "a merged
  result concretizes to the branch the valuation picks", and is reusable
  directly in the parser merge argument.
- `pprefix` — the invariant, stated INDUCTIVELY rather than as
  `exists k, firstn k present /\ skipn k absent`. Every preservation proof is
  an induction over a bitstream and the inductive form is what they can
  consume; `pprefix_split` recovers the witness form when a proof wants it.
- `pprefix_present_bits_is_prefix` — the payoff:
  `present_bits l f = firstn k (map (eval o cvv) l)`.
- Preservation, one lemma per way a bitstream is built:
  `pprefix_symbolic_input_bits` (base case — a source parser's packet is
  all-present), `pprefix_skipn` (each parser hands on a `skipn` of what it
  had), `pprefix_merge_true` / `pprefix_merge_false` (each `select` merges).
  Both merge directions are needed and they are not symmetric:
  `resolve_select_symbolic` puts the case condition in the THEN position and
  the remaining cases in the else, so a valuation falling through to the
  default takes the false branch once per case.
- Threaded through a parser run: `apply_extract_symbolic_packet` (an action
  moves the cursor and writes a header, never touching the packet),
  `pprefix_merge_results`, `pprefix_resolve_select`,
  `pprefix_run_parser_symbolic` (induction on fuel), and
  `pprefix_eval_parser_symbolic`.
- Threaded through the network (`SmtModuleQuery.v`, alongside the
  `wt_unconditional` development it mirrors):
  `module_update_gs_symbolic_pprefix` — only the parser case has content,
  since a transformer and a deparser leave `sh_read_tape` alone —
  `eval_network_from_symbolic_pprefix` (via the existing `fold_left_opt_inv`),
  and `eval_general_program_symbolic_pprefix`.

So: **every read tape reachable in a symbolic run has its absent positions as
a suffix, under every valuation.** That is the invariant the parser
commutation proof will consume, and it is now available as a single named
theorem rather than something to re-derive inside that proof.

#### 1.1.2. Two divergences the parser proof found

Both were fixed in the semantics rather than assumed away, and both are the
kind that is invisible until something relates the two evaluators.

- **A zero-width `Peek` past the present prefix accepted symbolically and
  rejected concretely.** `select_bits_available_concrete` asks whether the
  packet reaches `cursor + off + width`; `select_bits_valid` was conjoining the
  presence of the peeked *window* `[cursor + off, cursor + off + width)`, which
  for `width = 0` is empty and so contributes `SmtTrue` however short the
  packet is. A chained parser whose residual ended before `cursor + off` would
  then reject concretely and accept symbolically. `select_bits_valid` now
  measures from the **cursor**: `[cursor, cursor + off + width)`. Given the
  cursor is itself inside the present prefix — which the loop invariant above
  guarantees — that range being all present is *exactly* "the prefix reaches
  `cursor + off + width`", so the two checks now say the same thing.
- **`merge_header_maps` dropped a header written only on the else branch.**
  It took its keys from `m_then` alone, justified by "the two maps share the
  same header domain in practice" — true only because
  `init_general_symbolic_state` seeds the header map with the whole network's
  interface. Where that seeding does not apply (`SmtParserQuery`, the parser
  test programs), a header extracted only on the else side of a `select` was
  not a key of `m_then` and read back the map's default on that path. Same
  failure mode as SOUNDNESS.md model-debt item 2. It now folds over the union
  of both key sets, the shape `merge_mem_ctx_smt` already uses, which leaves
  only the much weaker obligation that the two maps carry the same default.

#### 1.1.3. A third divergence: state variables

`update_all_varlike` rebuilds a map from the keys already in it, so it cannot
introduce one. SOUNDNESS.md model-debt item 2 records this for headers, where
it made the network checker compare two empty outputs and answer `Equivalent`,
and the fix was to seed `sh_hdr_map` with `collect_write_headers`.

**The same hole was still open for a transformer's state variables.**
`init_general_symbolic_state` seeds `t_state_map` from the module's *declared*
`states` list, and nothing requires a rule's targets to be among them —
`well_formed_module` asks for `list_norepet`, `Sorted`,
`transformer_has_default` and `no_mem_ops_in_par`, and says nothing about
containment. A write to an undeclared state variable therefore survived
concretely (`update_varlike` is `PMap.set`) and vanished symbolically.

Fixed by `CrVarLike.force_keys` over `collect_module_state_targets`, which
re-sets each written target to the value it already reads. `PMap.gsident`
makes that the identity extensionally — it changes only which keys have an
explicit binding, which is exactly what `update_all_varlike` looks at. It
cannot simply set the default the way the header seed does: a declared state
variable's entry is a free `SmtArithVar` standing for its value on entry, and
overwriting it would erase an input.

Nothing observable changed (`dune runtest` is unmoved), which is the point —
it was latent, and it is the third instance of the same family after the two
in 1.1.2.

#### 1.1.4. Free scalars are still loose, deliberately

The region fix (SOUNDNESS.md model-debt item 3) pinned a region's entry cells to
bytes. The free SCALARS were left alone, and that is a decision rather than an
oversight:

- `eval_smt_arith`'s `SmtArithVar` arm coerces every non-`IntVal` to `ErrorVal`,
  and the lowering mirrors it with `ite (tag_is_int t) t tag_err`, so a free
  scalar can still be `ErrorVal` — and its WIDTH is model-chosen too, which is
  the same false-positive shape one level down (a comparison at `u64` against a
  variable the model made `u8` is false in both directions).
- It does not bite the way the region one did, because at network level the free
  scalars are a transformer's state and ctrl variables, and `check_sym_pkt_out`
  never compares those. They are also PREFIXED per program (`p1`/`p2`), unlike
  memory and packet bits, which are deliberately shared — so two programs whose
  output depends on a state variable already fail to be equivalent for a reason
  that has nothing to do with tags. That is a separate modelling gap.
- Fixing it properly needs a width for `State` and `Ctrl`, which the DSL does not
  declare. Pinning them to `u64` would be a modelling commitment, not a bug fix.

Regression test for the current state of affairs: `TestEquality`'s
"witness: a scalar the model leaves non-integer", which is still SAT and says so.

### 1.2 eBPF
Example workloads:
https://github.com/iovisor/bcc/tree/master/libbpf-tools
https://github.com/dslab-epfl/ebpf-se
https://github.com/libbpf/libbpf-bootstrap
https://github.com/Orange-OpenSource/bmc-cache/blob/main/bmc/bmc_kern.c
https://github.com/eunomia-bpf/KEN/tree/main/dataset/libbpf
https://github.com/cache-ext/cache_ext
https://github.com/OISF/suricata/tree/main/ebpf

### 1.3. Type-set-directed tag lowering (performance)

`Z3Solver.ml` lowers every `SmtArithExpr` to a `(value, tag)` pair, where the tag is
3 bits distinguishing `ErrorVal`, `UninitVal`, and `IntVal` at each of the four widths.
That encoding is what makes `smt_query_sound_some` true for the real solver (see
`SOUNDNESS.md` model debt item 4) and it is not optional — but it currently pays for
generality that is almost never used.

Measured on a 766-instruction `-O0` vs `-O2` pair (ablating the tag reasoning from the
lowering, which is unsound but fine as a stopwatch):

    tags on   ~2.5 s
    tags off  ~0.6 s

so roughly 3x, i.e. most of the solve. On the 40-instruction `bpf_ref` pair it is 0.02s
either way — this is a scaling problem, not a present one. It becomes the wall once
programs reach a few hundred instructions, which the `-O0` lowering of a modest C
function easily does.

The headroom: abstract each arith node by the SET of `CrVal`s it can denote (four int
types plus Uninit and Error) and size the tag to the set. Measured distribution over the
same query:

    type-set size 1 (monomorphic)   42%      -- tag is a compile-time constant
    type-set size 2                 40%      -- one bit suffices
    type-set size 3                 18%
    type-set size 6                 0.3%

and 81% of all `SmtBoolEq`/`SmtBoolLt` nodes have BOTH operands confined to at most two
types, so `tag_is_int` (a two-sided range check today) collapses to a single bit test.

The attraction is that this is **purely a lowering specialisation**: same formula, so no
Coq changes, no proof changes, and no new trust assumption. It lives entirely in
`Z3Solver.ml`.

Caveats before starting:

- The histogram bounds how much tag machinery could be removed. It does not predict the
  speedup, which nobody has measured.
- The monomorphic 42% is mostly constants and their immediate consumers, which are cheap
  already. The expensive nodes -- the deep `SmtConditional` chains -- are the 2-element
  ones, so the realistic win is the 3-bit-to-1-bit narrowing rather than elimination.
- The abstraction has to be sound in the same direction the encoding is: over-approximate
  the type set, never under-approximate it. A node wrongly typed as monomorphic would emit
  a constant tag where the semantics admits `ErrorVal`, which is exactly the class of bug
  the tags were introduced to fix.

### 1.4. Collapse the duplicate evaluators

Every transformer evaluator exists twice: a memory-threading recursion
(`eval_*_concrete_mem` / `eval_*_smt_mem`) and a memory-free one
(`eval_*_concrete` / `eval_*_smt`). The memory-free pair is the domain of
`CaracaraProgram` and of `SmtQuery.equivalence_checker_cr_dsl`, whose ~840 lines
are all `Qed` and whose soundness is the only result in the project stated over
**concrete execution** rather than over concretized symbolic states — so it is
not dead weight and must not simply be deleted.

**Step 1 — one recursion (no new theory). CONCRETE SIDE DONE; SYMBOLIC REMAINS.**
Redefine the memory-free evaluators as the threading ones run on an empty
context:

```coq
Definition eval_transformer_concrete t ps :=
  snd (eval_transformer_concrete_mem t empty_concrete_mem_ctx ps).
```

Done for the concrete side: `eval_hdr_op_assign_concrete` and the four
evaluators above it are now `snd (..._mem ... empty_concrete_mem_ctx ...)`, with
`..._eq` lemmas standing in for what `unfold` used to give, and the ~21 affected
proof sites in `ConcreteTransformerLemmas.v`, `ConcreteToSymbolicLemmas.v` and
`CtrlPlaneInvariants.v` rewritten to use them. `SmtQuery.v` needed no changes,
as predicted. Still zero admits.

What remains is the SYMBOLIC pair. It needs one thing the concrete side did not:
memory-free `LoadOp` emits `smt_error`, whereas the wrapper emits
`smt_ld_val ty SmtArrInit o`. Those are different expressions with the same
denotation, so `eval_hdr_op_assign_smt_eq` cannot be stated in the old form, and
`commute_sym_conc_assign` needs a lemma `eval_smt_arith (smt_ld_val ty SmtArrInit o) f
= ErrorVal` — the mirror of `CrVal.ld_val_unalloc`. Six `unfold` sites.

Groundwork already in the tree:

- `CrVal.ld_val_unalloc` / `st_val_unalloc` — an undeclared region reads
  `ErrorVal` and swallows writes, at every width. These are what make the
  equality hold; note it is *provable*, not definitional, because
  `List.seq 0 (it_bytes ty)` cannot reduce for a variable `ty`.
- `NoMemLemmas.v` — the reverse reduction, for transformers with no memory ops.
  Unused today; it is the escape hatch if a lemma resists porting.

What is still needed:

- An invariant `mem_unallocated` (every region reads `Unallocated`), preserved by
  each op, since the fold's context does change as it goes — `bump_extent` writes
  the extent map even when the contents cannot change. The *state* result depends
  only on the contents, which is why the equality holds at all.
- The characterizing equations the old definitions gave definitionally (the
  per-constructor shape of `..._assign`, the cons step of `..._list`, and so on),
  proved once and then used by `rewrite` where proofs currently `unfold`.
- ~21 `unfold` sites across `ConcreteTransformerLemmas.v`,
  `ConcreteToSymbolicLemmas.v` and `CtrlPlaneInvariants.v`. `SmtQuery.v` does not
  unfold them at all — it goes through the commute lemmas — so it should need no
  changes.

One asymmetry to expect on the symbolic side: memory-free `LoadOp` emits
`smt_error`, whereas the wrapper emits `smt_ld_val ty SmtArrInit o`. Those are
different expressions with the same denotation, so any proof comparing
expressions structurally rather than through `eval_smt_*` needs adjusting.

**Step 2 — the complete dedup (multi-session, new theory).** Delete the
memory-free wrappers outright by restating `SmtQuery`'s development over the
threading evaluators. That needs the memory analogue of the commutation in
`ConcreteToSymbolicLemmas.v`: a `concretize_mem_ctx` relation and, on top of it,
`ld_val` commuting with `smt_ld_val` and `st_val` with `smt_st_val` (both folds
over `it_bytes ty` cells), plus the extents. The two were deliberately built as
node-for-node mirrors so this proof would go through.

That same construction is what would lift `modnet_equivalence_checker_sound` to
talk about concrete execution — i.e. unify the two checkers at the STRONGER
standard rather than the weaker one. Worth doing before adding memory to
`CaracaraProgram`, which without it only extends the syntax.

### 1.5. Nothing catches a race in a `ParRule`

`ParRule`'s action carries a subset type obliging its ops to write distinct
targets, and `CrDslProperties.no_mem_ops_in_parb` additionally rejects loads and
stores inside a `Par`. Neither is enforced, and the second is not even reachable:

- `no_mem_ops_in_parb` is only visible through `well_formed_general_programb`,
  whose only caller is `Shim.print_malformed_gprog` — which prints a warning and
  returns. `modnet_equivalence_checker` compares packet length and region
  declarations, never well-formedness. So a program with stores in a `Par` runs.
- The `NoDup` obligation *is* enforced by typing, but nothing says what it buys.
  There is no lemma that it makes evaluation order irrelevant.

Both are harmless today for one reason: **`Par` has no parallel semantics.**
`eval_par_rule_concrete_mem` is `eval_seq_rule_concrete_mem` with a `proj1_sig`,
and the symbolic pair matches, so a `Par` action is threaded strictly
sequentially. There is no reordering to be wrong about — the standing TODO at the
end of `CrConcreteSemanticsTransformer.v` ("a proof about sequential vs
parallel") is the gap.

A racy program is therefore expressible and silently accepted. Two ways to fix
it, in increasing order of value:

1. **Enforce the existing check.** Gate `modnet_equivalence_checker` on
   `well_formed_general_programb`, or have the OCaml entry points refuse rather
   than warn. Cheap, and makes today's comments true. Note this would also start
   rejecting parser-less networks: `wf_module_network` no longer requires the
   start module to be a parser (the predicate was deleted), but
   `end_modules_are_deparsers` still requires the sinks to be deparsers.
2. **Give `Par` a real parallel semantics and prove the obligations discharge
   it** — that evaluating an action under any permutation gives the same state.
   That is what turns `NoDup` from documentation into a theorem and gives it a
   call site, the treatment `smt_arr_len` got in
   `eval_general_program_symbolic_arr_len_agrees`.

With (2) in place, memory could be *allowed* in a `Par` under a disjointness
obligation rather than banned. `NoDup` over regions is sound but rejects two
stores at different literal offsets of one region; the honest decidable version
is a footprint `(region, offset, it_bytes ty)` compared pairwise, computable only
when the offset is `OpConst`, since `StoreOp` takes its offset as a runtime
`Operand`. Anything more permissive needs the solver, which moves a
well-formedness question into the trust bucket with `smt_query_sound_*`.
