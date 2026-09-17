### 1.1. Prove `modnet_equivalence_checker_sound` over concrete execution — **DONE**

There are no admits left in the project. The checker's soundness comes in two
halves, kept apart so each can be read on its own:

- `modnet_equivalence_checker_sound_symbolic` — **proved**, `Qed`, assumes only
  `smt_query` + `smt_query_sound_none`. Relates the verdict to
  `concretize_sym_modnet_state` of the two SYMBOLIC final states. This is the
  solver-to-symbolic gap.
- `eval_general_program_commute` — **proved**, `Qed`, axiom-free. The
  symbolic-to-concrete gap, closed. Stated for `init_general_symbolic_state`
  and carrying `well_formed_general_program` + `is_linear_chain`, which is
  forced: over an arbitrary symbolic state the statement is FALSE (see
  SOUNDNESS.md for the read-tape counterexample).
- `modnet_equivalence_checker_sound` — **proved from those two** (~35 lines).

So `Print Assumptions modnet_equivalence_checker_sound` reports exactly two
things, both deliberate trust assumptions: `smt_query` and
`smt_query_sound_none`.

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

   **Progress — `NetworkCommuteLemmas.v`**, all `Closed under the global
   context`. The scaffolding either side of the induction is done; the
   induction and two of the three module cases are not.

   - §1–2 **The last node-level correspondence is proved.**
     `mem_extents_in_bounds_commute`: the concrete `forallb` and the symbolic
     `fold_right` agree. Two things had to be said. `pmap_keys_map` — a
     concretized map enumerates the same keys, via
     `PTree.elements_canonical_order'` — which is what makes the one place
     either semantics looks at a key *set* correspond at all. And the two
     bracket their conjuncts in opposite orders (`forallb` conjoins head-first,
     the `fold_right` puts the accumulator on the left of each `SmtBoolAnd`),
     so the induction closes with `andb_comm` rather than by matching shapes.
   - §3 **The fold is not a fold.** `downstream_cases` turns `no_fan_out` into
     "no successor or exactly one", and `network_concrete_step` /
     `network_symbolic_step` are the one-step equations. So the induction can
     be an ordinary one on fuel.
   - §4 **Rejection is absorbing, on both sides**
     (`module_update_concrete_invalid`, `module_update_symbolic_invalid`).
     This is what makes the bridge's *first* conjunct survive the modules that
     run after a rejection, where the two states have genuinely diverged and no
     commutation lemma applies: neither semantics can clear the flag, so once
     both runs are invalid the flags agree for the rest of the network with
     nothing known about the states. Without it the invariant is not inductive
     — `eval_parser_commute` does not apply on the divergent path, so the
     accept flags cannot be shown to agree there, only to be jointly false.
   - §5 **The deparser module case** (`deparser_mod_commute`). It needed a
     congruence, and the reason is worth knowing: the packet a deparser is
     handed is the READ tape, which concretizes through `present_bits` — a
     filter — while `concretize_sym_module_state`'s `DeparserMod` branch maps
     positionally. **The two genuinely disagree about the incoming packet**,
     and the only thing that saves the case is that a deparser reads nothing
     but its header map (`eval_deparser_concrete_cong`).
   - §6 `inject_headers_commute`, so `MemCommuteLemmas`' transformer results —
     stated about `eval_sym_state ps f` — apply at the network level, where the
     state arrives already injected.
   - §7 **The design fork below is settled, the other way.** See there.
   - §8 **The memory-safety check survives the pointwise weakening.**
     `MemCommuteLemmas` §6 notes that `mem_extents_in_bounds_concrete` is the
     one exception to "the concrete side is blind to pointwise-vs-structural",
     because it folds over `pmap_keys`. `mem_extents_in_bounds_concrete_cong`
     is that exception discharged: a key present in one extent map and absent
     from the other reads the absent map's default, the default is
     `mk_int u64 0`, and nothing is `CrVal.ltb` below zero, so the surplus keys
     contribute `true`. Carries a hypothesis that both defaults are
     `mk_int u64 0` — one more conjunct for the induction's invariant, and one
     `PMap.set` preserves for free.
   - §9 **Step 9 is done: the program wrapper is proved.**
     `program_commute_from_network` takes the network-level outcome as
     hypotheses and delivers `eval_general_program_commute`'s conclusion: the
     start-module lookups agree because `PMap.map` preserves bindings, and the
     final flags agree because §8 bridges the extents check. It takes the
     network result as a HYPOTHESIS rather than naming an admitted lemma,
     deliberately — the induction's own hypotheses are not settled, and a
     guessed statement nobody has checked is worse than none.

   - §10–11 **Step 6 is done: `transformer_state_commute`.** The concrete
     transformer's output state IS the concretization of the symbolic one:

     ```coq
     Theorem transformer_state_commute : forall t mc ps f,
       transformer_dom_ok t (eval_sym_state ps f) ->
       snd (eval_transformer_concrete_mem t (concretize_mem_ctx mc f) (eval_sym_state ps f))
       = eval_sym_state (snd (eval_transformer_smt_mem t mc ps)) f.
     ```

     A whole-record equality, so it serves `gps_agree`'s `mod_states` clause
     AND `sh_hdr_map` (which is `module_header_map` of exactly this state) with
     no weakening anywhere. `pmap_ext` splits it into defaults, domains and
     per-key; per-key is `transformer_commute_hdr`/`_sv` for keys IN the
     domain, which is where `pmap_ext` needs them — outside it both sides read
     a default and the defaults agree.

     §10 is the missing half. Defaults are free (`PMap.set` never moves `fst`).
     Domains are not, and they hold exactly when every target the transformer
     writes is already in its maps: `op_dom_ok` says that per op, and it
     propagates through op → op list → match-action rule → transformer. One
     thing makes that induction work and is worth keeping: **`op_dom_ok`
     depends on the state only through its SHAPE**, so the hypothesis can be
     stated against the initial state rather than re-established after every
     op (`op_dom_ok_shape`).

   - §12–13 **Step 7 is done: `parser_mod_commute`.** It puts
     `eval_parser_commute`'s conclusion into the shape `module_update_gs_*`
     consumes, which means turning its POINTWISE header agreement into the
     whole-map equality `gps_agree` wants — the same gap step 6 had, in a
     different place, and §12 closes it the same way.

     Two things about the statement are load-bearing. **The accept flags agree
     UNCONDITIONALLY**; everything else is guarded by acceptance, because on a
     rejecting path the symbolic run has read padding and carried on down a
     path the concrete run does not have. And the shape argument needs the
     parser's own extract targets to be in the domain
     (`parser_extracts_ok`) — the parser analogue of `transformer_dom_ok`.

     §12 proves both parsers preserve the header map's shape. The concrete one
     is an ordinary fuel induction. The symbolic one has a wrinkle the concrete
     one does not: `merge_header_maps` folds over the union of BOTH branches'
     key sets, so a merge's domain is a union — which collapses back to the
     original only because both branches started from it. That is why
     `resolve_select_shape` takes its hypothesis for EVERY target rather than
     for the one that fires.

   - §14 **The extent map's default never moves**, on either side — every
     writer of it is a `PMap.set`. That is the hypothesis §8 needs, lifted to
     the module level (`module_update_gs_*_extent_default`), so the induction
     can carry it as an invariant rather than re-deriving it.
   - §15 **All three module kinds are now stated as STEPS**, in the shape
     `module_update_gs_*` presents rather than the shape the evaluators do:
     `transformer_mod_step`, `deparser_mod_step`, `parser_mod_step`. So the
     induction has one lemma per kind and no plumbing of its own.

     Three things the steps settle, each of which would otherwise surface
     inside the induction:

     - **A transformer's step is unconditional** — it does not write
       `gps_valid` at all. Its one subtlety is that the concrete state's
       memory is only POINTWISE equal to the concretized symbolic memory,
       while `transformer_commute_mem`/`_extent` are stated over the literal
       `concretize_mem_ctx`; `MemCommuteLemmas.eval_transformer_concrete_mem_cong`
       is what bridges that, and it is why §6 of that file exists.
     - **A deparser does not write the header map at all**, only the write
       tape (appended, hence `List.map_app`) and its own module state.
     - **The parser's flag half is unconditional and the rest is not.** Both
       sides conjoin the accept condition into the running validity and the
       two accept conditions agree whatever the packet did; everything else
       needs the result to be valid.

     `mod_states` stays a LITERAL `PMap.map` of the symbolic one across all
     three, because each kind stores its result with one `PMap.set` at the
     same key — `pmap_set_map_eq`. That is what keeps `gps_agree`'s structural
     clause available without weakening.

   - §16–19 **The induction's scaffolding is built.** `gs_rel` and
     `gs_dom_ok` are defined, the recursion is destructured under
     `no_fan_out`, and the three invariants that have to be carried
     ALONGSIDE the agreement are proved preserved across one module:

     - `gs_dom_ok_step` — the domain conditions. This was the piece flagged
       as the blocker, and it is done. Both conditions depend on their state
       only through its shape, every module preserves the header map's shape,
       and a transformer preserves its own state and ctrl maps' shapes
       (`smt_transformer_sv_shape`, `smt_transformer_ctrl_eq`), so the
       conditions survive. `dom_ok_at_shape` is the transfer lemma.
     - `module_update_symbolic_pprefix` — the read tape stays a
       presence-prefix. Only a parser rewrites it and a residual of a prefix
       is a prefix, so this is what keeps step 7 applicable at the SECOND
       parser in a chain.
     - `ms_kind_agree_step` — see the correction below.

   **A correction to the invariant recorded above.** Part (a) was stated as
   module-state DOMAIN agreement. That is not strong enough. Both
   `module_update_gs_*` dispatch on the module kind and the stored state's
   kind TOGETHER, and take a fallback branch that writes nothing when they
   disagree — so if the two sides ever held different KINDS at one key, one
   would store its result and the other would not, and the domains would come
   apart, after which the two runs can disagree about whether the network
   completes at all. The invariant has to be `ms_kind_agree`, which implies
   domain agreement (`ms_kind_agree_dom`) and is what is actually preserved.
   It starts true because concretization preserves the constructor
   (`ms_kind_agree_concretize`).

   Its preservation is also where `well_formed_parser` is needed for the first
   time: on a REJECTING run the concrete parser must still return `Some`, or
   it would take the branch that stores nothing while the symbolic side stores
   its result. `eval_parser_no_fuel_starvation` is what rules that out.

   - §20–22 **The induction is proved.** `network_commute` is the fuel
     induction and `program_commute_full` delivers
     `eval_general_program_commute`'s conclusion from five hypotheses about
     the INITIAL state. All `Closed under the global context`.

     `module_step_rel` is the last case analysis — three module kinds by two
     validity cases. Under validity the incoming `gps_agree` says the concrete
     state's fields ARE the concretized symbolic ones, so §15's steps apply
     directly; under invalidity nothing is known about the states and nothing
     needs to be. One thing worth keeping: for a parser and a deparser the
     stored module-state payload is DISCARDED — `set_module_header_map` and
     `set_module_packet` between them overwrite every field — so only its kind
     matters, and those two cases need no relation between the two payloads at
     all. Only the transformer needs `cls = concretize ls f`.

   **So what is left is not the semantics at all**: it is discharging
   `program_commute_full`'s five hypotheses at the state
   `init_general_symbolic_state` builds, and then wiring them through
   `modnet_equivalence_checker_sound`, which consumes the hypothesis-free form
   of the bridge. The five:

   - `no_fan_out` and `net_parsers_wf` — `is_linear_chain` and
     `well_formed_general_program` restricted to what the proof uses. Both are
     already hypotheses of `modnet_equivalence_checker_sound`, so its proof
     only has to pass them through, which is what this entry predicted.
   - `gs_dom_ok` at the initial state — what `collect_write_headers` and
     `force_keys` over `collect_module_state_targets` exist to provide.
   - `pprefix f (sh_read_tape s)` — holds because `symbolic_input_bits` marks
     every bit present (`ParserCommuteLemmas.pprefix_symbolic_input_bits`).
   - the extent default — `PMap.init`'s.

   Superseded, kept for the record:

   1. **`gs_rel` across one module.** Combining §15's three module steps with
      the validity split: under validity the module steps apply directly
      (the concrete state's fields ARE the concretized symbolic ones, which
      is what `gps_agree` gives); under invalidity nothing is known about the
      states and nothing needs to be — both flags stay false by §4, and
      `ms_kind_agree_step` keeps the domains in step. This is the one
      remaining piece with real case analysis: three kinds by two validity
      cases.
   2. **The fuel induction**, using §17's destructuring. Ordinary induction on
      fuel, carrying `gs_rel`, `ms_kind_agree`, `gs_dom_ok`, `pprefix` and the
      two extent defaults.
   3. **Tying it to `program_commute_from_network`** (§9), which already takes
      the network outcome as hypotheses and delivers the bridge's conclusion.

   Note that the two domain conditions transfer between the concrete and
   symbolic sides for free (`PMap.map` preserves domains), and both are what
   the header-map seeding (`collect_write_headers`) and `force_keys` over
   `collect_module_state_targets` exist to provide — so discharging them at
   the network's ENTRY is a statement about `CrVarLike.collect_*`, separate
   from preserving them along the chain.

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

   **Settled — how to compare a transformer's MODULE state: take whole-state
   equality, not an extensional `ts_agree`.** This entry used to recommend the
   opposite; `NetworkCommuteLemmas` §7 is the evidence that the first route is
   both available and cheaper.

   The question is whether `gps_agree`'s `mod_states c1 = mod_states c2` (and
   its `sh_hdr_map` clause) can be delivered from results that are per-key. On
   its own, pointwise `!!` agreement is **not** enough — that is exactly why
   the memory maps had to be weakened — because `!!` collapses an absent key
   onto the default and so cannot see the key set. Add the key set and the
   default and it *is* enough: `pmap_ext`.

   Both are available here, which is what decides it:

   - `new_pmap_from_old_default` / `new_pmap_from_old_dom`: the symbolic writer
     keeps `fst` and rebuilds the tree with `PTree.map`, so it moves neither
     the default nor the domain. This is the fact the entry called "not
     derivable from the class" — it is not derivable from the class, but all
     three instances *are* `new_pmap_from_old`, so one lemma about that covers
     them.
   - `pmap_set_default` / `pmap_set_dom_present`: the concrete writer keeps the
     default too, and adds a key only when it writes an absent one — which the
     domain invariant below rules out.
   - `pmap_map_default` / `pmap_map_dom` for the concretized side.

   So `gps_agree` does **not** need weakening, and
   `modnet_equivalence_checker_sound` does not have to be touched. Prefer this:
   an extensional `ts_agree` would also have needed a congruence for the
   concrete transformer in its state argument, per `CrVarLike` instance, which
   is strictly more work than the four `PMap` facts above.

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

Groundwork already in the tree: `CrVal.ld_val_unalloc` / `st_val_unalloc` — an
undeclared region reads `ErrorVal` and swallows writes, at every width. These
are what make the equality hold; note it is *provable*, not definitional,
because `List.seq 0 (it_bytes ty)` cannot reduce for a variable `ty`.

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

### 1.6. A map lookup is not an indexed array

`~/proj/ect` models a BPF map as a memory region and `bpf_map_lookup_elem` as
`slot = key % nslots` into it. The modulus is the problem: it puts distinct
keys in one entry, and that is unsound in the direction that matters — two
programs reading *different* map entries get reported equivalent.

It was demonstrated, not theorised. With `nslots = 4`, two programs differing
only in a constant key came back `Equivalent`:

```
lookup(key=3) vs lookup(key=7):  Equivalent      # 3 % 4 == 7 % 4
lookup(key=3) vs lookup(key=4):  Not Equivalent  # different slots
```

**What is already fixed.** Two things, and neither is the real fix:

- The two map *families* are now modelled separately, because they disagree
  about what a key is. An ARRAY map is pre-allocated and zero-filled at
  creation, so `key < max_entries` is present — always — and the presence is
  decided by the key alone, exactly; no presence byte is read, and the miss
  path the old model invented is gone. A HASH map's key is opaque and its
  contents on entry are unknown, so a free presence byte is the right
  abstraction there.
- A *constant* key at or above `nslots` is now refused rather than folded.
  Checking for a collision within one program is not enough: the two programs
  a comparison is about are translated separately and neither sees the other's
  keys, so `key=3` and `key=7` each alias nothing on their own. Requiring
  every constant key to be below `nslots` makes the slot *be* the key, which
  no other program can collide with.

**What remains.** A key the translator cannot evaluate — anything computed,
which includes every flow-tuple lookup — is still folded by the modulus and
still aliases silently. `MAP_MAX_SLOTS` only moves the boundary; it cannot
remove it, because the IR's regions are finite byte arrays and a map is
associative memory over a 2^32 key space. No encoding into a bounded array
avoids either aliasing keys or bounding the key space.

**The fix.** Model a lookup as an uninterpreted function of the map and the
key, constrained only to be functional: same map and same key give the same
result. That is what the semantics actually needs and what a bounded array
cannot express. Concretely:

- a new `SmtArithExpr` constructor for the application, and one for the map
  value it reads, with `eval_smt_arith` cases;
- `SmtCompile` lowering it into the core fragment, which is where the
  functional constraint has to be stated;
- `Z3Solver` emitting a genuine uninterpreted function (`mk_func_decl`), which
  Z3 handles natively — this is the one place the solver is *better* suited
  than the array encoding;
- and the concrete side needs a matching story, since
  `eval_general_program_concrete` has to run it too.

Until then the guard above is what keeps the unsound cases loud. The one
concrete gap it does not cover is a computed key.

### 1.7. A control-plane config is an input, but `ctrl` is seeded per program

`init_general_symbolic_state` seeds a transformer's ctrl variables through
`seed_name prog_prefix (SVCtrl m_id v)` (`CrVarLike.v:735`, in
`init_sym_mod_state`), which expands to
`get_mod_prefix prog_prefix m_id ++ "ctrl_" ++ pos_to_string v`
(`CrVarLike.v:551`) — so a ctrl name is `p1_m10_ctrl_1` and the two programs a
comparison is about get *unrelated* control-plane configurations. Regions and packet bits are deliberately unprefixed for the
opposite reason, and the comment on `init_symbolic_mem` states it: give the two
runs independent variables for an input and "the solver satisfies 'the outputs
differ' by simply handing them different memories."

A table's contents are supplied from outside the program, so they are an input
by exactly that test. The rationale currently written down — that state and
ctrl are "each program's own internals" — holds for state-as-scratch and does
not hold for ctrl. The consequence is that any program whose output depends on
a table comes back `NotEquivalent` for free, which is the failure mode the
region comment exists to warn about.

Nothing is broken today only because `OpCtrlPlane` is effectively dead syntax:
the sole use anywhere is `TestPrograms.v:84`, and no `test/*.ir` fixture
contains one. That also means there is no regression surface, so this is the
cheap moment to do it.

**The fix**, in an order that never leaves a shared variable without a
declaration check behind it:

- **Widths first.** A header can be seeded width-pinned —
  `SmtCast u64 ty (SmtVarVal "hdr_<h>")` — because `ExtractOpConstructor h w ty`
  declares a width and `collect_header_types` recovers it. A `Ctrl` is a bare
  uid and `Operand` is width-free by design, so a shared ctrl would stay a
  loose `SmtArithVar`: an arbitrary `CrVal`, possibly `ErrorVal` or the wrong
  tag (1.1.4). Shared-and-loose is *safer* than unshared, since both sides see
  the same junk and agree on it, but it reopens the same bug the region fix
  closed (SOUNDNESS.md model-debt item 3): a checked `cast` sends a
  width-mismatched value to `ErrorVal`, and `CrVal.ltb`/`eqb` are false on
  `ErrorVal` in *both* directions, so a pair of programs built around
  complementary comparisons (e.g. `x > 100` vs `x < 101`) can silently lose a
  case. That reopens exactly when the two programs read one ctrl at different
  widths — one op gets `ErrorVal`, the other does not, and the verdict is
  `NotEquivalent` on a configuration no control plane can produce. So add a
  `collect_ctrl_types`
  walk over the ops that *consume* each ctrl, seed
  `SmtCast u64 ty (SmtVarVal "ctrl_<c>")`, and refuse a program that reads one
  ctrl at two widths, the way `solve` refuses a query failing `lcb`.
- **Then the gate.** Sharing a name is well defined only behind a declaration
  check. `modnet_equivalence_checker` has `mem_region_decls_eqb` for exactly
  this and consults ctrl nowhere (`SmtModuleQuery.v:171`, a comment). A
  `ctrl_decls_eqb` — same uid set, same widths — is the precondition, or the
  query silently means "for every value of p1's ctrl 3 and p2's unrelated
  ctrl 3".
- **Then unprefix, and make it program-global.** The prefix is per *module*,
  not just per program, so dropping `prog_prefix` alone leaves `_m10_`, and two
  independently compiled programs do not share module numbering — the eBPF
  lowering numbers modules per basic block, so an `-O0`/`-O2` pair has disjoint
  module ids. Sharing therefore means seeding ctrl once as `ctrl_<uid>` rather
  than per module, which also makes one uid in two modules one variable. That
  is a change to the seeding, not a rename.
- **The concrete seed has to move with it.** `init_concrete_transformer_state`
  sets `t_ctrl_map := PMap.init UninitVal` (`CrVarLike.v:379`), so concretely
  every ctrl is `UninitVal` and any op reading one yields `ErrorVal`. Harmless
  while ctrl is unused, but a real input needs a concrete seed that inhabits
  the symbolic family, the way `seed_header_concrete` gives a header
  `mk_int ty 0` and `init_concrete_mem` gives a region zero bytes rather than
  `mk_region`'s uninitialized cells. Otherwise there is no concrete counterpart
  for `eval_general_program_commute` to relate.

**Do not change `State` at the same time.** It looks like the same case and is
not. Initial register contents are an input, which argues for sharing, but
`State` doubles as per-module scratch a lowering allocates freely — `force_keys`
over `collect_module_state_targets` exists precisely because a rule can write a
state variable the module never declared. Two lowerings of one program have
different scratch sets, and sharing scratch by uid would alias unrelated
temporaries into one variable. The IR cannot tell register-as-input from
state-as-scratch apart, which is the argument for modelling a register as a
`MemRegion` — already shared, already runtime-indexed — and leaving `State`
prefixed.

**Regression test**, in the style of "hdr init: a register read before its
extraction is free": a pair differing only in a rule that reads a ctrl, which
must come back `Equivalent` with sharing and `NotEquivalent` without. Verify
both ways round — a test that passes before the change tests nothing.

This also removes a constraint from the P4 front-end plan. Lowering a
runtime-populated table's action parameters to `OpCtrlPlane` is meaningless
while ctrl is prefixed, which is why entries have to be supplied as constants;
with sharing it asks "for every table configuration, do these agree?", which is
the question a `basic.p4`-style LPM table actually poses.

### 1.8. Header validity: what a `SetOp` and a conditional emit would buy

The IR has no header validity bit, which costs two different things. Neither is
speculative — both were measured against p4lang/tutorials and
Princeton-Cabernet/p4-projects with the p4c backend in `translation/`.

**The two changes.**

- **A parser op that writes a constant into a header.** `ParserOp` is
  `SeekForward | ExtractOpConstructor`, so a parser can branch but cannot
  record which branch it took. One more constructor — `SetOp h v ty` — lets a
  front-end emit `SetOp flag 0` in the start state and `SetOp flag 1` in every
  state that extracts, after which `isValid()` is an ordinary match on an
  ordinary header. Cost is one case each in `eval_parser_concrete`,
  `eval_sym_parser_state` and `ParserCommuteLemmas`, and it touches no tape, no
  cursor and no presence condition — which is where the parser proofs are hard.
  It does not disturb `ParserWellFormed` either: a non-consuming state already
  exists as `psd_action = None`.
- **A guarded `EmitOp`.** This is the expensive one, and the reason is written
  down already: `wt_unconditional` says every emitted bit carries
  `cvc := SmtTrue`, and `sym_out_equal_sound` compares write tapes
  *positionally*, deliberately unlike the read tape. Conditional emit means the
  write tape grows presence conditions and the `present_bits` / `pprefix`
  argument has to be redone on the output side.

**What `SetOp` alone buys: nothing.** It was worth checking rather than
assuming. Across both repos exactly one program is blocked only by validity
being a disjunction — `basic_tunnel`, whose `parse_ipv4` is reached both
directly and through the tunnel — and the front-end now derives that
disjunction and emits it as several rules with the same action, so
`basic_tunnel` lowers without any IR change. `SetOp`'s one unique advantage,
exact validity through a *cyclic* parser, is unexercised: `source_routing` has
a parser loop but needs header stacks, and `mri` has one but needs conditional
emit anyway. No Cabernet program is blocked by validity alone — every one that
tests `isValid` also needs a hash, a register, or `setValid`.

**What the pair buys.**

- *Faithfulness, not just lowerability,* for `basic`, `qos`, `ecn`,
  `basic_tunnel` and `multicast`. All five lower today, but their deparsers
  emit unconditionally, so a packet whose IPv4 header was never parsed still
  gets 160 bits of seeded garbage on the wire. Today that is contained by
  analysing one packet class per query with the parser rejecting the rest
  (`PktClass.v`); the pair removes the need to restrict, and with it the need
  to edit the program under test.
- *`p4runtime/advanced_tunnel.p4`*, which is `basic_tunnel` plus encap and
  decap written as `setValid`/`setInvalid`. Its only other blocker is
  `counter.count()` — registers, 1.6's territory.
- *Necessary but not sufficient* for `SipHash-tofino` (all three variants) and
  `AES-tofino`, which invalidate a metadata header to control what is emitted.
  Both additionally need a `Random` extern; SipHash's rounds otherwise lower.

**What it does not buy.** `mri`, `link_monitor` and `source_routing` need
header stacks; `flowcache` needs cloning; `firewall` and `load_balance` need a
hash. Those are unrelated gaps.

**So the ordering is: conditional emit is the valuable half and `SetOp` is the
cheap half, and `SetOp` on its own is not worth doing.** If validity is ever
taken on, take both — `SetOp` is what makes a guarded emit have something exact
to be guarded *on*, and a guarded emit is what makes `SetOp` worth having.

### 1.9. A header is seeded at its CONTAINER's width, not its declared width

`seed_header_syms` gives a header some parser extracts an arbitrary value of
its `CrIntType` — `SmtCast u64 ty (SmtVarVal "hdr_<h>")`. For a field whose
declared width fills its container that is exact. For one that does not it is
too permissive: `ExtractOpConstructor h width ty` carries BOTH the declared
bit width and the container, and `collect_header_types` keeps only the
container, so a `bit<2>` field is seeded as an arbitrary `u8`.

It only shows when a header is READ WITHOUT HAVING BEEN PARSED, because an
extraction overwrites the seed with `width` bits and is exact. That is not a
corner case — it is what a P4 program does whenever it reads a field without
an `isValid()` guard, which the tutorials' `ecn.p4` does.

**Demonstrated, not theorised.** `test/p4tutorials/ecn.p4` tests
`hdr.ipv4.ecn == 1 || hdr.ipv4.ecn == 2`; `ecn_alt.p4` writes the same thing
as `hdr.ipv4.ecn != 0 && hdr.ipv4.ecn != 3`, which for a `bit<2>` is the same
set. The checker says **NotEquivalent**, on a model with
`ipv4.ecn = 252` — a value no `bit<2>` can hold. It arises because the
packet is not IPv4, so `parse_ipv4` never runs and the field keeps its seed.
Guard both reads with `isValid()` and the pair goes back to Equivalent, which
is what pins the diagnosis.

**Which direction.** This over-approximates the input space, so it produces a
spurious NotEquivalent rather than a missed difference — a false alarm, not a
false assurance. It is still worth fixing: a checker that cries wolf on a
correct optimisation is one nobody runs.

**The fix.** `SmtBitSlice 0 w` is exactly the operator wanted and already
exists: `slice_val` returns `mk_int u64 (v & ones w)`, so the inner term still
denotes a `u64`, the cast's source check still passes, and `cast u64 ty` retags
without truncating because `w` never exceeds the container. The seed becomes an
arbitrary `w`-bit integer tagged at the container -- which is exactly what an
extraction of `w` bits produces, and that correspondence is the whole point.

```coq
(* now *)   SmtCast u64 ty (SmtVarVal (seed_name "" (SVHdr h)))
(* fixed *) SmtCast u64 ty (SmtBitSlice 0 width (SmtVarVal (seed_name "" (SVHdr h))))
```

What moves with it:

- **`collect_header_types` carries the width.** It already destructures
  `ExtractOpConstructor h _ ty` and discards it in that `_`
  (`CrVarLike.v:600`); the type becomes `list (Header * CrIntType * nat)`, and
  `lookup_header_type` with it.
- **`seed_header_conc` (`InitReachable.v`) is written through the SAME
  functions the symbolic term denotes** -- `cast u64 ty (slice_val 0 width
  (IntVal (ii_hdr ii h) u64))`, not a hand-rolled `Z.land`. Then
  `seed_header_adequate` stays the one-liner it is (`cast_u64_mk_int` plus
  `slice_val`'s own reduction) instead of becoming a bit-twiddling lemma. This
  is the discipline `init_conc_mem` already follows, where `region_of_bytes` is
  the normalizer on both sides.
- **`seed_header_concrete` (`CrVarLike.v`) needs no change**: `mk_int ty 0` is
  still an inhabitant of the narrowed family.
- **`lookup_header_type` should fold with `max` on the width.** It takes the
  FIRST match, so a header extracted at two widths gets whichever the fold saw
  first -- and picking the narrower one would UNDER-approximate the input
  space, which is a false Equivalent rather than a false alarm. Nothing in the
  tree does this today (the p4c backend gives each field one Header at one
  width, and `lower_table.py` chunks wide fields into separate Headers), but it
  is one line and it is the only part of this touching soundness.

Expect fallout in `valid_iff_reachable`, which says the concretizable states
are exactly the valid ones and is proved through `seed_header_adequate` ->
`init_concretize_eq` / `inputs_realizable`. The blast radius is `CrVarLike.v`,
`InitReachable.v` and two lines of `NetworkCommuteLemmas.v`; `pmap_fold_ext`
does most of the work and should be indifferent to the term shape. Update
`SOUNDNESS.md` alongside.

Until then `ecn_alt.p4` is a checked-in witness: it is EXPECTED to report
NotEquivalent, and it should start reporting Equivalent when this is fixed.

### 1.10. The repository has no LICENSE, and two tests are AGPL-derived

`translation/tests/fridge_eack*.p4` transcribes `calc_tcp_eack.p4` and
`translation/tests/conquest_baseline*.p4` copies `baseline.p4`, both from
[Princeton-Cabernet/p4-projects](https://github.com/Princeton-Cabernet/p4-projects),
which is **AGPL-3.0**. Each file now carries the upstream copyright and licence
notice, which it did not when the fridge one was first committed.

There is no LICENSE file in this repository, so what carrying those files
implies is undecided. AGPL is strongly copyleft and its terms attach on
distribution. Three ways out, and it is not our call which:

- pick a licence for this repository and check it against AGPL-3.0;
- keep the tests but not the sources — have `run.sh` fetch the upstream repo,
  as the eBPF fixtures already depend on an external `~/proj/ect`;
- replace them with programs written here that exercise the same constructs,
  losing the "this is a real program someone published" property that is much
  of why they are worth having.

Worth settling before the artifact is published, not after.
