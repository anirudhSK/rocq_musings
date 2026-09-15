# Soundness bugs in the memory model, and in the shims around the checker

Four bugs, in two groups.

**Bugs 1 and 2** are defects in the checker's own semantics. Both come from the
same gap: the solver was free to choose arbitrary `(tag, value)` pairs for a
region's contents on entry, while the IR assumes a region is a byte array. Neither
is a mistake in the soundness or completeness statements — those are still true.
What was wrong is the set of initial states we were exploring: it included states
no machine can be in, and a difference witnessed only by such a state is not a real
difference. Both were found through loads, and only through loads — see
[Why only loads](#why-only-loads).

**Bugs 3 and 4** are the other direction: defects in untrusted translation code
*around* a verified core, found because the checker gave something independent to
disagree with. Bug 3 is in ParserHawk's exporter, bug 4 in our own JSON-to-IR
shim.

---

## Bug 1 — a checked cast turns an unconstrained input into `ErrorVal`

### What is the bug

Two programs that must agree on every input are reported `NotEquivalent`:

```
P1:  h := mem[0]                     P2:  h := mem[0]
     if h > 100  then 1 else 0            if h < 101  then 0 else 1
```

For any byte `b`, `b > 100 ⟺ ¬(b < 101)`, so these emit the same byte on every
input. (`TestModulePrograms.mod_prog_mem_cmp_gt` / `_lt`.)

### How does it happen

The IR is `LoadOp u8 region_1 0 h`. A width-`ty` load expands to a per-byte
assembly:

```coq
ld_val ty a base   = cast u64 ty (fold_i  or_at u64 acc (byte_into_val (ld_cell a (base+i)) i))
byte_into_val b i  = mul_at u64 (cast u8 u64 b) 2^(8i)
```

The solver returns `mem[0] = (tag u16, value 5)`, which decodes to `IntVal 5 u16`:

| step | result |
| --- | --- |
| `cast u8 u64 (IntVal 5 u16)` | `crinttype_eqb u16 u8 = false` → **`ErrorVal`** ← **diverges here** |
| `mul_at u64 ErrorVal 1` | `ErrorVal` |
| `or_at u64 (IntVal 0 u64) ErrorVal` | `ErrorVal` |
| `cast u64 u8 ErrorVal` | `ErrorVal` |
| `h > 100` via `CrVal.ltb` | `false` |
| `h < 101` via `CrVal.ltb` | `false` |

P1 falls through to its default and emits 0; P2 falls through to its default and
emits 1. Different outputs, so `NotEquivalent`, witnessed by `mem[0] = (u16, 5)`.

Note **where** it diverges. Not in the load, and not in the comparison — both do
exactly what they are specified to do. It diverges one step earlier, at the
boundary, when the solver was permitted to choose a cell no machine could present.

### Why does it happen

Two properties combine, and both are needed:

1. **`cast` is checked, not coercive.** It takes a source and a destination type
   and validates the source tag, so a wrong-width input becomes `ErrorVal` rather
   than being reinterpreted.
2. **`CrVal.ltb` is false in *both* directions on `ErrorVal`.** So `x > 100` and
   `x < 101` stop being complements, and a pair of programs built around that case
   analysis silently loses a case.

Neither is wrong on its own. The gap is that a region's contents on entry are an
**input**; the IR says that input is a byte array, and the solver encoding did not.

This did not surface earlier because nothing used to cast a value the solver could
set directly. The casts we had were applied to parser output, and a parser fixes
the bit width, so there was no freedom to introduce a type mismatch.

### How to fix it

Constrain the input to be what the IR already claims it is: for every cell below
the declared length, `tag = u8`. This is now a conjunct of the query
(`SmtCompile.cell_is_byte`, lifted by `regions_wf`).

Two alternatives were considered and rejected for now:

- **(a) Make an operation over `ErrorVal` invalidate the whole run.** This
  collapses into the both-reject trap — two programs that both reject are
  reported "equivalent" — so it trades a false `NotEquivalent` for a false
  `Equivalent`, and it makes every computation involving an error value
  indistinguishable when we may want to tell them apart.
- **(b) Drop the `from` field and let casts coerce anything.** This closes the gap
  from the other side, but it lets the solver answer `(u64, 0x01)` where only
  `(u8, 0x01)` is meaningful — trading a false verdict for uninterpretable
  counterexamples, since memory is a byte array and a `u64` cell means nothing.

---

## Bug 2 — an over-wide value collides with its neighbour's byte slot

### What is the bug

Again two programs that must agree, reported `NotEquivalent`:

```
P1:  out := mem[0..1]              P2:  lo := mem[0]
     (one u16 load)                     hi := mem[1]
                                        out := lo | (hi << 8)
```

(`test/basic_load.ir` — `LoadOp W16` at offset 0 — against
`test/basic_load_split.ir` — `LoadOp W8` at offsets 0 and 1.)

### How does it happen

The solver returns `mem[0] = (u8, 0xffff)`, `mem[1] = (u8, 0x00)`. **Both tags are
`u8`**, so bug 1's constraint is satisfied. But `0xffff` does not fit in eight bits.

P1, the u16 load:

| step | result |
| --- | --- |
| `cast u8 u64 (IntVal 0xffff u8)` | tag matches → `mk_int u64 0xffff`, which masks to the **target** width (64), so **no truncation** ← **diverges here** |
| `* 2^0` and `* 2^8` | `0xffff` and `0` |
| `or` | `0xffff` |
| `cast u64 u16` | `0xffff` |

P2, two u8 loads: each ends in `cast u64 **u8**`, which masks to eight bits, so
`mem[0]` reads back as `0xff`. Result: `0xff | (0 << 8) = 0x00ff`.

`0xffff ≠ 0x00ff`.

### Why does it happen

`IntVal` pairs a raw 64-bit value with a width tag, so the *representation* admits
values that do not fit their tag. `mk_int` cannot build one — but a solver model
does not go through `mk_int`.

**This one really is specific to multi-byte loads, and the reason is sharp: at one
byte, the trailing `cast u64 ty` truncation is exactly the constraint that is
missing.** It masks the excess away and the bug is invisible. At two or more bytes
the excess bits sit in positions `8+`, which is where the *next* cell's
contribution goes, and the `or` merges them **before** the final mask — which is
then 16 bits wide, too wide to remove a collision that has already happened.

So it is not quite that other operations are careful with width and `ld_val` is
sloppy. It is that `ld_val` is the only place where two independently chosen cells
are combined *by position*, so it is the only place where one cell's excess can
land on another's slot.

### How to fix it

A second conjunct: every cell below the declared length is `< 256`.

The alternative — masking each cell inside `ld_val` — fixes the assembly but
leaves the model free to report `(u8, 0xffffffYY)` as a witness. That is the same
uninterpretable-counterexample problem as bug 1's option (b), and it is rejected
for the same reason.

---

## Why only loads

Neither bug can be triggered anywhere else, for two separate reasons:

- **Region equality cancels.** The other place a region's entry cells are observed
  is the equivalence check itself, and both programs' regions are rooted at the
  *same* `SmtArrVar` — `init_symbolic_mem` seeds one set of region variables shared
  by both runs. A malformed cell therefore appears identically on both sides and
  makes no difference.
- **Stores cannot manufacture one.** `byte_of_val` ends in `cast u64 u8`, so
  anything written during a run is a well-formed `u8` or `ErrorVal`. Only the
  *initial* contents are unconstrained.

### Which constraint catches which bug

Measured by keeping one half of the conjunct and dropping the other:

| constraint kept | one u8 load, opposite compares | u16 load vs two u8 loads |
| --- | --- | --- |
| tag only (`tag = u8`) | Equivalent | **Not Equivalent** |
| value only (`< 256`) | **Not Equivalent** | Equivalent |
| both | Equivalent | Equivalent |

Two things worth reading off this table:

**Bug 1 is not multi-byte-specific.** `ld_val` casts *every* cell with
`cast u8 u64` at every width, and `it_bytes u8 = 1`, so a single-byte load
performs exactly one such cast and is just as exposed. The `mem[0] > 100` example
above is a one-byte load.

**The two halves are independent.** Neither constraint subsumes the other, and
each has exactly one regression test that fails without it.

---

## What this family of bugs actually is

An underspecification of the set of initial states the checker explores.

It is worth being explicit that this is the *same* defect as the earlier symbolic
state initialization bug — where every run was restricted to
`header_i = state_i = ctrl_i` — but failing in the opposite direction:

| | reachable set | consequence |
| --- | --- | --- |
| state-init bug | **under**-approximated | real differences missed → false `Equivalent` |
| these two | **over**-approximated | unreal differences found → false `NotEquivalent` |

In both cases the soundness and completeness statements were true as written. What
was wrong was which states they were quantifying over. This is why `SOUNDNESS.md`
records that imprecision in the reachable set is unsound **in either direction**:
over-approximating compares runs that never happen, under-approximating hides runs
that do.

The corresponding entry conditions now have to agree on three sides, and they must
move together:

- **symbolic** — `eval_smt_mem`'s `SmtArrVar` arm maps `CrVal.to_byte` over the
  region;
- **solver** — the `regions_wf` conjunct pins tag and value;
- **concrete** — `concrete_gp_state_is_valid` requires every cell below the
  declared length to be `Legal (mk_int u8 _)`, and `init_concrete_mem` builds
  regions of zero bytes.

Loosen one without the others and one of the two solver axioms becomes false.

Because `regions_wf` is stated in the IR rather than asserted about the model, it
is provably vacuous on the Rocq side (`regions_wf_true`): `to_byte` already forces
every valuation to satisfy it. That is what makes conjoining it to the query
sound — it constrains the solver without changing what the query means.

### What is still open

`concrete_gp_state_is_valid` pins down regions, **field registers**, the tapes, the
access extents and the validity flag. The header clause was added later: a header
some parser extracts holds an arbitrary value of its own width on entry, which the
symbolic seed `CrVarLike.seed_header_syms` *forces* rather than merely permits, so
it needs no solver-side constraint.

It does **not** yet pin down `mod_states` — whose transformer entries carry free
state and control variables — nor headers that no parser extracts. Those are free
on the symbolic side with no stated concrete counterpart, so the same class of bug
is still possible there. It is harder to trigger, because comparison and
arithmetic collapse `UninitVal` and `ErrorVal` to the same behaviour, but the gap
is real and `reachable_if_valid` remains admitted.

---

# Bugs found *with* the checker, in the shims around it

The two above were defects in our own semantics, found by reasoning about it. The
two below are a different kind: defects in **untrusted translation code sitting
next to a verified core**, found because something independent was able to
disagree with it. Neither was detectable from inside the shim that contained it —
both shims produced well-formed, self-consistent output that was wrong only
relative to a semantics living somewhere else.

## Bug 3 — ParserHawk exports a transition rule its synthesizer never verified

### What is the bug

ParserHawk's IPU and Tofino pipelines for the multi-field-key workload are
synthesized against the same specification, so they should agree. Lowered into the
IR and compared, they came back `NotEquivalent`.

### How does it happen

Synthesis emits four variables per pipeline stage `S` and TCAM slot `T`:
`assign_stage_S_tcamT`, `key_val_…`, `key_mask_…`, `tran_idx_…`. (The names are
transposed — the outer loop is the stage but it is written into the `tcam` field —
which is confusing but not itself the bug.) The final model for this workload:

| stage | assign | val | mask | tran_idx |
| --- | --- | --- | --- | --- |
| 0 | **4** | 0 | 65535 | 2 |
| 1 | 1 | 0 | 65535 | 2 |
| 2 | **0** | 0 | 65535 | **3** |

`implementation()` has node `i` consult only **stage `i`**'s slots, and a slot
fires only when `assignments[i][T] == node_id`. So stage 0's slot is dead
(`4 ≠ 0`), stage 2's slot is dead (`0 ≠ 2`), and node 0 always takes its default.
Tracing `idx` through the verified model confirms it: `[1, 2, 3]`.

`code_gen_IPU.py` instead reads `assign` as an owner pointer and files the rule
under `node_list[assign]`, guarded only by `assign < num_parser_nodes`. So stage
2's dead slot is emitted as a **live rule on node 0**, and stage 0's real
parameters vanish from the JSON entirely.

The divergence is observable: on packet `0…01` with field1's register starting at
191, the exported pipeline accepts after extracting only `field_0`, emitting two
registers it never wrote. Running ParserHawk's own verification query pinned to
that same input gives `spec = impl = [0, 0, 1]` — the verified pipeline never goes
there.

### Why does it happen

`assign` means two different things to its two consumers: an **enable predicate**
in `implementation()` (fire iff `assign` names the node reading this stage) and an
**owner pointer** in the exporter. They coincide only when `assign` names a node
inside that entry's own stage, and nothing enforces it — the synthesis constraint
bounds `assign` only from above:

```python
s.add(Or(assignments[i][j] < sum_l[i], assignments[i][j] > num_parser_nodes))
```

`sum_l[i]` is the correct upper end of stage `i`'s node range, but there is no
lower bound, so naming a node in an *earlier* stage is permitted — always dead in
the model, always emitted by the exporter.

### How to fix it

Membership in the entry's own stage, not just an upper bound. Stage `S` owns nodes
`[sum_l[S] - parser_node_pipe[S], sum_l[S])`:

```python
lo = sum(parser_node_pipe[:S]); hi = lo + parser_node_pipe[S]
if lo <= nodeID < hi: ...
```

Better still, add the same lower bound to the synthesis constraint, so `assign`
can only ever be "a node in this stage" or "unused" and there is nothing to
misfile. Note this leaves a second, latent gap: the TCAM slot index carries match
priority (lower dominates) and the JSON drops it, so a node with several entries
loses their order.

This does not affect ParserHawk's synthesis or verification, both of which operate
on the Z3 model. It affects only the untrusted step that lowers that model to a
pipeline description — precisely the step an independent equivalence checker is
positioned to validate.

## Bug 4 — an overrunning lookahead rejects or not depending on bit adjacency

### What is the bug

Two pipelines that differ only in an extra key bit disagree about whether a
lookahead running off the end of the packet rejects. Reduced:

| `Tran_key` | lowered as | 8-bit packet, peek at cursor 9 |
| --- | --- | --- |
| `["lookahead 1"]` | one `Select` case | **Reject** |
| `["lookahead 1", "field1[8]"]` | a chain of one-case states | **accepts** |

Found by `translation/parserhawk/test_lower_table.py`, not by hand.

### How does it happen

`eval_transition_concrete` checks `select_bits_available_concrete` over **every**
case of a select before matching any of them, so one overrunning `Peek` rejects
the parse even when an earlier case would have matched.

`lower_table.py` emits a single `Select` only when every rule's cared bits form
one contiguous run. A key spanning two runs goes through `chain()`, which emits
one zero-width state per run with the next rule as its fallthrough. Each of those
states carries a single case, so its availability check covers only its own
origin — and a `Peek` sitting in a later link is never reached once an earlier
link falls through.

### Why does it happen

Two lowering paths with different observable semantics, selected by a property of
the *input encoding* rather than of the pipeline: whether the key's bits happen to
be adjacent. Bit adjacency is not supposed to be semantically load-bearing.

### How to fix it

**Fixed.** `lower_table.peek_guard` emits a leading state whose select carries
every `Peek` origin from that node's rules, with the cases *and* the default all
targeting the chain head. The match is therefore irrelevant and only the
availability check survives, restoring all-cases-first semantics however the key
splits. It is zero-width, so the cursor its offsets are measured from is
unchanged. Both sides of the reduced case above now reject, and the property
tests exercise chained keys containing a `Peek` without the exclusion they
previously needed.

This makes the lowering **self-consistent**; it does not make it faithful to
ParserHawk, whose lookahead loop drops an out-of-range bit from the key rather
than rejecting. The IR cannot express that with `Peek` as it stands — availability
is baked into `eval_transition_concrete`. Matching it would mean eliding the bit
statically inside `unroll_by_cursor`, which knows the cursor and so knows which
lookaheads overrun; dropping an entry shifts every other bit's position, so
`val`/`mask` would have to be re-derived per configuration. That remains open, and
it is the last place where our lowering differs from ParserHawk by construction
rather than by accident.

## What the two have in common

Both sit in a shim on the boundary of a verified artifact — one after ParserHawk's
solver, one before our IR — and both were invisible from inside that shim. A
property test over the exporter alone would have passed Bug 3: the JSON was well
formed and internally consistent, and wrong only against `implementation()`. What
found each was an **independent implementation of the same semantics** to disagree
with: our equivalence checker for Bug 3, and for Bug 4 a reference interpreter
plus the IR's own evaluator, reached through the `run_parser` executable.

That is also the limit of the harness as it stands. It can show that our
s-expression means what `lower_table.py` intends; it cannot show that we have read
ParserHawk's JSON correctly in the first place. Only a differential against
`implementation()` would close that, and it is the natural next step — it is the
check ParserHawk itself does not have.
