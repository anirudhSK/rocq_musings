# Two soundness bugs in the memory model

Both come from the same gap: the solver was free to choose arbitrary `(tag, value)`
pairs for a region's contents on entry, while the IR assumes a region is a byte
array. Neither is a mistake in the soundness or completeness statements — those
are still true. What was wrong is the set of initial states we were exploring: it
included states no machine can be in, and a difference witnessed only by such a
state is not a real difference.

Both were found through loads, and only through loads. That is not a coincidence
— see [Why only loads](#why-only-loads).

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

`concrete_gp_state_is_valid` pins down regions, the tapes, the access extents and
the validity flag. It does **not** yet pin down `mod_states` — whose transformer
entries carry free state and control variables — or `sh_hdr_map`. Those are free
`SmtArithVar`s on the symbolic side with no stated concrete counterpart, so the
same class of bug is still possible there. It is much harder to trigger, because
comparison and arithmetic collapse `UninitVal` and `ErrorVal` to the same
behaviour, but the gap is real and `reachable_if_valid` remains admitted.
