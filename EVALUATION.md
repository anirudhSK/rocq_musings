# Evaluation: what is checked, and what it costs

Every equivalence query the evaluation can run is registered in
`extracted_code/BenchEq.ml`, one line per case. `bench_eq` runs them, times
them, and reports how big each program was, so the table in the paper is
generated rather than transcribed.

```
dune exec bench_eq -- --list                  # the registry, run nothing
dune exec bench_eq -- --reps 5 --csv out.csv  # time everything
dune exec bench_eq -- --family P4             # one family
dune exec bench_eq -- --case katran           # one case, by substring
```

## What is timed

The **check only**. Building both programs happens once before the clock
starts and is reported separately as `build_ms`: reading and parsing an
s-expression, generating a TSS pair in Rocq, or — for P4 — running the p4c
rocq extension, which is why those `build_ms` figures are seconds. The checker
then runs `--reps` times over the same two in-memory programs and the
**median** is reported, with min and max alongside, because Z3's time on one
query varies run to run. Use `--reps 1` for a sweep and more when a number is
going into a table.

### Building the query versus solving it

The check time is split further, because it is two costs with different
characters and reporting only their sum says which is which for neither:

| column | what |
|---|---|
| `load/ms` | reading the programs in. Not part of a check; reported apart from it. For P4 this is the p4c extension running, hence seconds. |
| `query/ms` | from the checker calling `solve` to Z3 being asked anything: the `lcb` precondition check, `SmtCompile` rewriting into the core fragment, `collect_arr_lens` and the region conjunct, then lowering to Z3 AST. |
| `z3/ms` | `Solver.check`, and reading a model back on a SAT. |
| `med/ms` | the two above together — the median over `--reps`. |

`query/ms` is *our* cost, roughly linear in the term's DAG, and the thing this
project has repeatedly had to make fast — `memo-memo.txt` records a 131s → 0.01s
from one change to how the lowering memoises, which lands entirely here.
`z3/ms` is Z3's search, which is not linear in anything.

`SolveTime` accumulates per `solve` call and `Z3Solver.solve` stamps a clock at
each phase boundary, so the marks tile the whole call with no gaps. Unlike
`SmtSize` it is always on: a handful of `gettimeofday` calls against a query
measured in milliseconds costs nothing, and a measurement only available in a
special mode is one nobody takes. The breakdown reported is from the run whose
time was the **median**, so the parts and the total on a row describe the same
execution rather than being separately averaged into disagreement.

The CSV carries each phase separately (`lcb_ms`, `compile_ms`, `collect_ms`,
`lower_ms`) for when the question is which part of the build is slow.

## Reading a verdict

Every case carries the verdict it must produce, and a case that reports
anything else is marked `BAD` and exits non-zero. A timing for a query that
answered the wrong question is not worth quoting.

This matters more than it sounds. `Equivalent` is also what two programs that
both *stopped running* produce — the comment on the vlan_filter pair records
exactly that happening, when a context-layout bug made every access overrun
the region and both sides reject. So the registry deliberately pairs each
`Equivalent` claim with a **probe**: a perturbed variant that must come back
`NotEquivalent`, showing the program's behaviour is observable at all. A table
of `Equivalent` rows with no probes is not evidence.

## Size columns

Two different sizes, because they answer different questions.

**`IrSize`** walks the same in-memory program handed to the checker: the
`Nm/Nr/Np/No` column is modules, transformer rules, parser states, and total
operations. The CSV carries all 20 metrics per side (`a_*`, `b_*`), including
`hdr_ops`, `mem_ops`, `match_terms`, `regions` and `region_bytes`. This
describes the *input*.

**`SmtSize`** measures the formula that actually reaches Z3, recorded at the
one point every query funnels through (`Z3Solver.solve`) after `SmtCompile`
has rewritten it into the core fragment. This describes the *work*.

The `smt` column is `smt_dag`: **distinct** subterms, compared by physical
identity. That is what Z3 effectively sees, because the lowering memoizes on
exactly that notion of identity (`PhysTbl`) and hash-conses as it goes.

The CSV also carries `smt_tree`, the same term counted as if unfolded, and
`smt_sharing`, their ratio. Do not quote `smt_tree` as a size: symbolic
execution of a branchy program shares aggressively, and the ratio reaches
**8×10¹³** on the larger eBPF cases. The tree number is there only to show how
much of the apparent size is sharing; `smt_dag` is the honest one.

Measuring costs a walk of the DAG, so it is off by default. `bench_eq` does
one extra **untimed** run with it on, then turns it off before the clock
starts — a size measurement never lands in a reported time.

### Run each case alone

Cases share a process, and Z3's state does not fully reset between queries, so
a case's time depends on what ran before it. This is not a small effect:
`map-update-probe` measured 237 ms and 1859 ms in two batch runs either side of
an unrelated change, while alone it was within 20% of 2 s both times. The batch
numbers were the artefact, in both directions.

**Any number going into a table wants `--isolate`**, which re-runs each case in
a fresh process and collects its CSV row. It is slower and it is the only mode
whose timings mean anything across runs.

### Which size predicts the timing?

Over all 49 cases, `smt_dag` correlates with median time at r ≈ +0.31 and
`IrSize` ops at r ≈ +0.18. Restricted to `Equivalent` verdicts, both improve
sharply — r ≈ +0.62 and +0.40.

So: the SMT size is the better predictor, and neither is good until the
verdicts are separated. That split is the real structure in the data, and a
table that mixes verdicts in one column hides it.

---

# The four families

## TSS — packet classification

`PktClass.v` builds two programs from one filter database: `linear_db`, a
linear scan tracking match priority, which is the specification; and `tss_db`,
tuple space search over the same database. They must classify identically for
every 192-bit packet.

| case | database |
|---|---|
| `tss-simple` | `SimpleDB`, 3 filters, hand-written |
| `tss-overlap` | `OverlapDB` — filters that overlap but have different tuple shapes |
| `tss-distinct` | `DistinctDB` — the priority-arbitration case |
| `tss-gen-1/2/4/8` | generated, seed 1, for the size sweep |

The generated rows are where the scaling shows: across 1, 2, 4 and 8 filters
the check grows faster than the database does — in one 5-rep run on a laptop,
roughly 33, 44, 76 and 215 ms. Re-measure before quoting; these move with the
machine and with Z3's run-to-run variance. They use the same generator as the
fuzz campaign, which carries
its own splitmix64 rather than `Random`, so a seed reproduces across OCaml
versions.

**The campaign is a separate thing.** `bench_eq` times *one* query; the claim
that the two agree for *every* database is approached by sampling, which is
`dune exec fuzz_tss -- --seed S --count N --size 1,2,4,8`. Its `--mutate` flag
is the campaign's own control (every observable database must come back
`NotEquivalent`) and `--prec` reports how many databases actually exercise
priority arbitration rather than single-filter matching. If the paper quotes a
campaign, quote those too — a campaign of vacuous `Equivalent` verdicts is the
same trap as above, one level up.

## ParserHawk — synthesized parser pipelines

ParserHawk emits a hardware pipeline for a parser spec. Two questions: does a
synthesized pipeline agree with the spec it came from, and do the pipelines
for two targets agree with each other. `ParserHawkEval.dump_headers` wraps a
pipeline into the network that emits the named headers, which is what makes
two pipelines comparable.

| case | pair | verdict |
|---|---|---|
| `ph-icmp` | Parse icmp: spec vs IPU pipeline | Equivalent |
| `ph-sai` | Sai V2: spec vs Tofino pipeline | Equivalent |
| `ph-ethernet-cross` | ethernet: Tofino vs IPU | Equivalent |
| `ph-multifield-tofino` | Multi-keys: spec vs Tofino | Equivalent |
| `ph-multifield-ipu` | Multi-keys: spec vs IPU | **NotEquivalent** |
| `ph-multifield-cross` | Multi-keys: Tofino vs IPU | **NotEquivalent** |

The last two are **the finding, not a failure**. ParserHawk's Z3 model was
right and its JSON writer dropped a lower-bound check on a node's transition
rules, so the emitted IPU pipeline carries transition edges the model never
had. A run where these come back `Equivalent` means the artifact was
regenerated with the bug fixed, and the registry should be updated to say so.

Note the asymmetry in what exists: `icmp` has only an IPU artifact and `sai`
only a Tofino one, so neither has a cross-target row.

## eBPF — two lowerings of one program

Programs come from eBPF-SE's examples (Katran) and Suricata, translated by
`~/proj/ect/bpf_to_ir`.

**Self pairs** are the end-to-end claim that a real program translates and
checks. The query is still universally quantified over every input, so it is
not trivial, but it cannot fail for a reason specific to the program — it is
what a program of that size costs.

| program | self | probe |
|---|---|---|
| Katran `xdp_pktcntr.c` | `katran-xdp-self` | `katran-xdp-probe` — counter incremented by 2 |
| Katran `adapter_integration_test_kern.c` | `katran-cls-self` | `katran-cls-probe` — `TC_ACT_SHOT` on the unset flag |
| Suricata `filter.c` | `suricata-filter-self` | `suricata-filter-probe` — DADDR branch returns 7 |
| Suricata `vlan_filter.c` | `suricata-vlan-self` | `suricata-vlan-probe` — a different VLAN set |

`suricata-filter` is the widest single test of the translator: two map
lookups, a store through a returned value pointer, LD_ABS and LD_IND packet
reads, and a ctx store.

Other eBPF rows:

- `bpf-O0-O2` — the same C compiled at `-O0` and `-O2`. This is the real
  cross-lowering equivalence, and the one closest to what the IR is for.
- `bpf-load-split` — a u16 load against the two u8 loads it coalesces from.
- `vlan-mut-*` — single in-place *bytecode* edits, one preserving and two
  observable. Source-level variants only exercise differences clang happens to
  emit; these are chosen.
- `map-*` — a lookup against the same lookup spilled through the stack, with a
  probe for each arm. All three return a constant on every path, so a checker
  comparing only the emitted packet would call them equivalent; what separates
  them is the map region.

## P4 — lowered by the p4c rocq extension

Each case is two source programs that must lower to the same function of the
input, with a deliberately-wrong variant as the control. The pairs come from
`translation/tests/run.sh`; `bench_eq` lowers them itself (honouring the
`.flags` and `.entries` sidecars) so lowering and timing live in one place.

Between them they cover expression lowering (`p4-rotl`), predication and
metadata threading (`p4-fridge-eack`), match-action tables and their entry
ordering (`p4-table-*`), the Tofino-native architecture (`p4-tna-rotl`), the
derived `isValid()` predicate (`p4-valid-merge`), `exit` (`p4-exit`), and slice
assignment (`p4-slice-assign`).

Lowering costs ~2.4–6.3 s per program and is reported in `build_ms`, separate
from the check.

---

# Gaps

Things worth knowing before building a table around this.

### The P4 application programs are not here

The rocq extension's README surveys what lowers:
**5 of 13** p4lang/tutorials — `basic`, `qos`, `ecn`, `basic_tunnel`,
`multicast` — and **1 of 19** Princeton-Cabernet/p4-projects,
`ConQuest/baseline`.

Neither repository is vendored here or checked out on this machine, so none of
those six are in the registry; every P4 row above is a micro-test from
`translation/tests`. Adding them needs two things:

1. The sources. `git clone` both repos and point the registry at them.
2. **A second program to compare against** — the harder half. Lowering
   produces *one* IR program, and an equivalence check needs a pair. The
   micro-tests solve this by being written in pairs. For an application
   program the options are: lower it twice under different compiler flags (the
   analogue of the eBPF `-O0`/`-O2` row); lower it and check against a
   hand-written spec (what ParserHawk does); or perturb it and check the
   perturbation is observable (a probe, which is evidence the lowering is not
   vacuous but is not an equivalence result).

Until that is decided, "5 of 13 tutorials lower" is a *lowering* claim, not an
*equivalence-checking* claim, and the paper should not blur the two.

### `fw/xdp_map_access_kern.c` is excluded

It uses the constant map key 23, and the model can only represent a key below
`--map-slots` without folding it onto another key's entry, so at the default
of 4 the translator refuses it rather than aliasing silently. That refusal is
TODO.md 1.6, which is about replacing the slot mapping with an uninterpreted
function.

The *cost* half of that entry is now fixed. `--map-slots=32` translates it into
a 288-cell region, and comparing the pair took **175 s**, of which 179/180 was
`Solver.check` — not model extraction, which was 0.01 s. The cause was
`SmtCompile.region_bytes_wf` unrolling `cell_is_byte` over every cell: 372
cells x 2 conjuncts = 744 forced `select` terms. Narrowing a cell's value field
to eight bits (below) brought it to **11 s**.

The `map-*` rows in the registry are the hand-written `ex/map/` programs, not
this one. Adding it needs the key model fixed, not the cost.

### NotEquivalent can cost far more than Equivalent

`katran-cls-probe` takes ~5.1 s against ~120 ms for the self pair on the same
programs — a 40×-plus difference, and the largest single timing in the
registry. Z3 finding and exhibiting a counterexample is a different problem
from proving there is none. If the table mixes verdicts in one column, this
will look like noise and is not.

### Sizes are syntactic

`IrSize` counts IR syntax and predicts solve time poorly (r ≈ +0.18); the
largest program in the registry (`suricata-filter`, 146 ops) checks in a few
hundred ms while `katran-cls-probe` at 54 ops takes ~5 s. `smt_dag` is better
(r ≈ +0.31, and +0.62 within `Equivalent`), which is why it is now reported.

But it does not close the gap, and the clearest case says why.
`katran-cls-self` and `katran-cls-probe` build formulas of almost identical
size — 15612 and 15862 distinct subterms — and take ~105 ms and ~4.8 s. A 1.6%
difference in the formula, a 45× difference in the time. Nothing structural
about the query explains that: what changed is that one is unsatisfiable and
the other has a model Z3 has to find and exhibit.

So quote `smt_dag` as the size, but do not present either number as *the*
explanation of the timings. The honest statement is that size explains solve
time only within a verdict class, and that the verdict matters more than the
size does.


---

# A cell is a byte

`CrVal.st_arr` and `CrVal.st_cell` used to store an arbitrary `CrVal`. Every
*reachable* store already wrote a byte — `st_val` writes `byte_of_val`, which
ends in `cast u64 u8` — so the invariant held by reachability, and `CrVal.v`
said so in prose ("A region is an array of BYTES") without anything enforcing
it.

`CrVal.to_cell` now enforces it: an integer of any width is masked into a byte,
and `ErrorVal` / `UninitVal` pass through. `to_cell_byte_of_val` proves it is
the identity on everything `byte_of_val` produces, so no reachable store
changed and no program's behaviour changed.

What it buys is in the solver. `Z3Solver` encodes a cell in `tag_bits + 8`
rather than `tag_bits + 64` bits, which makes the "value < 256" half of
`cell_is_byte` true by construction at every index — so that conjunct is gone
from `SmtCompile.v` rather than being asserted `len` times per region. Dropping
it weakens the asserted formula, which is the safe direction: a weaker
constraint admits more models, so a query can only become satisfiable, never
less so, and a false `Equivalent` is what a validator must never produce.

`pack_cell` mirrors `to_cell` on the tag too — `to_cell` sends an `IntVal` of
any width to a `u8`, so a tag of 2..5 becomes 2 while `UninitVal` (1) and
`ErrorVal` (0) pass through. Getting that wrong would leave the lowering
claiming a cell is a `u64` whose value had been truncated, which is not a
`CrVal` the semantics can produce.

Measured with `--isolate`, verdicts unchanged on all 49 registry cases:

| case | before | after | |
|---|---|---|---|
| `map_access` (fw, 288-cell region) | 175 s | 11.2 s | 15.6x |
| `katran-cls-probe` | 5311 ms | 1259 ms | 4.2x |
| `map-update-probe` | 2092 ms | 1739 ms | 1.2x |
| `suricata-vlan-probe` | 64 ms | 27 ms | 2.4x |

The whole Rocq development rebuilds with no new axioms; the only `Admitted` is
the pre-existing `eval_general_program_commute`.

## What did not work

Three other approaches to the same conjunct, for the record:

- **A quantifier** — one `forall i. i < len -> cell_is_byte` per region instead
  of the unrolling: **572 s**, over 3x worse. Z3's instantiation over an array
  quantifier costs more than the unrolled form.
- **A lambda-built region** — `\i. concat(u8_tag, zext(byte[i]))`, so
  well-formedness holds by construction with no constraint at all: 0.75 s, but
  the verdict came back **Unknown**. Lambdas push the query out of Z3's
  decidable array fragment. A fast wrong answer is not an answer.
- **Constraining only the indices the query mentions** — every index in that
  query is symbolic, not constant, so there is nothing to narrow to.
