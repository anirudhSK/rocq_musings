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

```
### Generate all the numbers for paper's evaluation.

# run ./regen.sh in bench/ebpf, bench/p4, and bench/parserhawk
# the eBPF translator should be in translation/ect and should only require that clang and llvm are installed
# the P4 translator should be in translation/p4c and may require you to build it
#   e.g. cd translation/p4c ; mkdir -p build ; cmake -B build ; cmake --build build
# the parserhawk translator should just be the python file in translation/parserhawk

# The paper's "Total Time" columns correspond to bench_eq's "total/ms" column
# The paper's "Load Time" column corresponds to bench_eq's "query/ms" column
# The paper's "Solve Time" column corresponds to bench_eq's "z3/ms" column
# sorry if it's confusing :/
dune exec --profile release bench_eq -- --isolate --reps 16
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
| `query/ms` | from the checker calling `solve` to Z3 being asked anything: the `lcb` precondition check, `SmtCompile` rewriting into the core fragment, `collect_arr_lens` and the region conjunct, then lowering to Z3 AST. Confusingly, this is called "Load Time" in the paper's scaling eval. |
| `z3/ms` | `Solver.check`, and reading a model back on a SAT. |
| `med/ms` | the two above together — the median over `--reps`. This is called "Total Time" in the paper's eval tables. |

`query/ms` is *our* cost, roughly linear in the term's DAG, and the thing this
project has repeatedly had to make fast — `memo-memo.txt` records a 131s → 0.01s
from one change to how the lowering memoises, which lands entirely here.
`z3/ms` is Z3's search, which is not linear in anything. Confusingly, this is called "Solve Time" in the paper's scaling eval.

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
