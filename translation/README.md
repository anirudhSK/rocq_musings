# translation/ — getting other languages into the IR

Three front-ends live here. Two are submodules of their own repositories
(`p4c`, `ect`); the other is a script.

| | language | entry point |
|---|---|---|
| `p4c/extensions/rocq` | P4 | `rocq`, a p4c backend |
| `ect` | eBPF | `bpf_to_ir`, over a compiled object |
| `parserhawk/lower_table.py` | ParserHawk pipelines | the script |

All three emit an s-expression the IR can read: a
`GeneralCaracaraProgram` for the first two, a bare `Parser` for ParserHawk.
`EqCheck --net` is what compares two of them.

## `p4c/extensions/rocq` — P4

A p4c backend that lowers a P4 program to a `.ir` s-expression, written to
**stdout**. See [its README](p4c/extensions/rocq/README.md) for usage, what
lowers today, and what it refuses. Build and test:

```bash
(cd p4c/build && make rocq)     # the backend
./tests/run.sh                  # differential tests, via EqCheck
./tests/p4c_bugs/run.sh         # a real p4c miscompilation, caught
```

`p4c/` is a submodule of a p4c fork; the backend lives in its `extensions/`
directory, which CMake picks up automatically.

`tests/` holds the differential tests for the backend: pairs of P4 programs
that must lower to the same thing, each with a deliberately wrong variant as
its control. They live in the parent repository rather than in the submodule
because their *oracle* does — every one of them gets its verdict from
`EqCheck.exe` or `RunNet.exe`, which the Coq extraction builds. `tests/README.md`
has the details, `tests/differential.py` checks a lowering against p4c's own
semantics through P4Testgen.

## `ect` — eBPF

A submodule holding the eBPF front-end: `bpf_to_ir` translates a compiled BPF
object into a `GeneralCaracaraProgram`, so two lowerings of one C source — the
same program at `-O0` and at `-O2` — can be proved equivalent. `bpf_dump`
prints an object's instructions. Both are Python and need no build step; see
[its README](ect/README.md) for the program shape, what is and is not modelled,
and the map region layout.

```bash
git submodule update --init translation/ect
./ect/bpf_to_ir prog.o > prog.ir
```

Building the *example objects* needs a clang and `llc` with the BPF target,
which the stock macOS toolchain does not have. `ect`'s property tests drive the
IR's own `run_net` as their oracle, through `tests/irrunner.py`.

The `test/bpf_*.ir` fixtures in the parent repository come from here, and so do
the eBPF rows of the benchmark — `bench/ebpf/regen.sh` rebuilds them and
records the exact commands.

## `parserhawk/lower_table.py` — ParserHawk

Lowers a ParserHawk synthesized pipeline (the JSON its `codegen()` returns) to
a `Parser` s-expression. Its docstring is the reference — in particular for
`lookahead`, for the loops it admits, and for what `--input-bits` unrolls.
`mutation_sweep.sh` drives it and `test_lower_table.py` tests it;
`bench/parserhawk/regen.sh` records the flags each checked-in pipeline needs.

ParserHawk itself is not vendored: synthesizing a pipeline means running its
CEGIS loop, which is a search and can take an hour, so the JSON is an input
artifact here.
