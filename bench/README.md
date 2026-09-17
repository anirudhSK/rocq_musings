# bench/

The programs the equivalence benchmark checks. Every case reads a `.ir` file from here, and the compilers that produced those files (p4c, clang, ParserHawk) are needed only to *regenerate* them.

```
bench/
  p4/          p4lang/tutorials, Princeton-Cabernet ConQuest, a p4c bug
  ebpf/        dslab-epfl/ebpf-se, OISF/suricata
  parserhawk/  synthesized parser pipelines
```

There are `regen.sh` files in each subdir to rebuild the `ir/` files from their sources.

Run the benchmark with

```
dune exec --profile release bench_eq -- --reps 3 --csv results.csv
```

and see `extracted_code/BenchEq.ml` for the registry, which which programs are compared and what verdict we expect.

Submodules the scripts use:

```
git submodule update --init translation/p4c translation/ect
```
