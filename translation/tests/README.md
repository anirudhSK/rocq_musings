# translation/tests

Differential tests for the rocq p4c backend. `run.sh` lowers each `.p4` here
and checks the equivalences that should hold between them; `differential.py`
checks a program against p4c's own semantics via P4Testgen.

Every pair is followed by a deliberately wrong variant that must be reported
non-equivalent. Without that, a suite of agreeing programs would also be
satisfied by a checker that had stopped observing anything — which is not
hypothetical: the ConQuest control below came back *Equivalent* and that is how
we found that a forwarding decision was not observable at all.

A `<name>.entries` sidecar supplies table entries; a `<name>.flags` sidecar
supplies extra compiler flags, with `@ROOT@` standing for the repository root.

`deparse_direct` / `deparse_table` is the one pair here that exists to pin a
*spelling* rather than a feature. p4c's midend rewrites every control body —
a deparser included — into a `@hidden action` dispatched by a keyless
`@hidden table`, so the same deparser reads `tbl_d.apply();` after the midend.
The lowering used to walk only a deparser's top-level statements and silently
skip what it did not recognise, so that spelling emitted nothing at all. The
pair keeps both readings honest from source, without needing a midend dump; it
was found by sweeping `--excludeMidendPasses` and comparing, which is worth
re-running after any change to the deparser visitor:

```
p4test --top4 MidEnd --dump DIR prog.p4     # with a pass, and with it excluded
rocq ... DIR/<last>.p4 | EqCheck --net ...
```

## Third-party sources

Two cases are derived from [Princeton-Cabernet/p4-projects][pc], which is
**AGPL-3.0**. Each file carries the upstream copyright and licence notice.

| here | upstream | how |
|---|---|---|
| `fridge_eack*.p4` | `Fridge-tofino/p4src/calc_tcp_eack.p4` | arithmetic transcribed; the v1model harness around it is ours, since the original is a control module taking an `out bit<32>` |
| `conquest_baseline*.p4` | `ConQuest-tofino/p4src/baseline.p4` | used unmodified; the variants change only the routing expression |

**This repository has no LICENSE file.** Carrying AGPL-derived sources in it is
a licensing decision that has not been made — see the note in TODO.md.

[pc]: https://github.com/Princeton-Cabernet/p4-projects
