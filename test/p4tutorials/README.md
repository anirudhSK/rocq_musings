# p4tutorials

The five p4lang/tutorials programs the rocq backend can lower, each with a
semantics-preserving source variant, and the `.ir` both compile to.

| | |
|---|---|
| `<name>.p4` | the tutorial program, unmodified |
| `<name>_alt.p4` | a variant that should behave identically |
| `<name>.ir`, `<name>_alt.ir` | what they lower to |
| `*.entries` | the table configuration both sides run |

Regenerate with:

```bash
rocq --stub-checksum --table-entries <entries> <name>.p4 > <name>.ir
```

## What each pair exercises

The variants were chosen to hit different parts of the lowering rather than to
be five of the same rewrite.

- **basic** — the MAC swap goes through a temporary, and `ttl - 1` is written
  `ttl + 255`. TTL is `bit<8>` and P4 arithmetic on it is mod 2⁸, so those are
  the same only if the lowering masks to the declared width.
- **qos** — an `else if` chain flattened into independent `if`s with explicit
  guards, so the second condition is a conjunction carried into the rule
  rather than obtained from rule order.
- **basic_tunnel** — a conjunction written as nesting and a negation as an
  `else`. `hdr.ipv4` is reached two ways by the parser, so its validity is a
  disjunction over parse paths and the pair checks both spellings agree on it.
- **multicast** — an `isValid()` guard removed. The parser extracts ethernet
  on its only path, so the guard is vacuous — a claim about the validity
  derivation, checked rather than assumed.
- **ecn** — `ecn == 1 || ecn == 2` against `ecn != 0 && ecn != 3`, the same set
  for a `bit<2>`. **This pair is expected to report NotEquivalent**; see below.

## Two caveats these fixtures carry

**They need `--stub-checksum`,** so the emitted packet carries a stale IPv4
checksum. Sound here only because both sides of every pair are stubbed the
same way. `update_checksum` is a ones-complement sum and is unimplemented.

**`ecn` is a known-failing witness, not a passing test.** It reports
NotEquivalent because `ecn.p4` reads `hdr.ipv4.ecn` without an `isValid()`
guard, and a header is seeded at its *container's* width rather than its
declared one — so on a non-IPv4 packet the `bit<2>` field can come back 252.
TODO.md 1.9 has the diagnosis and the fix; this pair should start reporting
Equivalent when that lands.

## Configurations

All five have runtime-populated tables, which cannot be left to the control
plane: a `Ctrl` variable is seeded per program, so two programs being compared
would get unrelated configurations and the solver would satisfy "the outputs
differ" by handing them different tables (TODO.md 1.7). The entries here are
transcribed from the tutorials' own `sN-runtime.json` topologies rather than
invented — switch s1 of the triangle topology for `ipv4_lpm`, and of
`sig-topo` for `multicast` — so these correspond to a configuration the
upstream tests actually use.
