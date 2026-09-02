#!/bin/sh
# Plant a bug in lower_table.py, confirm test_lower_table.py catches it, restore.
#
# A property suite that has never been shown to fail is not evidence of anything.
# The first version of these tests let three of the eight below through, and each
# survivor pointed at a blind spot in the GENERATOR rather than a missing
# property: scattered key bits never produce a multi-bit run, so MSB/LSB pattern
# order was indistinguishable; randomly drawn masks almost never overlap, so
# first-match order was unobservable; and nothing exercised --input-bits below
# the longest path, so the unroller's whole reason for existing was untested.
set -e
cd "$(dirname "$0")"
BAK=$(mktemp)
cp lower_table.py "$BAK"
trap 'cp "$BAK" lower_table.py; rm -f "$BAK"; rm -rf .hypothesis' EXIT

mut () {
  cp "$BAK" lower_table.py
  python3 - "$2" "$3" <<'PY'
import sys
p = "lower_table.py"; s = open(p).read()
old, new = sys.argv[1], sys.argv[2]
assert old in s, f"anchor not found: {old[:60]}"
open(p, "w").write(s.replace(old, new, 1))
PY
  # Independent runs: Hypothesis replays previously-failing examples from
  # .hypothesis, which would let one mutation's counterexample flatter the next.
  rm -rf .hypothesis
  printf '  %-34s ' "$1"
  if LT_MAX_EXAMPLES=${LT_MAX_EXAMPLES:-250} \
     .venv/bin/pytest test_lower_table.py -q -x --no-header \
       -p no:cacheprovider >/dev/null 2>&1
  then echo "SURVIVED  <-- gap in the tests"
  else echo "caught"
  fi
}

echo "mutation sweep (each mutation should be caught):"
mut "key bits ascending" \
    'key=lambda e: (e[1], -e[2])' 'key=lambda e: (e[1], e[2])'
mut "peek offset +1" \
    'origin = f"(Peek {off} {width})"' 'origin = f"(Peek {off + 1} {width})"'
mut "pattern LSB-first" \
    'return coq_list(["Coq_true" if (v >> (w - 1 - i)) & 1 else "Coq_false"' \
    'return coq_list(["Coq_true" if (v >> i) & 1 else "Coq_false"'
mut "rule priority reversed" \
    'for (runs, val, tgt) in reversed(decoded):' 'for (runs, val, tgt) in decoded:'
mut "unroller: no overrun check" \
    'if w and cur + w > input_bits:' 'if False:'
mut "header slice hi+1" \
    'out.append(("h", r[0][1], r[-1][2], r[0][2] + 1, pos))' \
    'out.append(("h", r[0][1], r[-1][2], r[0][2] + 2, pos))'
mut "select default -> Accept" \
    'return ("select", cases, default)' 'return ("select", cases, ("accept",))'

# BORDERLINE, reported separately: this one is very nearly an EQUIVALENT
# mutation, so "SURVIVED" here is not a gap in the tests.  Comparing a
# contiguous slice in one state and comparing its bits one at a time in a chain
# agree on which keys match -- merging is an optimisation, not semantics.  The
# only observable difference is WHEN a Peek's availability is checked, which is
# the known defect in test_known_peek_availability; once the guard-state fix
# lands this should be fully equivalent and can be deleted.
echo
echo "borderline (near-equivalent; SURVIVED is expected):"
mut "runs never merged" \
    'if cur and adjacent(cur[-1], item):' 'if False:'
