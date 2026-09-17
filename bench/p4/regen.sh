#!/bin/bash
# Regenerate bench/p4/ir/*.ir from bench/p4/src/*.p4.
#
# Every P4 row of the benchmark is ONE source compiled twice: once as the
# rocq extension sees it straight from the frontend, and once after p4c's
# midend has rewritten it.  Nothing here needs a second compiler or a historic
# checkout -- `p4test --top4 MidEnd --dump DIR` writes the program after each
# midend pass as ORDINARY P4 SOURCE, so the interchange format between p4c's
# internals and this backend is P4 itself.  The rocq extension runs just after
# the FRONTEND and never sees the midend, which is why --excludeMidendPasses
# is passed to p4test and not to rocq.
#
# Usage: bench/p4/regen.sh          (from anywhere)
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
rocq="$root/translation/p4c/build/rocq"
p4test="$root/translation/p4c/build/p4test"
for t in "$rocq" "$p4test"; do
  [ -x "$t" ] || { echo "missing $t -- (cd translation/p4c/build && make rocq p4test)" >&2; exit 2; }
done
src="$here/src"; out="$here/ir"; mkdir -p "$out" "$src"

# src/ is a COPY of sources that live elsewhere in this repository, refreshed
# here so the two cannot drift: bench/ is meant to hold the programs the
# benchmark checks in one place, and a stale copy would mean the .ir beside it
# came from something else.  The originals are the authority.
#
# Where they came from before that:
#
#   basic qos basic_tunnel multicast   p4lang/tutorials, via test/p4tutorials
#   conquest_baseline.p4               Princeton-Cabernet/p4-projects,
#                                      ConQuest-tofino/p4src/baseline.p4,
#                                      used UNMODIFIED.  **AGPL-3.0**, and this
#                                      repository has no LICENSE file -- see
#                                      TODO.md.
#   issue5765.p4                       written here, a reducer for
#                                      p4lang/p4c issue #5765
#
# The *.entries files are table configurations: a table the source does not
# populate itself takes its entries from one, passed to rocq --table-entries.
for f in test/p4tutorials/basic.p4 test/p4tutorials/qos.p4 \
         test/p4tutorials/basic_tunnel.p4 test/p4tutorials/multicast.p4 \
         test/p4tutorials/ipv4_lpm.entries test/p4tutorials/basic_tunnel.entries \
         test/p4tutorials/multicast.entries \
         translation/tests/conquest_baseline.p4 \
         translation/tests/p4c_bugs/issue5765.p4; do
  cp "$root/$f" "$src/$(basename "$f")"
done
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
: > "$work/empty.entries"

TNA="-D__TARGET_TOFINO__=1 -I$root/translation/p4c/backends/tofino/bf-p4c/p4include"

# lower <out-name> <source.p4> <rocq flags...>
lower () {
  local name=$1 f=$2; shift 2
  "$rocq" "$@" "$f" 2>"$work/$name.log" >"$out/$name.ir"
  if grep -q 'error:' "$work/$name.log"; then
    echo "FAIL  $name"; grep -oE 'error: .*' "$work/$name.log" | head -3 | sed 's/^/      /'; exit 1
  fi
  echo "ok    $name.ir"
}

# midend <out-name> <source.p4> <excluded passes or -> <p4test flags> -- <rocq flags...>
midend () {
  local name=$1 f=$2 ex=$3; shift 3
  local pflags=""
  while [ "$1" != "--" ]; do pflags="$pflags $1"; shift; done
  shift
  local d="$work/d.$name"; rm -rf "$d"; mkdir -p "$d"
  if [ "$ex" = "-" ]; then
    # shellcheck disable=SC2086
    "$p4test" $pflags --top4 MidEnd --dump "$d" "$f" >/dev/null 2>&1
  else
    # shellcheck disable=SC2086
    "$p4test" $pflags --excludeMidendPasses "$ex" --top4 MidEnd --dump "$d" "$f" >/dev/null 2>&1
  fi
  local last
  last=$(ls "$d" | grep '\.p4$' | tail -1)
  [ -z "$last" ] && { echo "FAIL  $name: p4test produced no midend dump"; exit 1; }
  lower "$name" "$d/$last" "$@"
}

T="--stub-checksum --random-is-lo"

# --- p4lang/tutorials -------------------------------------------------------
# The synthesized @hidden tables the midend introduces have no entries of their
# own and only a default action, which an empty configuration says exactly; the
# program's real table takes ipv4_lpm.entries.
for n in basic qos basic_tunnel multicast; do
  ent="$src/ipv4_lpm.entries"
  [ -f "$src/$n.entries" ] && ent="$src/$n.entries"
  # shellcheck disable=SC2086
  lower  "${n}_src"    "$src/$n.p4" $T --table-entries "$ent"
  # shellcheck disable=SC2086
  midend "${n}_midend" "$src/$n.p4" - -- $T --table-entries "$ent"
done

# --- Princeton-Cabernet ConQuest -------------------------------------------
# Two passes are excluded, and both are limitations of THIS LOWERING rather
# than of p4c:
#
#   HandleNoMatch   puts `verify(false, error.NoMatch)` into the parser, and
#                   the parser lowering accepts only extract and advance.
#   EliminateTuples rewrites the checksum's tuple literal into a `tuple_0`
#                   struct declared AHEAD of the header struct.  Header uids
#                   are assigned in declaration order and the checker gives
#                   the two compared programs ONE shared free register per
#                   uid, so sixteen extra declarations shift every later field
#                   and force ConQuest's ethernet.dst_addr to equal the other
#                   program's tuple_0.f0.  With the pass in, the pair reports
#                   NotEquivalent on that misalignment rather than on any
#                   behaviour.  The fix is a name-to-uid sidecar shared by both
#                   lowerings; excluding the pass is the workaround.
# shellcheck disable=SC2086
lower  conquest_src    "$src/conquest_baseline.p4" $TNA --stub-checksum --table-entries "$work/empty.entries"
# shellcheck disable=SC2086
midend conquest_midend "$src/conquest_baseline.p4" HandleNoMatch,EliminateTuples \
       $TNA -- $TNA --stub-checksum --table-entries "$work/empty.entries"

# --- p4lang/p4c issue #5765 -------------------------------------------------
# The same source compiled twice by the same p4c, once with the whole midend
# and once with GlobalCopyPropagation excluded, so a NotEquivalent verdict is a
# statement about that PASS rather than about two spellings of a program.
# shellcheck disable=SC2086
midend issue5765_gcp   "$src/issue5765.p4" -                      -- $T --table-entries "$work/empty.entries"
# shellcheck disable=SC2086
midend issue5765_nogcp "$src/issue5765.p4" GlobalCopyPropagation  -- $T --table-entries "$work/empty.entries"
