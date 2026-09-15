#!/bin/bash
# Catch a real p4c miscompilation with the equivalence checker.
#
# The method needs no second compiler, which is the point.  A miscompiling
# optimization pass does not have to be reproduced by checking out an old p4c:
# it is enough to run the SAME compiler with the pass on and with it off, and
# ask whether the two results agree.
#
# Getting at "p4c's midend output" turns out to need no plumbing either.
# `--top4 MidEnd --dump DIR` writes the program after each midend pass as
# ORDINARY P4 SOURCE, so the interchange format between p4c's internals and
# this backend is P4 itself.  That is also the answer for a historic bug: run
# the old p4c far enough to dump, then lower the dump with today's extension.
#
# What this does NOT need is for the backend to sit inside p4c's midend.  It
# does not -- rocq runs just after the frontend -- so `--excludeMidendPasses`
# passed to rocq does nothing at all.  Passing it to p4test is what matters.
#
# Usage: translation/tests/p4c_bugs/run.sh

set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../../.." && pwd)
rocq="$root/translation/p4c/build/rocq"
p4test="$root/translation/p4c/build/p4test"
eqcheck="$root/_build/default/extracted_code/EqCheck.exe"
runnet="$root/_build/default/extracted_code/RunNet.exe"
work=$(mktemp -d); trap 'rm -rf "$work"' EXIT
fail=0

for t in "$rocq" "$p4test" "$eqcheck" "$runnet"; do
  [ -x "$t" ] || { echo "missing $t" >&2; exit 2; }
done

# --- #5765: GlobalCopyPropagation, stale constant across an out argument ----
src="$here/issue5765.p4"
mkdir -p "$work/on" "$work/off"
"$p4test" --top4 MidEnd --dump "$work/on"  "$src" >/dev/null 2>&1
"$p4test" --excludeMidendPasses GlobalCopyPropagation \
          --top4 MidEnd --dump "$work/off" "$src" >/dev/null 2>&1

on=$(ls "$work"/on/*.p4 2>/dev/null | tail -1)
off=$(ls "$work"/off/*.p4 2>/dev/null | tail -1)
if [ -z "$on" ] || [ -z "$off" ]; then
  echo "FAIL  p4test produced no midend dump"; exit 1
fi

# The synthesized tables the midend introduces have no entries of their own and
# only a default action, which an empty configuration says exactly.
: > "$work/empty.entries"
for v in on off; do
  eval "f=\$$v"
  "$rocq" --random-is-lo --table-entries "$work/empty.entries" "$f" \
      2>"$work/$v.log" >"$work/$v.ir"
  if [ "$(grep -c 'error:' "$work/$v.log")" != "0" ]; then
    echo "FAIL  could not lower the $v dump"
    grep -oE 'error: .*' "$work/$v.log" | head -3 | sed 's/^/        /'
    exit 1
  fi
done

got=$("$eqcheck" --net "$work/on.ir" "$work/off.ir" 2>&1 | tail -1)
if [ "$got" = "Not Equivalent" ]; then
  echo "ok    issue5765        the checker separates the two compilations"
else
  echo "FAIL  issue5765        got '$got', want 'Not Equivalent'"
  echo "      If this now says Equivalent, the p4c in translation/p4c has been"
  echo "      updated with the fix -- which is the good outcome, not a broken"
  echo "      test.  Confirm against the issue and retire this case."
  fail=1
fi

# The verdict alone does not say WHICH way it is wrong, so show it.
b=$("$runnet" "$work/on.ir"  "pkt:0000000000000000" 2>&1 | head -1)
c=$("$runnet" "$work/off.ir" "pkt:0000000000000000" 2>&1 | head -1)
echo "        with the pass:    $b   <- hdr.h.res is the stale 100"
echo "        without the pass: $c   <- hdr.h.res is what random wrote"

exit $fail
