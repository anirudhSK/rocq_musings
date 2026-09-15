#!/bin/bash
# Regenerate bench/parserhawk/ir/*.ir from bench/parserhawk/json/*.json.
#
# The JSON is what ParserHawk's `codegen()` returns -- the synthesized parser
# PIPELINE for one target.  It is an input to this repository, not something
# produced here: regenerating a .json means re-running ParserHawk's CEGIS loop
# (`*_op.py` under z3/cegis_loop/), which is a synthesis search and can take an
# hour.  The .json files are therefore checked in as artifacts and only the
# .ir files below are regenerated.
#
# --field-sizes gives the bit width of each `field_N` the pipeline extracts,
# in index order; the JSON names fields but does not carry their widths.
#
# Usage: bench/parserhawk/regen.sh
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
lower="$root/translation/parserhawk/lower_table.py"
[ -f "$lower" ] || { echo "missing $lower" >&2; exit 2; }
out="$here/ir"; mkdir -p "$out"

gen () { # <out-name> <json> <field sizes> [extra lower_table.py args...]
  local n=$1 j=$2 fs=$3; shift 3
  python3 "$lower" --field-sizes "$fs" "$@" -o "$out/$n.ir" "$here/json/$j" \
    || { echo "FAIL  $n"; exit 1; }
  echo "ok    $n.ir"
}

gen icmp_ipu          icmp_ipu.json          16,1
# The Tofino pipeline for Multi-keys LOOPS.  --input-bits unrolls it on
# (node, cursor) against a packet of that length, which is what makes it
# comparable to the spec: without it the parser is emitted as a loop whose
# termination depends on an input length nothing here has fixed.  17 bits is
# the longest path of the IPU pipeline and of the spec, so it is the length
# all three are about.
gen multifield_tofino multifield_tofino.json 8,8,1 --input-bits 17
gen multifield_ipu    multifield_ipu.json    8,8,1
gen sai_tofino        sai_v4_tofino.json     1,16,8,8,8,1,1,1,1

# test/parserhawk holds the same four files, because TestEquality's expect
# tests read them from there; keep the two copies identical rather than
# letting them drift.
for f in "$out"/*.ir; do
  cp "$f" "$root/test/parserhawk/$(basename "$f")"
done
echo "ok    copied into test/parserhawk (TestEquality reads them there)"
