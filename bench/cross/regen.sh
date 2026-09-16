#!/bin/bash
# Regenerate bench/cross/ir/*.ir from bench/cross/src/{basic.c,basic.p4}.
#
# Unlike bench/ebpf/regen.sh and bench/p4/regen.sh, which mirror sources out
# of a submodule into src/, bench/cross/src IS the source: one XDP program
# and one P4 program, written here to say the same thing (parse an Ethernet
# header, pass IPv4, drop everything else), each run through its own front
# end -- ect for basic.c, the rocq extension in translation/p4c for basic.p4.
#
# ect and the rocq extension declare their own, unrelated memory regions and
# header interfaces for that same intent, so basic_bpf.ir and basic_p4.ir are
# NOT yet comparable by the equivalence checker (no shared header/region
# naming between the two front ends exists). This script only produces the
# two .ir files; wiring a pair into bench_eq is separate follow-up work.
#
# Needs a clang and an `llc` WITH THE BPF TARGET for the eBPF side -- see
# bench/ebpf/regen.sh for the macOS toolchain note -- and a built p4c
# (`cd translation/p4c/build && make rocq`) for the P4 side.
#
# ECT and ROCQ point at the submodule/build product (defaults below).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
ECT=${ECT:-$root/translation/ect}
ROCQ=${ROCQ:-$root/translation/p4c/build/rocq}
src="$here/src"; out="$here/ir"; mkdir -p "$out"

[ -x "$ECT/bpf_to_ir" ] || {
  echo "no $ECT/bpf_to_ir -- git submodule update --init translation/ect" >&2
  exit 2
}
[ -x "$ROCQ" ] || {
  echo "missing $ROCQ -- (cd translation/p4c/build && make rocq)" >&2
  exit 2
}

if [ -z "${CLANG:-}" ]; then
  mularch=$(clang -print-multiarch 2>/dev/null || true)
  if [ -n "$mularch" ] && [ -d "/usr/include/$mularch" ]; then
    CLANG="clang -isystem /usr/include/$mularch"
    case "$mularch" in
      x86_64-linux-gnu) CLANG="$CLANG -D__x86_64__" ;;
    esac
  fi
fi
CLANG=${CLANG:-clang}
LLC=${LLC:-llc}

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT

# --- eBPF: src/basic.c -> ir/basic_bpf.ir ----------------------------------
# shellcheck disable=SC2086
$CLANG -target bpf -O2 -g -I"$src" -emit-llvm -c "$src/basic.c" -o "$work/basic.o.bc" || {
  echo "FAIL  clang basic.c" >&2; exit 1; }
"$LLC" -mtriple=bpf -mcpu=probe -filetype=obj -o "$work/basic.o" "$work/basic.o.bc" || {
  echo "FAIL  llc basic.c" >&2; exit 1; }
"$ECT/bpf_to_ir" "$work/basic.o" >"$out/basic_bpf.ir" || {
  echo "FAIL  bpf_to_ir basic.c" >&2; exit 1; }
echo "ok    basic_bpf.ir"

# --- P4: src/basic.p4 -> ir/basic_p4.ir ------------------------------------
# Just the frontend, no midend dump: basic.p4 has no tables, checksum
# control, or random() call, so it needs none of --table-entries,
# --stub-checksum, or --random-is-lo.
"$ROCQ" "$src/basic.p4" >"$out/basic_p4.ir" 2>"$work/basic_p4.log"
if grep -q 'error:' "$work/basic_p4.log"; then
  echo "FAIL  rocq basic.p4" >&2
  grep -oE 'error: .*' "$work/basic_p4.log" | head -3 | sed 's/^/      /' >&2
  exit 1
fi
echo "ok    basic_p4.ir"
