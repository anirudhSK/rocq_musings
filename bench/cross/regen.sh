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
# bench/ebpf/regen.sh for the macOS toolchain note -- a built p4c
# (`cd translation/p4c/build && make rocq p4test`) for the P4 side, and this
# repository built (`make -j && dune build --profile release`) for pretty_print.
#
# Alongside ir/, this writes a gitignored build/ holding the INPUT each front
# end actually saw, so a surprising .ir can be read against it:
#
#   build/basic_bpf.o             the BPF object handed to ect
#   build/basic_bpf.out           that object disassembled, `llvm-objdump -d`
#   build/basic_p4.frontend.p4    basic.p4 as the rocq extension receives it
#   build/basic_{bpf,p4}.pretty   each .ir as `pretty_print` renders it
#
# The .p4 comes from `p4test --top4 FrontEndLast`, which writes the program
# after p4c's last frontend pass as ordinary P4 source.  That is the same
# program `rocq` lowers: main() there runs the stock FrontEnd and then a MidEnd
# of only TypeChecking and ConstantFolding before the CoqVisitor walks it, so
# what the visitor sees is the frontend's output.  p4test is a second binary
# doing the frontend over again rather than a dump out of `rocq` itself, since
# the rocq extension emits IR and nothing else.
#
# ECT, ROCQ and P4TEST point at the submodule/build product (defaults below).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
ECT=${ECT:-$root/translation/ect}
ROCQ=${ROCQ:-$root/translation/p4c/build/rocq}
P4TEST=${P4TEST:-$root/translation/p4c/build/p4test}
src="$here/src"; out="$here/ir"; build="$here/build"; mkdir -p "$out" "$build"

[ -x "$ECT/bpf_to_ir" ] || {
  echo "no $ECT/bpf_to_ir -- git submodule update --init translation/ect" >&2
  exit 2
}
for t in "$ROCQ" "$P4TEST"; do
  [ -x "$t" ] || {
    echo "missing $t -- (cd translation/p4c/build && make rocq p4test)" >&2
    exit 2
  }
done
[ -x "$root/_build/default/extracted_code/PrettyPrint.exe" ] || {
  echo "no pretty_print -- (cd $root && make -j && dune build --profile release)" >&2
  exit 2
}

pretty () {
  (cd "$root" && dune exec --profile release pretty_print -- "$out/$1.ir") \
    >"$build/$1.pretty" || { echo "FAIL  pretty_print $1.ir" >&2; exit 1; }
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

if [ -z "${OBJDUMP:-}" ]; then
  case $LLC in
    */*) OBJDUMP=$(dirname "$LLC")/llvm-objdump ;;
    *)   OBJDUMP=llvm-objdump ;;
  esac
fi
command -v "$OBJDUMP" >/dev/null 2>&1 || {
  echo "missing $OBJDUMP -- set OBJDUMP, as with LLC (see the note above)" >&2
  exit 2
}

work=$(mktemp -d); trap 'rm -rf "$work"' EXIT

# --- eBPF: src/basic.c -> ir/basic_bpf.ir ----------------------------------
# shellcheck disable=SC2086
$CLANG -target bpf -O2 -g -I"$src" -emit-llvm -c "$src/basic.c" -o "$work/basic.o.bc" || {
  echo "FAIL  clang basic.c" >&2; exit 1; }
"$LLC" -mtriple=bpf -mcpu=probe -filetype=obj -o "$build/basic_bpf.o" "$work/basic.o.bc" || {
  echo "FAIL  llc basic.c" >&2; exit 1; }
"$ECT/bpf_to_ir" "$build/basic_bpf.o" >"$out/basic_bpf.ir" || {
  echo "FAIL  bpf_to_ir basic.c" >&2; exit 1; }
(cd "$build" && "$OBJDUMP" -d basic_bpf.o) >"$build/basic_bpf.out" || {
  echo "FAIL  llvm-objdump basic_bpf.o" >&2; exit 1; }
pretty basic_bpf
echo "ok    basic_bpf.ir"

# --- P4: src/basic.p4 -> ir/basic_p4.ir ------------------------------------
# --dump names its files <stem>-NNNN-<pass>.p4 and there is no way to ask for
# a fixed one, so the dump goes to a scratch directory and the single file it
# holds is copied out under a stable name.  Selecting FrontEndLast rather than
# dumping the whole frontend is what keeps it to one file.
d="$work/fe"; mkdir -p "$d"
"$P4TEST" --top4 FrontEndLast --dump "$d" "$src/basic.p4" >/dev/null 2>&1
fe=$(ls "$d"/*.p4 2>/dev/null | tail -1)
if [ -z "$fe" ]; then
  echo "FAIL  p4test produced no frontend dump for basic.p4" >&2; exit 1
fi
cp "$fe" "$build/basic_p4.frontend.p4"

# Just the frontend, no midend dump: basic.p4 has no tables, checksum
# control, or random() call, so it needs none of --table-entries,
# --stub-checksum, or --random-is-lo.
"$ROCQ" "$src/basic.p4" >"$out/basic_p4.ir" 2>"$work/basic_p4.log"
if grep -q 'error:' "$work/basic_p4.log"; then
  echo "FAIL  rocq basic.p4" >&2
  grep -oE 'error: .*' "$work/basic_p4.log" | head -3 | sed 's/^/      /' >&2
  exit 1
fi
pretty basic_p4
echo "ok    basic_p4.ir"
