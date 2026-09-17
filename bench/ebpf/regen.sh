#!/bin/bash
# Regenerate bench/ebpf/ir/*.ir from the translation/ect submodule.
#
# Each eBPF row is ONE C source compiled by clang at two optimization levels
# and translated to the IR, so each pair asks whether LLVM's optimizer
# preserved the program's meaning -- the same question the P4 rows ask of
# p4c's midend.
#
# There is no second pipeline here: `make` in translation/ect builds every
# example at -O1 and -O2 and translates both, and this script runs that make
# and copies what it wants.  translation/ect/Makefile carries the exact
# compiler flags and is the authority for how a .ir is produced.
#
# One more row, vlan_filter_mask, is not a second C source: it's a single
# in-place edit to vlan_filter's compiled bytecode (mutate_bpf.py, reusing
# ect's tests/mutate.py), expected NotEquivalent against vlan_filter_O2.  The
# rows above all expect Equivalent, and an Equivalent verdict is also what two
# runs that both merely REJECT produce, so a family with no NotEquivalent
# probe is not evidence the checker can distinguish these programs at all.
#
# Needs a clang and an `llc` WITH THE BPF TARGET -- the stock macOS toolchain
# has neither:
#
#     CLANG=/opt/homebrew/opt/llvm/bin/clang LLC=/opt/homebrew/opt/llvm/bin/llc \
#         bench/ebpf/regen.sh
#
# ECT points at the submodule (default translation/ect).
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/../.." && pwd)
ECT=${ECT:-$root/translation/ect}
src="$here/src"; out="$here/ir"; mkdir -p "$out" "$src"

[ -f "$ECT/Makefile" ] || {
  echo "no Makefile under $ECT -- git submodule update --init translation/ect" >&2
  exit 2
}
command -v python3 >/dev/null || {
  echo "no python3 -- needed for the vlan_filter_mask mutation probe" >&2
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

# One make, everything.  CLANG/LLC pass straight through if they are set.
make -C "$ECT" -j8 ${CLANG:+CLANG="$CLANG"} ${LLC:+LLC="$LLC"} all >/dev/null || {
  echo "FAIL  make in $ECT" >&2
  make -C "$ECT" ${CLANG:+CLANG="$CLANG"} ${LLC:+LLC="$LLC"} all 2>&1 | tail -20 >&2
  exit 1
}

# take <benchmark name> <path under ect/ex, without the .O<n>.ir suffix> <opt>
#
# The benchmark name carries the optimization level because that is what the
# row is about; the source keeps its upstream name.
take () {
  local name=$1 f=$2 o=$3
  [ -f "$ECT/ex/$f.$o.ir" ] || { echo "FAIL  $ECT/ex/$f.$o.ir not built" >&2; exit 1; }
  cp "$ECT/ex/$f.$o.ir" "$out/${name}_$o.ir"
  echo "ok    ${name}_$o.ir"
}

# src/ is a COPY of the sources in the submodule, refreshed here so the two
# cannot drift: bench/ is meant to hold the programs the benchmark checks in
# one place, and a stale copy would mean the .ir beside it came from something
# else.  translation/ect is the authority.
#
# Each keeps ect's filename, which is NOT always its upstream one:
#
#   xdp_pktcntr.c    dslab-epfl/ebpf-se, katran/xdp_pktcntr.c
#   cls_pktcntr.c    ... katran/adapter_integration_test_kern.c
#   map_access.c     ... fw/xdp_map_access_kern.c
#   filter.c         OISF/suricata ebpf/filter.c          **GPL-2.0-only**
#   vlan_filter.c    OISF/suricata ebpf/vlan_filter.c     **GPL-2.0-only**
#
# All five are verbatim apart from their #includes, which a per-directory shim
# header replaces so they build without a kernel tree; each file's own header
# comment says exactly what was changed.  This repository has no LICENSE file
# -- see TODO.md.
for f in ebpf-se/xdp_pktcntr.c ebpf-se/cls_pktcntr.c ebpf-se/map_access.c \
         ebpf-se/ebpf_se_common.h suricata/filter.c suricata/vlan_filter.c \
         suricata/sur_common.h; do
  cp "$ECT/ex/$f" "$src/$(basename "$f")"
done

take xdp_pktcntr ebpf-se/xdp_pktcntr O1
take xdp_pktcntr ebpf-se/xdp_pktcntr O2
take cls_pktcntr ebpf-se/cls_pktcntr O1
take cls_pktcntr ebpf-se/cls_pktcntr O2
take map_access  ebpf-se/map_access  O1
take map_access  ebpf-se/map_access  O2

take filter      suricata/filter      O1
take filter      suricata/filter      O2
take vlan_filter suricata/vlan_filter O1
take vlan_filter suricata/vlan_filter O2

# The NotEquivalent probe.  Matched by substring rather than instruction
# index: the index an optimizer assigns the mask op is not stable across
# clang/llc versions, so a hardcoded index would silently mutate the wrong
# instruction on a different toolchain instead of failing loudly.  "4095" is
# the 0x0fff mask vlan_filter.c ANDs vlan_tci with; the mutant changes it to
# 0x1000 (4096), selecting on a different bit entirely.
python3 "$here/mutate_bpf.py" "$ECT" "4095->4096" \
    "$ECT/ex/suricata/vlan_filter.O2.o" "$ECT/ex/suricata/vlan_filter_mask.O2.o" || {
  echo "FAIL  mutating vlan_filter for the mask probe" >&2; exit 1; }
make -C "$ECT" ${CLANG:+CLANG="$CLANG"} ${LLC:+LLC="$LLC"} \
     ex/suricata/vlan_filter_mask.O2.ir >/dev/null || {
  echo "FAIL  lowering vlan_filter_mask.O2.o" >&2; exit 1; }
cp "$ECT/ex/suricata/vlan_filter_mask.O2.ir" "$out/vlan_filter_mask.ir"
echo "ok    vlan_filter_mask.ir"
