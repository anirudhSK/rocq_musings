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
for f in ebpf-se/xdp_pktcntr.c ebpf-se/cls_pktcntr.c ebpf-se/map_access.c \
         ebpf-se/ebpf_se_common.h suricata/filter.c suricata/vlan_filter.c \
         suricata/sur_common.h; do
  cp "$ECT/ex/$f" "$src/$(basename "$f")"
done

# dslab-epfl/ebpf-se.  -O0 is NOT usable for any of these three: the shim
# declares each helper as a function POINTER initialized to its number, and
# only -O1 and up fold that to an immediate -- at -O0 clang emits an indirect
# `call rN`, which bpf_to_ir does not model, and every map access downstream
# then loses its provenance.  See README.md.
take xdp_pktcntr ebpf-se/xdp_pktcntr O1
take xdp_pktcntr ebpf-se/xdp_pktcntr O2
take cls_pktcntr ebpf-se/cls_pktcntr O1
take cls_pktcntr ebpf-se/cls_pktcntr O2
take map_access  ebpf-se/map_access  O1
take map_access  ebpf-se/map_access  O2

# OISF/suricata.  filter.c calls helpers and so has the same -O0 limitation;
# vlan_filter.c calls none, so -O0 works and that pair is the real -O0/-O2 one.
take filter      suricata/filter      O1
take filter      suricata/filter      O2
take vlan_filter suricata/vlan_filter O2

# ... except that the Makefile only builds -O0 for ex/basic/ex0.c, since that
# is the one source the IR's own fixtures need it for.  Ask for this one
# explicitly.
make -C "$ECT" ${CLANG:+CLANG="$CLANG"} ${LLC:+LLC="$LLC"} \
     ex/suricata/vlan_filter.O0.ir >/dev/null || {
  echo "FAIL  building vlan_filter at -O0" >&2; exit 1; }
take vlan_filter suricata/vlan_filter O0
