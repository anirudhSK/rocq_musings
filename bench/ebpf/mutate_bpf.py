#!/usr/bin/env python3
"""Apply one named bytecode mutation from ect's tests/mutate.py to a .o file.

Single in-place instruction edit, same length, no relocation to fix up --
see mutate.py's own docstring for why this is worth having alongside the
compiler-generated O1/O2 pairs in bench/ebpf/regen.sh: it's a difference a
compiler would never produce.

Usage: mutate_bpf.py <ECT dir> <label substring> <in.o> <out.o>

<label substring> selects a mutation by matching against the labels
mutate.mutations() yields (e.g. "4095->4096" for an ALU immediate changing
from 0xfff to 0x1000).  Instruction INDICES in those labels are not stable
across toolchain versions, so this matches by substring and fails loudly,
listing every label seen, unless exactly one matches -- silently mutating
the wrong instruction would be worse than not mutating at all.
"""
import os
import sys


def main():
    if len(sys.argv) != 5:
        raise SystemExit("usage: mutate_bpf.py <ECT dir> <label substring> "
                          "<in.o> <out.o>")
    ect, needle, src, dst = sys.argv[1:5]
    sys.path.insert(0, ect)
    sys.path.insert(0, os.path.join(ect, "tests"))
    from mutate import mutations

    blob = open(src, "rb").read()
    all_mutations = list(mutations(blob))
    matches = [(name, m) for name, m in all_mutations if needle in name]
    if len(matches) != 1:
        for name, _ in all_mutations:
            print("  " + name, file=sys.stderr)
        raise SystemExit("expected exactly one mutation matching %r in %s, "
                          "found %d (labels above)" % (needle, src, len(matches)))
    name, mutated = matches[0]
    with open(dst, "wb") as f:
        f.write(mutated)
    print("mutated %s: %s -> %s" % (src, name, dst))


if __name__ == "__main__":
    main()
