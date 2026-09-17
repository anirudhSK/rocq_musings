#!/usr/bin/env python3
"""Differential-test the rocq backend against p4c's own semantics.

Every other test in this directory is RELATIVE: it checks that two spellings of
the same computation lower to programs the equivalence checker cannot tell
apart.  That is a real property and it is not the one that matters most -- a
systematic misreading shared by both spellings (an endianness, a field order, a
width mask off by one) is invisible to it, because both sides have it.

This one is absolute.  p4testgen symbolically executes the P4 program against
p4c's model of the target and emits, per path it finds, an input packet and the
output packet that model produces.  We lower the same program with rocq, run it
on the same input with run_net, and compare.  A mismatch is a lowering bug and
there is nothing to interpret.

    translation/tests/differential.py prog.p4 [--tests N] [-- <rocq flags>]

Needs p4testgen, which is not built by default:

    cd translation/p4c/build && cmake -DENABLE_TEST_TOOLS=ON .. && make p4testgen
"""

import argparse
import os
import re
import subprocess
import sys
import tempfile

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
ROCQ = os.path.join(ROOT, "translation/p4c/build/rocq")
TESTGEN = os.path.join(ROOT, "translation/p4c/build/p4testgen")
RUNNET = os.path.join(ROOT, "_build/default/extracted_code/RunNet.exe")


def need(path, how):
    if not os.path.exists(path):
        sys.exit("missing %s\n  build it: %s" % (path, how))


# ---------------------------------------------------------------- STF parsing

ADD_RE = re.compile(r"^add\s+(\S+)\s+(.*)$")


def parse_adds(text):
    """Table entries p4testgen chose, as lines for --table-entries.

    STF writes an entry as

        add <control>.<table> <key>:<value> ... <control>.<action>(<p>:<v>, ...)

    and --table-entries wants `<table> <key>... -> <action> [<arg>...]`, with
    keys and arguments POSITIONAL.  The names are dropped rather than resolved:
    STF lists keys in the table's key order and arguments in the action's
    parameter order, which is the same order this needs.

    Using p4testgen's own choice of entries is the point.  A table populated at
    runtime has no entries in its source, so the model and the lowering would
    otherwise be executing different switches.
    """
    def clean(tok):
        """STF quotes names and writes numbers in binary as well as hex."""
        tok = tok.strip().strip('"')
        if tok.startswith("0b"):
            return str(int(tok[2:], 2))
        return tok

    out = []
    for line in text.splitlines():
        m = ADD_RE.match(line.strip())
        if not m:
            continue
        table = clean(m.group(1)).split(".")[-1]
        rest = m.group(2).strip()
        # A table with an lpm or ternary key carries an entry PRIORITY between
        # the table name and the keys.  It orders the entries, which is what
        # --table-entries derives from specificity instead, so it is dropped.
        rest = re.sub(r"^\d+\s+", "", rest)
        call = re.search(r"(\S+)\s*\((.*)\)\s*$", rest)
        if call:
            action = clean(call.group(1)).split(".")[-1]
            argtext = call.group(2)
            keytext = rest[:call.start()].strip()
        else:                      # an action with no parameters
            parts = rest.rsplit(None, 1)
            keytext, action = (parts[0], parts[1]) if len(parts) == 2 else ("", rest)
            action = clean(action).split(".")[-1]
            argtext = ""
        keys = [clean(k.split(":", 1)[1] if ":" in k else k) for k in keytext.split()]
        args = [clean(a.split(":", 1)[1] if ":" in a else a)
                for a in argtext.split(",") if a.strip()]
        out.append(" ".join([table] + keys + ["->", action] + args))
    return out


def is_parse_failure(text):
    """Does this test exercise a FAILED parse?

    v1model sets standard_metadata.parser_error and runs the pipeline anyway,
    so the model still emits a packet.  The IR treats a parser reject as
    terminal -- gps_valid goes false and stays false, which is what makes the
    both-rejected disjunct of modnet_equivalence_checker_sound mean anything.
    The two conventions are not comparable, so these are counted apart rather
    than reported as a lowering bug.
    """
    return "ExtractFailure" in text or "parser_error" in text


def parse_stf(text):
    """STF is bmv2's test format.  The two lines we need are

        packet <port> <hex>
        expect <port> <hex>

    Hex may carry spaces, and an `expect` may carry `*` for a don't-care
    nibble, which is how p4testgen writes a field the path did not constrain.
    Returns a list of (in_hex, expect_hex_or_None); the None is a drop, where
    the model emits nothing at all.
    """
    # STF ends a packet with `$`, which is a marker and not a nibble.
    text = text.replace("$", "")
    cases, pending = [], None
    for line in text.splitlines():
        line = line.strip()
        m = re.match(r"^packet\s+\d+\s+(.*)$", line)
        if m:
            if pending is not None:
                cases.append((pending, None))
            pending = re.sub(r"\s+", "", m.group(1))
            continue
        m = re.match(r"^expect\s+\d+\s*(.*)$", line)
        if m and pending is not None:
            cases.append((pending, re.sub(r"\s+", "", m.group(1))))
            pending = None
    if pending is not None:
        cases.append((pending, None))
    return cases


# ------------------------------------------------------------------ run_net

RUN_RE = re.compile(r"^\[(.*?)\]\s+(\d+)b")


def run_ir(ir_path, in_hex):
    """The emitted packet as hex, or None if the run rejected."""
    out = subprocess.run([RUNNET, ir_path, "pkt:" + in_hex],
                         capture_output=True, text=True).stdout
    first = out.strip().splitlines()[0] if out.strip() else ""
    if first.startswith("reject"):
        return None
    m = RUN_RE.match(first)
    if not m:
        return None
    body = m.group(1).strip()
    if not body:
        return ""
    return "".join("%02x" % int(b) for b in body.split(","))


# ---------------------------------------------------------------- comparison

def compare(got, want):
    """The IR's output against the model's.

    Two allowances, both principled rather than convenient:

    `*` in the model's output is a nibble the symbolic path never constrained,
    so any value satisfies it.

    The model appends the PAYLOAD -- the bytes the parser did not consume --
    while the IR's deparser emits only what it emits and leaves the residual on
    the read tape (see the note on sh_read_tape in CLAUDE.md).  So the IR's
    output has to match a PREFIX of the model's, and the rest of the model's
    has to be the tail of the input, which the caller checks.
    """
    if len(got) > len(want):
        return False, "emitted %d nibbles, model emitted %d" % (len(got), len(want))
    for i, (g, w) in enumerate(zip(got, want)):
        if w == "*":
            continue
        if g.lower() != w.lower():
            return False, "nibble %d: emitted %s, model %s" % (i, g, w)
    return True, ""


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("p4")
    ap.add_argument("--tests", type=int, default=10)
    ap.add_argument("--arch", default="v1model")
    ap.add_argument("--target", default="bmv2")
    ap.add_argument("--keep", action="store_true", help="keep the work directory")
    ap.add_argument("rocq_flags", nargs="*", help="extra flags for rocq")
    args, unknown = ap.parse_known_args()
    args.rocq_flags = list(args.rocq_flags) + unknown  # anything we do not know is rocq's

    need(ROCQ, "cd translation/p4c/build && make rocq")
    need(RUNNET, "cd %s && make && dune build" % ROOT)
    need(TESTGEN, "cd translation/p4c/build && cmake -DENABLE_TEST_TOOLS=ON .. && make p4testgen")

    work = tempfile.mkdtemp(prefix="differential.")
    name = os.path.splitext(os.path.basename(args.p4))[0]

    # 1. the model's tests
    tg = subprocess.run(
        [TESTGEN, "--target", args.target, "--arch", args.arch,
         "--test-backend", "STF", "--max-tests", str(args.tests),
         "--out-dir", work, args.p4],
        capture_output=True, text=True)
    stf = [f for f in sorted(os.listdir(work)) if f.endswith(".stf")]
    if not stf:
        print("FAIL  p4testgen produced no tests")
        print(tg.stderr.strip()[:2000])
        return 2

    # 2. our lowering, once per test file -- p4testgen picks a control-plane
    #    configuration per path, so the entries are not the same for all of them
    ok = bad = skipped = parsefail = 0
    for f in stf:
        text = open(os.path.join(work, f)).read()
        if is_parse_failure(text):
            parsefail += 1
            continue
        flags = list(args.rocq_flags)
        # Always written, even when p4testgen chose no entries: an empty file
        # is a real configuration (every table empty, only default actions),
        # and it is how the backend is told that the file is the whole story.
        ent = os.path.join(work, f + ".entries")
        open(ent, "w").write("\n".join(parse_adds(text)) + "\n")
        flags += ["--table-entries", ent]
        ir = os.path.join(work, f + ".ir")
        with open(ir, "w") as out:
            r = subprocess.run([ROCQ] + flags + [args.p4],
                               stdout=out, stderr=subprocess.PIPE, text=True)
        if r.returncode != 0 or os.path.getsize(ir) < 200:
            print("FAIL  %s did not lower (%s)" % (name, f))
            for line in r.stderr.splitlines():
                if "error:" in line:
                    print("        " + line.strip()[:150])
            return 2

        for in_hex, want in parse_stf(text):
            if want is None:
                skipped += 1        # the model drops; the IR has no drop to compare
                continue
            got = run_ir(ir, in_hex)
            if got is None:
                print("  FAIL  %s: the IR rejected, the model emitted %s" % (f, want[:32]))
                bad += 1
                continue
            good, why = compare(got, want)
            if good:
                ok += 1
            else:
                bad += 1
                print("  FAIL  %s: %s" % (f, why))
                print("          in    %s" % in_hex)
                print("          ir    %s" % got)
                print("          model %s" % want)

    print("%-24s %d ok, %d failed, %d dropped by the model, %d parse-failure paths"
          % (name, ok, bad, skipped, parsefail))
    if not args.keep:
        subprocess.run(["rm", "-rf", work])
    else:
        print("  work: %s" % work)
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
