"""Property-based tests for lower_table.py.

    .venv/bin/pytest test_lower_table.py -q

WHAT THIS CAN AND CANNOT CATCH.  The ParserHawk bug this file is a reaction to --
an exporter that filed a TCAM entry under the wrong node -- could not have been
found by testing the exporter alone: its output was well formed and
self-consistent, and wrong only against a semantics living somewhere else.  The
same limit applies here.  Nothing below compares us against ParserHawk's
`implementation()`, so nothing below can tell us we have MISREAD the JSON.

What it does cover is the other half: that the s-expression we emit means what
this lowering thinks it means.  That is where the index arithmetic lives -- key
bit order, run merging, field chunking, the fallthrough chain, Peek offsets, and
the (node, cursor) unroller -- and the oracle for it is the IR itself, reached
through the `run_parser` executable.

The generator is written as composable strategies rather than as a loop over an
RNG, which is the whole reason for using Hypothesis here: it is what lets a
failure shrink to something diagnosable.  The first bug this suite found arrived
as a 3-node pipeline with a 14-entry key, and the minimal form -- one node, a
two-entry key -- is what revealed the cause.

Run `./mutation_sweep.sh` after changing anything here.  A property suite that
has never been shown to fail on a planted bug is not evidence of anything; three
of the first eight mutations survived, and each one exposed a blind spot in the
generator rather than a missing property.
"""

import json, os, subprocess, sys, tempfile

from hypothesis import HealthCheck, assume, given, settings
from hypothesis import strategies as st

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
LOWER = os.path.join(HERE, "lower_table.py")
# The built executable directly: `dune exec` per call dominates the runtime.
RUNNER = os.path.join(ROOT, "_build", "default", "extracted_code", "RunParser.exe")

# Every example shells out several times, so the per-example deadline has to go.
# mutation_sweep.sh raises the budget: 60 examples is enough for a regression run
# but not always enough to rediscover a planted bug from a cold example database.
SETTINGS = settings(max_examples=int(os.environ.get("LT_MAX_EXAMPLES", "60")),
                    deadline=None,
                    suppress_health_check=[HealthCheck.too_slow])

FIELD_WIDTHS = [1, 2, 4, 8, 16]


# ---------------------------------------------------------------- strategies

def window(draw, sizes):
    """A contiguous run of bits from one field.

    The WIDTH is drawn with `sampled_from`, which is uniform, rather than
    `integers`, which is biased towards the low end of its range.  That bias is
    what Hypothesis wants for shrinking, but here it collapses nearly every
    window to a single bit -- and a one-bit run is exactly where MSB-first and
    LSB-first patterns coincide and `runs_of` has nothing to merge.  Two planted
    mutations survived until this was made explicit.
    """
    f = draw(st.integers(0, len(sizes) - 1))
    w = draw(st.sampled_from(range(1, sizes[f] + 1)))
    lo = draw(st.integers(0, sizes[f] - w))
    return [f"field{f}[{b}]" for b in range(lo, lo + w)]


@st.composite
def key_entries(draw, sizes, mixed=True):
    """A Tran_key.

    Deliberately biased towards CONTIGUOUS windows.  Scattered bits give runs of
    length one, where MSB-first and LSB-first patterns coincide and a bit-order
    bug is invisible; runs_of only has something to merge when the bits are
    adjacent.  A planted "pattern LSB-first" mutation survives a generator that
    only scatters.
    """
    if not mixed:
        # Either all lookaheads or all field bits, never both.  A key that mixes
        # them always spans more than one run and so takes lower_table's chained
        # path, where the known peek-availability defect lives -- see
        # test_known_peek_availability.  Excluding the shape up front beats
        # filtering it out afterwards, which discards most of what is generated.
        #
        # COVERAGE GAP: no property test therefore exercises a chained key that
        # contains a Peek.  Close this when the guard-state fix lands.
        if draw(st.booleans()):
            n = draw(st.sampled_from([1, 2]))
            return [f"lookahead {j} " for j in range(n)]
        # One window is a single run; two are usually two, which is the only way
        # to reach lower_table's `chain` path without mixing in a lookahead.
        # Without this, `chain` is barely exercised and two planted mutations --
        # "runs never merged" and "rule priority reversed", both of which only
        # affect chaining -- survive.
        ks = window(draw, sizes)
        if draw(st.booleans()):
            ks = ks + [e for e in window(draw, sizes) if e not in ks]
        return draw(st.permutations(ks))

    key = list(window(draw, sizes)) if draw(st.booleans()) else []
    extra = draw(st.lists(
        st.one_of(
            st.builds(lambda j: f"lookahead {j} ", st.integers(0, 1)),
            st.integers(0, len(sizes) - 1).flatmap(
                lambda f: st.integers(0, sizes[f] - 1).map(
                    lambda b: f"field{f}[{b}]"))),
        max_size=3))
    for e in extra:
        if e not in key:
            key.append(e)
    # parse_key sorts, so the order here must not matter.
    return draw(st.permutations(key))


@st.composite
def rules(draw, width, n, tgt):
    """tran_logic for a key of `width` bits.

    The second half builds an OVERLAPPING rule: a mask that is a subset of an
    earlier rule's, agreeing with it on the shared bits, matches every key that
    rule does.  Without one, randomly drawn masks almost never overlap, first-
    match order is unobservable, and a planted "rule priority reversed" mutation
    survives.
    """
    # min_size=1: `lists` is biased towards empty, and a node with no rule can
    # never show a priority bug.
    out = draw(st.lists(
        st.tuples(st.integers(0, (1 << width) - 1),
                  st.integers(1, (1 << width) - 1),
                  tgt),
        min_size=1, max_size=3))
    logic = [[f"val:{v & m}", f"mask:{m}", f"nxt:{t}"] for (v, m, t) in out]

    # A deliberately OVERLAPPING pair, adjacent and in a random order.  Both
    # match any key that is zero on the wider mask, and their targets differ, so
    # swapping them is observable.  Everything about that has to be arranged:
    # independently drawn masks rarely overlap, independently drawn targets are
    # often equal, and a pair that agrees on its target proves nothing.  Without
    # it the "rule priority reversed" mutation survives.
    if draw(st.booleans()):
        m = draw(st.integers(1, (1 << width) - 1))
        keep = draw(st.lists(st.booleans(), min_size=width, max_size=width))
        sub = m
        for b in range(width):
            if (m >> b) & 1 and not keep[b]:
                sub &= ~(1 << b)
        t1 = draw(tgt)
        t2 = draw(tgt.filter(lambda t: t != t1))
        pair = [[f"val:0", f"mask:{m}", f"nxt:{t1}"],
                [f"val:0", f"mask:{sub if sub else m}", f"nxt:{t2}"]]
        logic += draw(st.permutations(pair))
    return logic


@st.composite
def pipelines(draw, forward=False, mixed_peek=True, must_extract=False):
    """A pipeline in ParserHawk's emitted shape, plus its field widths.

    Widths stay <= 64 so each field gets exactly one header and header ids line
    up with field ids; chunking is exercised separately.

    [forward] restricts every target to a LATER node, which makes the graph
    acyclic by construction.  That is ParserHawk's own IPU shape -- its
    constraint is `tran_idx >= sum_l[i]` -- and the tests about --input-bits
    need it, since `longest_path` is undefined on a cycle.  Generating it
    directly beats filtering: with four nodes and free targets, most pipelines
    loop, and Hypothesis rightly complains about discarding that many.
    """
    sizes = draw(st.lists(st.sampled_from(FIELD_WIDTHS), min_size=1, max_size=3))
    n = draw(st.integers(1, 4))
    nodes = []
    for i in range(n):
        tgt = st.integers(i + 1, n) if forward else st.integers(0, n)
        # [must_extract] keeps every node consuming, so the longest path is
        # nonzero and there is a cursor at which an extraction can overrun --
        # otherwise the --input-bits tests discard most of what they draw.
        extract = draw(st.integers(0, len(sizes) - 1) if must_extract
                       else st.one_of(st.none(), st.integers(0, len(sizes) - 1)))
        key = draw(key_entries(sizes, mixed=mixed_peek))
        nodes.append({
            "Extraction": None if extract is None else f"field_{extract}",
            "Tran_key": key,
            "default_tran": draw(tgt),
            "tran_logic": draw(rules(len(key), n, tgt)) if key else []})
    return nodes, sizes


@st.composite
def packets(draw, max_bits=40):
    return draw(st.lists(st.integers(0, 1), max_size=max_bits))


# ---------------------------------------------------------------- reference

def parse_key_ref(tran_key):
    """Independent restatement of ParserHawk's key packing: field bits first
    (field ascending, bit descending), then lookaheads (offset ascending), with
    the FIRST entry the most significant.  Deliberately not shared with
    lower_table.parse_key -- reusing it would reproduce any bug it has."""
    hdr, peek = [], []
    for e in tran_key:
        e = e.strip()
        if e.startswith("lookahead"):
            peek.append(("p", int(e.split()[1])))
        else:
            f, b = e[len("field"):].split("[")
            hdr.append(("h", int(f), int(b.rstrip("]"))))
    return (sorted(set(hdr), key=lambda x: (x[1], -x[2]))
            + sorted(set(peek), key=lambda x: x[1]))


def reference_run(nodes, sizes, packet, input_bits=None):
    """What the lowered parser is SUPPOSED to do, per the IR's semantics.

    Headers start uninitialised (Shim.mk_parser_state), so a key bit taken from
    a field no node has extracted yet makes its rule unmatchable -- slice_val of
    UninitVal is ErrorVal and CrVal.eqb is false against every pattern.

    [input_bits] mirrors --input-bits: an extraction that would overrun accepts
    instead of rejecting.
    """
    fields, cur, node = {}, 0, 0
    visits, bound = 0, (len(nodes) + 4) * (len(packet) + 1)
    while True:
        visits += 1
        if visits > bound:
            return "incomplete"
        if node >= len(nodes):
            return ("accept", dict(fields))
        nd = nodes[node]
        if nd["Extraction"] is not None:
            f = int(nd["Extraction"].split("_")[1])
            w = sizes[f]
            if cur + w > len(packet):
                if input_bits is not None:
                    return ("accept", dict(fields))
                return "reject"
            fields[f] = int("".join(str(b) for b in packet[cur:cur + w]), 2)
            cur += w

        entries = parse_key_ref(nd["Tran_key"])
        logic = nd["tran_logic"] or []
        if not logic:
            node = nd["default_tran"]
            continue
        total = len(entries)

        # Every case's bits are read before any is matched, so a Peek that runs
        # off the end rejects even if an earlier case would have matched
        # (eval_transition_concrete's select_bits_available_concrete).
        for e in logic:
            kv = {k.split(":")[0]: int(k.split(":")[1]) for k in e}
            mask = kv["mask"] & ((1 << total) - 1)
            for i, ent in enumerate(entries):
                if ((mask >> (total - 1 - i)) & 1 and ent[0] == "p"
                        and cur + ent[1] + 1 > len(packet)):
                    return "reject"

        def keybit(ent):
            if ent[0] == "p":
                return packet[cur + ent[1]]
            _, f, b = ent
            return None if f not in fields else (fields[f] >> b) & 1

        nxt = nd["default_tran"]
        for e in logic:
            kv = {k.split(":")[0]: int(k.split(":")[1]) for k in e}
            mask = kv["mask"] & ((1 << total) - 1)
            got, ok = 0, True
            for i, ent in enumerate(entries):
                if not (mask >> (total - 1 - i)) & 1:
                    continue
                b = keybit(ent)
                if b is None:            # reads a field nothing has extracted
                    ok = False
                    break
                got |= b << (total - 1 - i)
            if ok and got == (kv["val"] & mask):
                nxt = kv["nxt"]
                break
        node = nxt


# ---------------------------------------------------------------- plumbing

def lower(nodes, sizes, extra=()):
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        json.dump(nodes, fh)
        src = fh.name
    try:
        return subprocess.run(
            [sys.executable, LOWER, "--field-sizes", ",".join(map(str, sizes)),
             *extra, src], capture_output=True, text=True)
    finally:
        os.unlink(src)


def run_ir(ir_text, packet, wf=False):
    with tempfile.NamedTemporaryFile("w", suffix=".ir", delete=False) as fh:
        fh.write(ir_text)
        path = fh.name
    try:
        args = [RUNNER] + (["--wf", path] if wf
                           else [path, "".join(map(str, packet))])
        return subprocess.run(args, capture_output=True, text=True,
                              cwd=ROOT).stdout.strip()
    finally:
        os.unlink(path)


def ir_to_result(out):
    if out == "Reject":
        return "reject"
    if out == "Incomplete":
        return "incomplete"
    got = {}
    for part in filter(None, (p.strip() for p in out.split(","))):
        h, v = part.split("=")
        got[int(h[1:]) - 1] = int(v)          # header i+1 <-> field i
    return ("accept", got)


def lowered(nodes, sizes, extra=()):
    """The .ir text, or discard the example.

    `cannot lower:` is a verdict (a non-consuming cycle, say), not a failure --
    but a traceback is.  Note this discards via `assume`, not `pytest.skip`:
    inside `@given`, skip aborts the whole test rather than one example.
    """
    r = lower(nodes, sizes, extra)
    if r.returncode != 0:
        assert "cannot lower:" in r.stderr, r.stderr.strip()[-400:]
        assume(False)
    return r.stdout


def longest_path_of(text):
    for line in text.splitlines():
        if line.startswith("; Longest path needs "):
            return int(line.split()[4])
    return None


def body(text):
    return [l for l in text.splitlines() if not l.startswith(";")]


def has_chained_peek(nodes):
    """Does some node's key mix a lookahead with anything else?

    Such a key always spans more than one run -- a Peek run can never merge with
    a header run -- so lower_table takes its chained path, where the known
    peek-availability defect lives.  See test_known_peek_availability.
    """
    return any(any(e.strip().startswith("lookahead") for e in nd["Tran_key"])
               and len(parse_key_ref(nd["Tran_key"])) > 1
               for nd in nodes if nd["tran_logic"])


# ---------------------------------------------------------------- properties

@SETTINGS
@given(pipelines(mixed_peek=False), st.lists(packets(), min_size=1, max_size=3))
def test_differential(pipeline, pkts):
    """(1) The lowered parser agrees with the reference on every packet."""
    nodes, sizes = pipeline
    ir = lowered(nodes, sizes)
    for pkt in pkts:
        assert reference_run(nodes, sizes, pkt) == ir_to_result(run_ir(ir, pkt)), \
            f"packet={''.join(map(str, pkt))}"


@SETTINGS
@given(pipelines())
def test_well_formed(pipeline):
    """(2) The IR accepts everything we emit: closed, unique labels, progress."""
    nodes, sizes = pipeline
    assert run_ir(lowered(nodes, sizes), [], wf=True) == "wellformed"


@SETTINGS
@given(pipelines())
def test_deterministic(pipeline):
    """(4) Lowering is a function of its input."""
    nodes, sizes = pipeline
    ir = lowered(nodes, sizes)
    assert lower(nodes, sizes).stdout == ir


@SETTINGS
@given(pipelines(forward=True, mixed_peek=False), st.lists(packets(), min_size=1, max_size=2))
def test_unroll_is_noop_above_longest_path(pipeline, pkts):
    """(3) --input-bits N changes nothing once N covers the longest path.

    BEHAVIOURAL, not textual: unrolling legitimately splits a node reachable at
    two cursors into two states, so the text can differ while the parser does
    not.  What must hold is that no extraction overruns and that the two agree
    on every packet.
    """
    nodes, sizes = pipeline
    ir = lowered(nodes, sizes)
    need = longest_path_of(ir)
    assume(need is not None)
    r = lower(nodes, sizes, ("--input-bits", str(need)))
    assert r.returncode == 0, "refused a pipeline the default path accepted"
    assert "warning:" not in r.stderr, f"--input-bits {need} reported an overrun"
    for pkt in pkts:
        assert run_ir(ir, pkt) == run_ir(r.stdout, pkt)


@SETTINGS
@given(pipelines(forward=True, mixed_peek=False, must_extract=True), st.data())
def test_overrun_accepts_instead_of_rejecting(pipeline, data):
    """(6) Below the longest path, an extraction that would run off the end
    accepts rather than rejects -- ParserHawk treats it as a no-op that freezes
    the fields.  Property (3) only covers lengths where no overrun happens, so
    without this the whole of unroll_by_cursor is untested."""
    nodes, sizes = pipeline
    ir = lowered(nodes, sizes)
    need = longest_path_of(ir)
    assert need is not None and need > 0
    short = data.draw(st.integers(0, need - 1))
    r = lower(nodes, sizes, ("--input-bits", str(short)))
    assume(r.returncode == 0)
    pkt = data.draw(st.lists(st.integers(0, 1), min_size=short, max_size=short))
    assert (reference_run(nodes, sizes, pkt, input_bits=short)
            == ir_to_result(run_ir(r.stdout, pkt))), \
        f"--input-bits {short} packet={''.join(map(str, pkt))}"


@SETTINGS
@given(pipelines(mixed_peek=False), st.lists(packets(), min_size=1, max_size=2))
def test_shadowed_rule_changes_nothing(pipeline, pkts):
    """(5) Rules are first-match, so a duplicate of an earlier rule can never be
    reached.  (An "unmatchable" rule is not expressible: lower_table masks val to
    the key width, so under a full mask every value is reachable.)"""
    nodes, sizes = pipeline
    i = next((k for k, nd in enumerate(nodes) if nd["tran_logic"]), None)
    assume(i is not None)
    ir = lowered(nodes, sizes)
    dup = json.loads(json.dumps(nodes))
    dup[i]["tran_logic"] = dup[i]["tran_logic"] + [dup[i]["tran_logic"][0]]
    r = lower(dup, sizes)
    assume(r.returncode == 0)
    for pkt in pkts:
        assert run_ir(ir, pkt) == run_ir(r.stdout, pkt)


# ---------------------------------------------------------------- known defect

def test_known_peek_availability():
    """CHARACTERISATION, not a specification.  DELETE THIS when the guard-state
    fix lands -- it asserts behaviour we believe is WRONG.

    The IR reads every case of a select before matching any
    (select_bits_available_concrete), so an overrunning Peek rejects.  But
    lower_table only emits a single select when the cared bits form one run; a
    key spanning two runs becomes a chain of one-case states, and a Peek in a
    later link is never entered once an earlier link falls through.  Whether an
    overrun rejects therefore depends on whether the key's bits happen to be
    adjacent, which should not be semantically load-bearing.
    """
    one = [{"Extraction": "field_0", "Tran_key": ["lookahead 1 "],
            "default_tran": 1, "tran_logic": [["val:1", "mask:1", "nxt:0"]]}]
    two = [{"Extraction": "field_0", "Tran_key": ["lookahead 1 ", "field1[8]"],
            "default_tran": 1, "tran_logic": [["val:1", "mask:3", "nxt:0"]]}]
    pkt = [0, 0, 1, 1, 1, 0, 1, 1]          # 8 bits; the peek wants bit 9
    assert ir_to_result(run_ir(lowered(one, [8, 16]), pkt)) == "reject"
    assert ir_to_result(run_ir(lowered(two, [8, 16]), pkt)) == ("accept", {0: 59})
