"""
Lower a ParserHawk synthesized pipeline into a Caracara IR `Parser` s-expression.
Emits just the Parser record for JSON that `codegen()` returns in ParserHawk's `*_op.py` scripts.

`lookahead N` in a Tran_key becomes the IR's `Peek`.  ParserHawk emits the
variable `node{i}_ahead{j}`, and `key_sel` reads packet bit `post_node_pos + j`
-- the bit `j` past the cursor AFTER that node's extraction.  The IR evaluates a
state's transition post-extraction too (`eval_parser_concrete` applies the action
before `eval_transition_concrete`), so `lookahead j` is exactly `Peek j 1`, with
no extra state needed.  Runs of consecutive `j` merge into one `Peek j w`.

A pipeline whose nodes loop is fine and is emitted as-is, not unrolled.  The IR
admits P4-style loops: `ParserWellFormed`'s progress condition asks only that
every cycle CONSUMES, and `eval_parser_concrete`'s fuel of
`|states| * (|packet| + 1)` bounds a parse on the argument that a configuration
is a (state, cursor) pair which a terminating parse never repeats.  Only a cycle
that moves no cursor is refused here, which is the same thing the IR refuses.

`--input-bits N` unrolls the parser on (node, cursor) against an N-bit packet
and emits `Accept` wherever an extraction would run past the end, with a warning
naming each one.  That is ParserHawk's behaviour, not the IR's: its
`dynamic_extract_loop` builds no branch for a cursor where the field does not
fit, so an over-long extraction silently keeps the field's old value and leaves
the cursor put, freezing everything after it; the IR rejects instead.  Without
the flag the graph is emitted as-is, which is right whenever no extraction can
overrun.

Unsupported:
* `post process fieldN[b]` entries.
"""

import argparse
import json
import re
import sys

BIT_RE = re.compile(r"^field(\d+)\[(\d+)\]$")
FIELD_RE = re.compile(r"^field_(\d+)$")
LOOKAHEAD_RE = re.compile(r"^lookahead\s+(\d+)$")

MAX_CHUNK = 64

IR_TYPE = {8: "W8", 16: "W16", 32: "W32", 64: "W64"}

class Unsupported(Exception):
    pass

class _Cyclic(Exception):
    """The state graph has a cycle; the longest path is not a graph property."""

def width_slot(width):
    """Narrowest CrIntType slot holding `width` bits.  Chunking keeps it <= 64."""
    for w in (8, 16, 32, 64):
        if width <= w:
            return w
    raise Unsupported(f"internal: chunk of {width} bits exceeds u64")

def chunk_widths(width):
    """Cut `width` into <=64-bit pieces, most significant first (wire order)."""
    if width <= 0:
        raise Unsupported(f"field width {width} is not positive")
    out = []
    left = width
    while left > MAX_CHUNK:
        out.append(MAX_CHUNK)
        left -= MAX_CHUNK
    out.append(left)
    return out

def parse_key(tran_key):
    """Tran_key -> key entries in ParserHawk's packing order.

    Entries are ("h", field, bit) for an already-extracted field bit and
    ("p", offset) for a lookahead bit.

    ParserHawk builds the key by concatenating field bits first (field
    ascending, bit descending) and then the lookahead bits (offset ascending),
    each newly appended bit becoming LESS significant -- see `key_sel` in
    mask_val_for_statetran_IPU.py.  So the first entry here is the key's MSB.
    `custom_sort` bubbles lookahead entries to the end of Tran_key but leaves
    them unordered among themselves (two non-field entries never swap), so sort
    them by offset here rather than trusting the JSON order.
    """
    hdr, peek = [], []
    for entry in tran_key:
        text = entry.strip()
        m = BIT_RE.match(text)
        if m:
            hdr.append(("h", int(m.group(1)), int(m.group(2))))
            continue
        m = LOOKAHEAD_RE.match(text)
        if m:
            peek.append(("p", int(m.group(1))))
            continue
        raise Unsupported(f"unrecognized Tran_key entry {entry!r}")
    return (sorted(set(hdr), key=lambda e: (e[1], -e[2]))
            + sorted(set(peek), key=lambda e: e[1]))

def run_value(val, total_bits, positions):
    """Value of the key bits at `positions` (0 = MSB of the packed key)."""
    v = 0
    for p in positions:
        v = (v << 1) | ((val >> (total_bits - 1 - p)) & 1)
    return v

def parse_kv(entry):
    """['val:6','mask:65535','nxt:6'] -> (6, 65535, 6)"""
    d = {}
    for item in entry:
        k, _, v = item.partition(":")
        d[k.strip()] = int(v)
    return d["val"], d["mask"], d["nxt"]

def coq_list(items):
    """Render a Rocq list as the extracted Coq_cons chain the .ir format uses."""
    out = "Coq_nil"
    for x in reversed(items):
        out = f"(Coq_cons {x} {out})"
    return out

class Builder:
    def __init__(self, pipeline, field_sizes):
        self.pipe = pipeline
        self.sizes = field_sizes
        self.n = len(pipeline)
        self.next_label = self.n + 1
        self.extra = []

        # (field, chunk) -> header id; chunk 0 holds the most significant bits.
        self.chunks = {}
        hid = 1
        for f, w in enumerate(field_sizes):
            base, entries = w, []
            for cw in chunk_widths(w):
                base -= cw
                entries.append({"header": hid, "width": cw,
                                "lo": base, "hi": base + cw})
                hid += 1
            self.chunks[f] = entries
        self.num_headers = hid - 1

    # -- helpers -----------------------------------------------------------
    def target(self, idx):
        if idx is None or idx >= self.n or idx < 0:
            return ("accept",)
        return ("state", idx + 1)

    def fresh(self):
        lbl = self.next_label
        self.next_label += 1
        return lbl

    def locate(self, field, bit):
        if field not in self.chunks:
            raise Unsupported(f"field{field} has no declared width")
        for c in self.chunks[field]:
            if c["lo"] <= bit < c["hi"]:
                return c["header"], bit - c["lo"]
        raise Unsupported(f"field{field}[{bit}] is outside the field's width")

    def runs_of(self, entries, positions):
        """Maximal runs of adjacent key bits, as tagged tuples:

            ("h", header, lo, hi, positions)   a header slice  -> SelHdr
            ("p", offset, width, positions)    a lookahead     -> Peek

        A header run is consecutive DESCENDING local bit indices within one
        header -- the key packs a field MSB-first, and a chunk boundary splits
        a run because the two halves live in different headers.  A lookahead
        run is consecutive ASCENDING offsets, which is the same direction:
        [Peek off width] reads MSB-first from [cursor + off], and the key lists
        lookahead j before lookahead j+1.
        """
        located = []
        for e, p in zip(entries, positions):
            if e[0] == "h":
                h, idx = self.locate(e[1], e[2])
                located.append(("h", h, idx, p))
            else:
                located.append(("p", None, e[1], p))

        def adjacent(prev, item):
            if prev[0] != item[0] or prev[1] != item[1]:
                return False
            return (item[2] == prev[2] - 1 if item[0] == "h"
                    else item[2] == prev[2] + 1)

        runs, cur = [], []
        for item in located:
            if cur and adjacent(cur[-1], item):
                cur.append(item)
            else:
                if cur:
                    runs.append(cur)
                cur = [item]
        if cur:
            runs.append(cur)

        out = []
        for r in runs:
            pos = [x[3] for x in r]
            if r[0][0] == "h":
                out.append(("h", r[0][1], r[-1][2], r[0][2] + 1, pos))
            else:
                out.append(("p", r[0][2], len(r), pos))
        return out

    def extraction_chunks(self, node):
        ext = node.get("Extraction")
        if ext is None:
            return []
        m = FIELD_RE.match(ext)
        if not m:
            raise Unsupported(f"unrecognized Extraction {ext!r}")
        field = int(m.group(1))
        if field >= len(self.sizes):
            raise Unsupported(
                f"{ext} has no width; --field-sizes has only {len(self.sizes)} entries"
            )
        return [(c["header"], c["width"]) for c in self.chunks[field]]

    # -- transitions -------------------------------------------------------
    def transition(self, node):
        logic = node.get("tran_logic") or []
        default = self.target(node.get("default_tran"))
        if not logic:
            return ("uncond", default)

        entries = parse_key(node.get("Tran_key") or [])
        if not entries:
            raise Unsupported("node has tran_logic but an empty Tran_key")
        total = len(entries)

        decoded = []
        for entry in logic:
            val, mask, nxt = parse_kv(entry)
            mask &= (1 << total) - 1
            if mask == 0:
                raise Unsupported(f"entry {entry!r} masks out every key bit")
            val &= mask
            cared = [i for i in range(total) if (mask >> (total - 1 - i)) & 1]
            decoded.append((self.runs_of([entries[i] for i in cared], cared),
                            val, self.target(nxt)))

        if all(len(runs) == 1 for (runs, _, _) in decoded):
            cases = []
            for (runs, val, tgt) in decoded:
                run = runs[0]
                cases.append((run, run_value(val, total, run[-1]), tgt))
            return ("select", cases, default)

        fallthrough = default
        for (runs, val, tgt) in reversed(decoded):
            fallthrough = self.chain(runs, val, total, tgt, fallthrough)
        # Every Peek this node's rules read has to be CHECKED FOR AVAILABILITY
        # before any of them is matched, because that is what the one-Select
        # path above does: [eval_transition_concrete] tests
        # [select_bits_available_concrete] over the whole select, so one
        # overrunning Peek rejects even when an earlier case would have matched.
        # Chaining scopes that check per state, and a Peek in a later link is
        # never reached once an earlier link falls through -- so without this
        # guard, whether an overrun rejects depends on whether the key's bits
        # happen to be ADJACENT, which is a property of the encoding and not of
        # the pipeline.
        peeks, seen = [], set()
        for (runs, _, _) in decoded:
            for r in runs:
                if r[0] == "p" and (r[1], r[2]) not in seen:
                    seen.add((r[1], r[2]))
                    peeks.append(r)
        if peeks:
            fallthrough = self.peek_guard(peeks, fallthrough)
        return ("uncond", fallthrough)

    def peek_guard(self, peeks, head):
        """A state that reads every Peek and goes to [head] regardless.

        Both the cases and the default target [head], so the match itself is
        irrelevant and only the availability check survives.  Zero-width, so the
        cursor the offsets are measured from is unchanged.
        """
        lbl = self.fresh()
        self.extra.append({
            "label": lbl, "action": None,
            "trans": ("select", [(r, 0, head) for r in peeks], head)})
        return ("state", lbl)

    def chain(self, runs, val, total, target, fallthrough):
        """One zero-width state per run; all must match to reach `target`.

        A [Peek] survives this splitting unchanged: none of the states made
        here extract, so the cursor at each of them is still the cursor after
        the original node's extraction -- the one the offset was measured from.
        """
        labels = [self.fresh() for _ in runs]
        for i, run in enumerate(runs):
            v = run_value(val, total, run[-1])
            # Intermediate links are ParserTargets, not bare labels.
            nxt = target if i == len(runs) - 1 else ("state", labels[i + 1])
            self.extra.append({
                "label": labels[i], "action": None,
                "trans": ("select", [(run, v, nxt)], fallthrough)})
        return ("state", labels[0])

    # -- whole parser ------------------------------------------------------
    def build(self):
        states = []
        for i, node in enumerate(self.pipe):
            ch = self.extraction_chunks(node)
            trans = self.transition(node)
            if len(ch) <= 1:
                states.append({
                    "label": i + 1,
                    "action": None if not ch else ("extract",) + ch[0],
                    "trans": trans})
            else:
                labels = [i + 1] + [self.fresh() for _ in ch[1:]]
                for k, (h, w) in enumerate(ch):
                    tail = (trans if k == len(ch) - 1
                            else ("uncond", ("state", labels[k + 1])))
                    states.append({"label": labels[k],
                                   "action": ("extract", h, w),
                                   "trans": tail})
        return states + self.extra

    def succs_of(self, s):
        t = s["trans"]
        outs = ([t[1]] if t[0] == "uncond"
                else [c[2] for c in t[1]] + [t[2]])
        return [x[1] for x in outs if x[0] == "state"]

    @staticmethod
    def consumes(s):
        """Does this state move the cursor?  A zero-width extract does not."""
        return bool(s["action"]) and s["action"][2] > 0

    def nonconsuming_cycle(self, states):
        """Is there a cycle none of whose states moves the cursor?

        That is the IR's own progress condition ([ParserWellFormed]'s
        [nonconsuming_edges] being acyclic), and it is the only kind of loop
        that fails to terminate.  A cycle through a state that extracts is
        FINE: the IR bounds a parse by |states| * (|packet| + 1) visits on the
        argument that a configuration is a (state, cursor) pair and a
        terminating parse never repeats one.  So a loop that consumes is
        bounded by the packet, not by the graph.
        """
        by_label = {s["label"]: s for s in states}
        nodes = {l for l, s in by_label.items() if not self.consumes(s)}
        color = {}

        def go(l):
            color[l] = 1
            for x in self.succs_of(by_label[l]):
                if x not in nodes:
                    continue
                c = color.get(x, 0)
                if c == 1 or (c == 0 and go(x)):
                    return True
            color[l] = 2
            return False

        return any(color.get(l, 0) == 0 and go(l) for l in nodes)

    def longest_path(self, states, start):
        """Bits the packet must HAVE on the longest path, or None if unbounded.

        Not just the bits CONSUMED: a [Peek] moves no cursor but still has to be
        inside the packet, and overrunning one REJECTS the parse rather than
        falling through to the select's default (see [select_bits_valid] in
        CrSymbolicSemanticsParser.v).  So a state needs its own extraction plus
        the further of what its successors need and what its own select peeks
        at -- otherwise the declared input length is too short and every packet
        that reaches the lookahead is rejected.

        [None] when the graph has a cycle.  Given [nonconsuming_cycle] has
        already passed, such a cycle consumes, so the parse still terminates --
        it ends by running out of packet.  How many bits that takes is then a
        property of the packet length you choose, not of the parser, and there
        is nothing here to compute.
        """
        by_label = {s["label"]: s for s in states}

        def peek_reach(s):
            """Bits past this state's post-extraction cursor that it reads."""
            t = s["trans"]
            if t[0] != "select":
                return 0
            return max([r[1] + r[2] for (r, _, _) in t[1] if r[0] == "p"] + [0])

        memo, onstack = {}, set()

        def go(lbl):
            if lbl in onstack:
                raise _Cyclic()
            if lbl in memo:
                return memo[lbl]
            s = by_label.get(lbl)
            if s is None:
                return 0
            w = s["action"][2] if s["action"] else 0
            onstack.add(lbl)
            best = w + max([go(x) for x in self.succs_of(s)] + [peek_reach(s), 0])
            onstack.discard(lbl)
            memo[lbl] = best
            return best

        try:
            return go(start)
        except _Cyclic:
            return None

    def unroll_by_cursor(self, states, start, input_bits):
        """One IR state per reachable (node, cursor), with over-long
        extractions turned into Accept.

        ParserHawk and the IR disagree about running off the end of the packet.
        [dynamic_extract_loop] only builds an [If] branch for a cursor where the
        whole field fits (`if end < 0: break`), so at any later cursor the
        expression falls through to its base -- the field's EXISTING value.  An
        over-long extraction is therefore a silent no-op that freezes the
        fields, and since the cursor does not move either, every later
        extraction is a no-op too.  The IR instead REJECTS
        ([apply_extract_concrete] returns [None] when cursor + width exceeds the
        packet), which is a different observable.

        Accepting at that point is what matches: no extraction runs, so no field
        changes, which is exactly ParserHawk's frozen-fields outcome.  Doing it
        needs the cursor, and the cursor is only static per CONFIGURATION -- a
        looping parser reaches the same node at several cursors -- so the graph
        is unrolled on (node, cursor).  That terminates because the cursor only
        grows and is capped by [input_bits].
        """
        by_label = {s["label"]: s for s in states}
        seen, new_states = {}, []
        self.overruns = []

        def visit(lbl, cur):
            key = (lbl, cur)
            if key in seen:
                return seen[key]
            # Keep the original label for a node's first cursor, so a parser
            # that reaches every node at one cursor is emitted unchanged.
            nl = lbl if all(k != lbl for (k, _) in seen) else self.fresh()
            seen[key] = nl
            # Reserve the slot BEFORE recursing, so states come out in the order
            # they are first reached.  A parser that needs no unrolling then
            # emits exactly what it did before the cursor pass existed.
            slot = {"label": nl}
            new_states.append(slot)
            st = by_label[lbl]
            w = st["action"][2] if st["action"] else 0
            if w and cur + w > input_bits:
                self.overruns.append((lbl, cur, w))
                slot.update(action=None, trans=("uncond", ("accept",)))
                return nl
            nxt = cur + w

            def retarget(t):
                return ("state", visit(t[1], nxt)) if t[0] == "state" else t

            tr = st["trans"]
            tr2 = (("uncond", retarget(tr[1])) if tr[0] == "uncond"
                   else ("select", [(r, v, retarget(g)) for (r, v, g) in tr[1]],
                         retarget(tr[2])))
            slot.update(action=st["action"], trans=tr2)
            return nl

        visit(start, 0)
        # By label, so a parser that needs no unrolling comes out byte-identical
        # to what the pass-free path emits.  Order is cosmetic -- states are
        # looked up by label and the start is named separately -- but keeping it
        # stable makes a regenerated fixture diffable.
        return sorted(new_states, key=lambda st: st["label"])

    def legend(self):
        out = []
        for f, entries in sorted(self.chunks.items()):
            if len(entries) == 1:
                out.append(f"field{f} ({self.sizes[f]} bits) "
                           f"-> header {entries[0]['header']}")
            else:
                parts = ", ".join(f"header {c['header']} [{c['hi'] - 1}:{c['lo']}]"
                                  for c in entries)
                out.append(f"field{f} ({self.sizes[f]} bits, chunked) -> {parts}")
        return out

    def emit_ops(self):
        """EmitOpConstructor per allocated header, in allocation order."""
        out = []
        for f, entries in sorted(self.chunks.items()):
            for c in entries:
                out.append(f"(EmitOpConstructor {c['header']} {c['width']})")
        return out

# --------------------------------------------------------------------------

def parser_sexp(states, start):
    def tgt(t):
        return {"accept": "Accept", "reject": "Reject"}.get(
            t[0], f"(TargetState {t[-1]})")

    def pat(v, w):
        return coq_list(["Coq_true" if (v >> (w - 1 - i)) & 1 else "Coq_false"
                         for i in range(w)])

    def case(c):
        """A case reads either an already-parsed header slice or a lookahead.

        [SelHdr] can never fail; [Peek] can run off the end of the packet, and
        when it does the parse rejects instead of taking the select's default.
        """
        run, v, g = c
        if run[0] == "h":
            _, h, lo, hi, _ = run
            origin, width = f"(SelHdr {h} {lo} {hi})", hi - lo
        else:
            _, off, width, _ = run
            origin = f"(Peek {off} {width})"
        return (f"((sc_origin {origin}) (sc_pattern {pat(v, width)}) "
                f"(sc_target {tgt(g)}))")

    def trans(t):
        if t[0] == "uncond":
            return f"(Unconditional {tgt(t[1])})"
        return f"(Select {coq_list([case(c) for c in t[1]])} {tgt(t[2])})"

    def state(s):
        act = ("None" if not s["action"] else
               f"(Some (ExtractOpConstructor {s['action'][1]} {s['action'][2]} "
               f"{IR_TYPE[width_slot(s['action'][2])]}))")
        return (f"((psd_label {s['label']}) (psd_action {act}) "
                f"(psd_trans {trans(s['trans'])}))")

    return (f"((parser_start {start}) "
            f"(parser_states {coq_list([state(s) for s in states])}))")

def render(b, states, start, input_bits=None):
    """Parser sexp, with a `;` preamble.  Sexplib skips those, so it still loads."""
    lines = ["; Generated by translation/parserhawk/lower_table.py -- a bare CrParser.Parser.",
             "; Header allocation:"]
    lines += [f";   {l}" for l in b.legend()]
    need = input_bits if input_bits is not None else b.longest_path(states, start)
    if input_bits is not None:
        lines.append(f"; Unrolled on (node, cursor) against a {input_bits}-bit packet.")
        lines.append("; An extraction that would run past the end is emitted as Accept,")
        lines.append("; because ParserHawk treats it as a no-op that freezes the fields")
        lines.append("; while the IR would reject.  See Builder.unroll_by_cursor.")
    if need is None:
        lines.append("; This parser LOOPS, and every cycle consumes, so it terminates by")
        lines.append("; running out of packet rather than by reaching an end state.  How")
        lines.append("; many bits that takes depends on the input length you pick, so there")
        lines.append("; is no figure to put here -- choose GeneralCaracaraProgramDef's input")
        lines.append("; length yourself.  The IR bounds the loop at |states| * (|packet|+1)")
        lines.append("; state visits; see the fuel on eval_parser_concrete.")
    else:
        lines.append(f"; Longest path needs {need} bits of packet "
                     "(use as GeneralCaracaraProgramDef's input length).")
        lines.append("; That counts lookahead: a Peek consumes nothing but still has to be in")
        lines.append("; the packet, and overrunning one rejects rather than defaulting.")
    lines.append("; Deparser emits covering every header written here:")
    lines.append(";   " + " ".join(b.emit_ops()))
    return "\n".join(lines) + "\n" + parser_sexp(states, start) + "\n"

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pipeline", help="ParserHawk pipeline JSON")
    ap.add_argument("--field-sizes", required=True,
                    help="comma-separated pkt_field_size_list, e.g. 1,16,8,8,8,1,1,1,1")
    ap.add_argument("--input-bits", type=int, default=None,
                    help="declared packet length.  Unrolls the parser on "
                         "(node, cursor) and emits Accept where an extraction "
                         "would run past the end, matching ParserHawk's "
                         "no-op-and-freeze rather than the IR's reject.")
    ap.add_argument("-o", "--output", help="write here instead of stdout")
    args = ap.parse_args()

    pipeline = json.load(open(args.pipeline))
    if not isinstance(pipeline, list):
        sys.exit("pipeline JSON must be a list of node dicts")

    try:
        sizes = [int(x) for x in args.field_sizes.split(",")]
        b = Builder(pipeline, sizes)
        states = b.build()
        # The IR's own progress condition: a loop is only a real loop if nothing
        # on it moves the cursor.  Anything else terminates by running out of
        # packet, so it is emitted as-is rather than unrolled.
        if b.nonconsuming_cycle(states):
            raise Unsupported(
                "the parser has a cycle that consumes no bits, so it never "
                "terminates; the IR rejects this too (ParserWellFormed's "
                "progress condition)")
        if args.input_bits is not None:
            if args.input_bits < 0:
                raise Unsupported("--input-bits cannot be negative")
            states = b.unroll_by_cursor(states, 1, args.input_bits)
            if b.overruns:
                print(f"warning: {args.pipeline}: {len(b.overruns)} extraction(s) "
                      f"run past the {args.input_bits}-bit packet and are "
                      f"emitted as Accept:", file=sys.stderr)
                for lbl, cur, w in b.overruns:
                    print(f"  state {lbl} at cursor {cur} wants {w} bits "
                          f"({cur + w} > {args.input_bits})", file=sys.stderr)
                # print("ParserHawk treats an over-long extraction as a NO-OP that freezes "
                #       "the fields\nand leaves the cursor put, so every later extraction "
                #       "is a no-op too; the IR\nwould REJECT instead.  Accepting matches "
                #       "the field values.  A pipeline that\nrelies on this is depending on "
                #       "running off the end of the packet.", file=sys.stderr)
        out = render(b, states, 1, args.input_bits)
    except Unsupported as e:
        sys.exit(f"cannot lower: {e}")

    if args.output:
        open(args.output, "w").write(out)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(out)

if __name__ == "__main__":
    main()
