"""
Lower a ParserHawk synthesized pipeline into a Caracara IR `Parser` s-expression.
Emits just the Parser record for JSON that `codegen()` returns in ParserHawk's `*_op.py` scripts.

Unsupported:
* `lookahead N` entries in Tran_key (the IR cursor does not currently support peeking).
* `post process fieldN[b]` entries.
"""

import argparse
import json
import re
import sys

BIT_RE = re.compile(r"^field(\d+)\[(\d+)\]$")
FIELD_RE = re.compile(r"^field_(\d+)$")

MAX_CHUNK = 64

IR_TYPE = {8: "W8", 16: "W16", 32: "W32", 64: "W64"}

class Unsupported(Exception):
    pass

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
    """Tran_key -> [(field, bit)] in natural packing order (field asc, bit desc)."""
    bits = []
    for entry in tran_key:
        m = BIT_RE.match(entry.strip())
        if not m:
            if "lookahead" in entry:
                raise Unsupported(
                    f"key entry {entry!r}: the IR has no lookahead -- extraction "
                    "advances the cursor irreversibly."
                )
            raise Unsupported(f"unrecognized Tran_key entry {entry!r}")
        bits.append((int(m.group(1)), int(m.group(2))))
    return sorted(set(bits), key=lambda fb: (fb[0], -fb[1]))

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

    def runs_of(self, bits, positions):
        """Maximal (same header, consecutive local index) runs; splits at chunks."""
        located = [self.locate(f, b) + (p,) for (f, b), p in zip(bits, positions)]
        runs, cur = [], []
        for item in located:
            if cur and item[0] == cur[-1][0] and item[1] == cur[-1][1] - 1:
                cur.append(item)
            else:
                if cur:
                    runs.append(cur)
                cur = [item]
        if cur:
            runs.append(cur)
        return [(r[0][0], r[-1][1], r[0][1] + 1, [x[2] for x in r]) for r in runs]

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

        bits = parse_key(node.get("Tran_key") or [])
        if not bits:
            raise Unsupported("node has tran_logic but an empty Tran_key")
        total = len(bits)

        decoded = []
        for entry in logic:
            val, mask, nxt = parse_kv(entry)
            mask &= (1 << total) - 1
            if mask == 0:
                raise Unsupported(f"entry {entry!r} masks out every key bit")
            val &= mask
            cared = [i for i in range(total) if (mask >> (total - 1 - i)) & 1]
            decoded.append((self.runs_of([bits[i] for i in cared], cared),
                            val, self.target(nxt)))

        if all(len(runs) == 1 for (runs, _, _) in decoded):
            cases = []
            for (runs, val, tgt) in decoded:
                h, lo, hi, pos = runs[0]
                cases.append((h, lo, hi, run_value(val, total, pos), tgt))
            return ("select", cases, default)

        fallthrough = default
        for (runs, val, tgt) in reversed(decoded):
            fallthrough = self.chain(runs, val, total, tgt, fallthrough)
        return ("uncond", fallthrough)

    def chain(self, runs, val, total, target, fallthrough):
        """One zero-width state per run; all must match to reach `target`."""
        labels = [self.fresh() for _ in runs]
        for i, (h, lo, hi, pos) in enumerate(runs):
            v = run_value(val, total, pos)
            # Intermediate links are ParserTargets, not bare labels.
            nxt = target if i == len(runs) - 1 else ("state", labels[i + 1])
            self.extra.append({
                "label": labels[i], "action": None,
                "trans": ("select", [(h, lo, hi, v, nxt)], fallthrough)})
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

    def longest_path(self, states, start):
        """Bits consumed on the longest extraction path."""
        by_label = {s["label"]: s for s in states}

        def succs(s):
            t = s["trans"]
            outs = ([t[1]] if t[0] == "uncond"
                    else [c[4] for c in t[1]] + [t[2]])
            return [x[1] for x in outs if x[0] == "state"]

        memo, onstack = {}, set()

        def go(lbl):
            if lbl in onstack:
                raise Unsupported("parser graph has a cycle; longest path is unbounded")
            if lbl in memo:
                return memo[lbl]
            s = by_label.get(lbl)
            if s is None:
                return 0
            w = s["action"][2] if s["action"] else 0
            onstack.add(lbl)
            best = w + max([go(x) for x in succs(s)] + [0])
            onstack.discard(lbl)
            memo[lbl] = best
            return best

        return go(start)

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
        h, lo, hi, v, g = c
        return (f"((sc_header {h}) (sc_start_index {lo}) (sc_end_index {hi}) "
                f"(sc_pattern {pat(v, hi - lo)}) (sc_target {tgt(g)}))")

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

def render(b, states, start):
    """Parser sexp, with a `;` preamble.  Sexplib skips those, so it still loads."""
    lines = ["; Generated by translation/parserhawk_to_ir.py -- a bare CrParser.Parser.",
             "; Header allocation:"]
    lines += [f";   {l}" for l in b.legend()]
    lines.append(f"; Longest extraction path: {b.longest_path(states, start)} bits "
                 "(use as GeneralCaracaraProgramDef's input length).")
    lines.append("; Deparser emits covering every header written here:")
    lines.append(";   " + " ".join(b.emit_ops()))
    return "\n".join(lines) + "\n" + parser_sexp(states, start) + "\n"

def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pipeline", help="ParserHawk pipeline JSON")
    ap.add_argument("--field-sizes", required=True,
                    help="comma-separated pkt_field_size_list, e.g. 1,16,8,8,8,1,1,1,1")
    ap.add_argument("-o", "--output", help="write here instead of stdout")
    args = ap.parse_args()

    pipeline = json.load(open(args.pipeline))
    if not isinstance(pipeline, list):
        sys.exit("pipeline JSON must be a list of node dicts")

    try:
        sizes = [int(x) for x in args.field_sizes.split(",")]
        b = Builder(pipeline, sizes)
        states = b.build()
        out = render(b, states, 1)
    except Unsupported as e:
        sys.exit(f"cannot lower: {e}")

    if args.output:
        open(args.output, "w").write(out)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(out)

if __name__ == "__main__":
    main()
