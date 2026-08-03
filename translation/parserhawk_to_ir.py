#!/usr/bin/env python3
"""
Lower a ParserHawk synthesized pipeline into the Caracara IR.

Emits either Rocq source (--format coq) or an s-expression .ir file
(--format ir) of the kind `Shim.load_general_program` reads, matching
test/parse_reject_deparse.ir.

Input is the JSON that `codegen()` returns in ParserHawk's `*_op.py` scripts --
a list of per-node dicts:

    {"Extraction": "field_2",
     "Tran_key": ["field2[7]", ..., "field2[0]"],
     "default_tran": 58,
     "tran_logic": [["val:6", "mask:65535", "nxt:6"], ...]}

Two things the pipeline JSON does NOT carry and that must be supplied:

  * field widths -- they live in `pkt_field_size_list` in the op script, so
    pass --field-sizes, or --op-script to scrape it.
  * the node count, used to decide which transition targets mean "accept".
    Taken from len(pipeline), which is `num_parser_nodes` by construction.

Mapping notes, and where they get non-obvious:

  node i            -> parser state label i+1        (positive is 1-based)
  default_tran/nxt  -> TargetState if < num_nodes, else Accept.  ParserHawk
                       emits out-of-range ids (53..59 in sai_v4) for accept:
                       `new_node` is a guarded no-op, so once idx leaves
                       [0, num_nodes) no further node fires.

  WIDE FIELDS.  `ExtractOpConstructor` coerces into a CrIntType, which tops out
  at u64, and `psd_action` allows one op per state.  A field wider than 64 bits
  is therefore split into ceil(w/64) chunks of <= 64 bits, each with its own
  header, extracted by a chain of states linked by `Unconditional`.  Chunks are
  cut 64-at-a-time from the MOST significant end (the wire order), so a 100-bit
  field becomes [64, 36].  The node's own transition hangs off the LAST chunk's
  state, and the node's entry label stays i+1 so inbound edges are unaffected.

  Tran_key -> sc_start_index/sc_end_index.  A SelectCase names ONE header and
  ONE contiguous slice, but a ParserHawk key is an arbitrary bit set, possibly
  spanning fields -- and, once a field is chunked, possibly straddling a chunk
  boundary.  Runs are cut on a single test: same header, and local bit index
  descending by exactly one.  Because a chunk boundary changes the header, that
  test also splits runs at chunk edges.

  A key that is one run becomes a single SelectCase.  Anything else is emitted
  as a CHAIN of zero-width decision states (psd_action = None), one per run, so
  the conjunction is expressed as a path.  Each run's failure edge targets the
  next tran_logic *entry*, not the next run, which keeps first-match-wins.

  Key bit order: `generate_tran_key` concatenates fields in index order and
  bits high-to-low, so the packed key is in natural MSB-first order.  The order
  bits appear in `Tran_key` is NOT that -- `custom_sort` in
  code_gen_big_tcam.py compares regex capture groups as strings, so it prints
  9,8,7,...,2,15,14,...,10,1,0.  This script re-sorts and ignores that.

  .ir output wraps the parser in a two-module network: the parser feeding a
  deparser that emits every allocated header, because `end_modules_are_deparsers`
  wants the sinks to be deparsers.  The declared packet length defaults to the
  longest extraction path through the parser (34 bits for sai_v4, which is
  ParserHawk's own input_bit_stream_size); override with --packet-len.

Unsupported, and rejected loudly rather than silently mistranslated:
  * `lookahead N` entries in Tran_key -- the IR cursor cannot peek.
  * `post process fieldN[b]` entries.
"""

import argparse
import json
import re
import sys

# --------------------------------------------------------------------------

BIT_RE = re.compile(r"^field(\d+)\[(\d+)\]$")
FIELD_RE = re.compile(r"^field_(\d+)$")

MAX_CHUNK = 64

COQ_TYPE = {8: "u8", 16: "u16", 32: "u32", 64: "u64"}
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


# --------------------------------------------------------------------------
# Structured build.  Targets are ("accept",) | ("reject",) | ("state", label);
# actions are None | ("extract", header, width); transitions are
# ("uncond", target) | ("select", [(header, lo, hi, value, target)], default).


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

        cases, fallthrough, chained = [], default, False
        for entry in reversed(logic):     # reversed: fall-through = next entry
            val, mask, nxt = parse_kv(entry)
            mask &= (1 << total) - 1
            if mask == 0:
                raise Unsupported(f"entry {entry!r} masks out every key bit")
            val &= mask
            cared = [i for i in range(total) if (mask >> (total - 1 - i)) & 1]
            runs = self.runs_of([bits[i] for i in cared], cared)
            tgt = self.target(nxt)

            if len(runs) == 1 and not chained:
                h, lo, hi, pos = runs[0]
                cases.append((h, lo, hi, run_value(val, total, pos), tgt))
            else:
                fallthrough = self.chain(runs, val, total, tgt, fallthrough)
                chained = True
        cases.reverse()

        if chained:
            for (h, lo, hi, v, tgt) in reversed(cases):
                fallthrough = self.chain([(h, lo, hi, None)], v, total,
                                         tgt, fallthrough, literal=v)
            return ("uncond", fallthrough)
        return ("select", cases, default)

    def chain(self, runs, val, total, target, fallthrough, literal=None):
        """One zero-width state per run; all must match to reach `target`."""
        labels = [self.fresh() for _ in runs]
        for i, (h, lo, hi, pos) in enumerate(runs):
            v = literal if literal is not None else run_value(val, total, pos)
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
        """Bits consumed on the longest extraction path.  0 if cyclic."""
        by_label = {s["label"]: s for s in states}

        def succs(s):
            t = s["trans"]
            outs = ([t[1]] if t[0] == "uncond"
                    else [c[4] for c in t[1]] + [t[2]])
            return [x[1] for x in outs if x[0] == "state"]

        memo, onstack = {}, set()

        def go(lbl):
            if lbl in onstack:
                raise Unsupported("parser graph has a cycle; pass --packet-len")
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


# --------------------------------------------------------------------------
# Renderers


def render_coq(b, states, start, name):
    def tgt(t):
        return {"accept": "Accept", "reject": "Reject"}.get(
            t[0], f"(TargetState (ParserStateLabelCtr {t[-1]}))")

    def bits(v, w):
        return "[" + ";".join("true" if (v >> (w - 1 - i)) & 1 else "false"
                              for i in range(w)) + "]"

    def trans(t):
        if t[0] == "uncond":
            return f"(Unconditional {tgt(t[1])})"
        cases = ";\n            ".join(
            f"mkSelectCase (HeaderCtr {h}) {lo} {hi} {bits(v, hi - lo)} {tgt(g)}"
            for (h, lo, hi, v, g) in t[1])
        return f"(Select [{cases}]\n              {tgt(t[2])})"

    body = ";\n".join(
        f"    mkParserStateDef (ParserStateLabelCtr {s['label']})\n"
        f"      " + ("None" if not s["action"] else
                     f"(Some (ExtractOpConstructor (HeaderCtr {s['action'][1]}) "
                     f"{s['action'][2]} {COQ_TYPE[width_slot(s['action'][2])]}))")
        + f"\n      {trans(s['trans'])}"
        for s in states)

    return ("(* Generated by translation/parserhawk_to_ir.py -- do not edit. *)\n"
            "(* Header allocation:\n"
            + "".join(f"   {l}\n" for l in b.legend()) + " *)\n"
            "From Stdlib Require Import List.\n"
            "Import ListNotations.\n"
            "From MyProject Require Import CrParser.\n"
            "From MyProject Require Import CrIdentifiers.\n"
            "From MyProject Require Import CrVal.\n"
            # ZArith last, as in TestParserPrograms.v: without it the positive
            # numeral notation is out of scope and `ParserStateLabelCtr 1`
            # elaborates 1 as nat.
            "From Stdlib Require Import ZArith.\n\n"
            f"Definition {name} : Parser :=\n"
            f"  mkParser (ParserStateLabelCtr {start}) [\n{body}\n  ].\n")


def parser_sexp(states, start):
    """The bare `Parser` record: ((parser_start N) (parser_states ...)).

    Identifiers are bare numbers: Header/ParserStateLabel/ModuleName are
    single-field records, which Coq extraction collapses to positive.  Likewise
    CrIntType collapses to CrWidth, hence a bare W64.
    """
    def tgt(t):
        return {"accept": "Accept", "reject": "Reject"}.get(
            t[0], f"(TargetState {t[-1]})")

    def pat(v, w):
        # sc_pattern is a `list bool`, MSB-first, rendered as the derived
        # Coq_cons chain -- CrTypeIF has no sugar for it.
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


def emit_ops(b):
    """EmitOpConstructor per allocated header, in allocation order."""
    out = []
    for f, entries in sorted(b.chunks.items()):
        for c in entries:
            out.append(f"(EmitOpConstructor {c['header']} {c['width']})")
    return out


def render_parser(b, states, start, packet_len):
    """Just the Parser, for wrapping by hand (e.g. sai_dump_headers).

    Sexplib skips `;` line comments, so the preamble still loads.  It carries
    the two things the caller needs to build a wrapper around this: the packet
    length, and the deparser emit list that covers every header written here.
    """
    lines = ["; Generated by translation/parserhawk_to_ir.py -- a bare CrParser.Parser.",
             "; Header allocation:"]
    lines += [f";   {l}" for l in b.legend()]
    lines.append(f"; Longest extraction path: {packet_len} bits "
                 "(use as GeneralCaracaraProgramDef's input length).")
    lines.append("; Deparser emits covering every header written here:")
    lines.append(";   " + " ".join(emit_ops(b)))
    return "\n".join(lines) + "\n" + parser_sexp(states, start) + "\n"


def render_ir(b, states, start, packet_len):
    """S-expression GeneralCaracaraProgram, as in test/parse_reject_deparse.ir."""
    parser = parser_sexp(states, start)
    # A deparser sink, so end_modules_are_deparsers holds.  Emits every header
    # the parser could have written, in allocation order.
    deparser = f"(DeparserModule 2 {coq_list(emit_ops(b))})"
    net = (f"((net_modules {coq_list([f'(ParserModule 1 {parser})', deparser])}) "
           f"(net_edges ((1 2))) (start_module 1))")
    return f"(GeneralCaracaraProgramDef {packet_len} Coq_nil\n {net})\n"


# --------------------------------------------------------------------------


def scrape_field_sizes(path):
    src = open(path).read()
    m = re.search(r"^pkt_field_size_list\s*=\s*\[([^\]]*)\]", src, re.M)
    if not m:
        raise Unsupported(f"no pkt_field_size_list in {path}")
    return [int(x) for x in m.group(1).replace(" ", "").split(",") if x]


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("pipeline", help="ParserHawk pipeline JSON")
    ap.add_argument("--field-sizes", help="comma-separated, e.g. 1,16,8,8,8,1,1,1,1")
    ap.add_argument("--op-script", help="scrape pkt_field_size_list from this *_op.py")
    ap.add_argument("--format", choices=("coq", "ir", "parser"), default="coq",
                    help="coq source (default); 'ir' for a GeneralCaracaraProgram "
                         "s-expression; 'parser' for just the Parser s-expression")
    ap.add_argument("--name", default="p_parserhawk",
                    help="Rocq definition name (--format coq only)")
    ap.add_argument("--packet-len", type=int,
                    help="declared packet length in bits (--format ir); "
                         "defaults to the longest extraction path")
    ap.add_argument("--start", type=int, default=0, help="start node id (default 0)")
    ap.add_argument("-o", "--output", help="write here instead of stdout")
    args = ap.parse_args()

    if args.field_sizes:
        sizes = [int(x) for x in args.field_sizes.split(",")]
    elif args.op_script:
        sizes = scrape_field_sizes(args.op_script)
    else:
        ap.error("need --field-sizes or --op-script")

    pipeline = json.load(open(args.pipeline))
    if not isinstance(pipeline, list):
        sys.exit("pipeline JSON must be a list of node dicts")

    try:
        b = Builder(pipeline, sizes)
        states = b.build()
        start = args.start + 1
        if args.format == "coq":
            out = render_coq(b, states, start, args.name)
        else:
            plen = (args.packet_len if args.packet_len is not None
                    else b.longest_path(states, start))
            out = (render_parser(b, states, start, plen) if args.format == "parser"
                   else render_ir(b, states, start, plen))
    except Unsupported as e:
        sys.exit(f"cannot lower: {e}")

    if args.output:
        open(args.output, "w").write(out)
        print(f"wrote {args.output}", file=sys.stderr)
    else:
        sys.stdout.write(out)


if __name__ == "__main__":
    main()
