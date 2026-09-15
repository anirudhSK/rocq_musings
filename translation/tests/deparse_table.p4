/* The same deparser as deparse_direct.p4, written the way p4c's MIDEND leaves
 * one: SynthesizeActions wraps the body into a @hidden action and
 * MoveActionsToTables dispatches it from a keyless table with a const default
 * action.  Both spellings emit the same two headers.
 *
 * This pair exists because the lowering used to walk only the top-level
 * statements of a deparser and SKIP what it did not recognise, so this side
 * emitted nothing at all -- a packet short by every header, with no diagnostic.
 * A relative test from source pins it without needing a midend dump.
 */
#include <core.p4>
#include <v1model.p4>

header a_t { bit<32> x; }
header b_t { bit<16> y; }
struct headers  { a_t a; b_t b; }
struct metadata { }

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
                inout standard_metadata_t sm) {
    state start { packet.extract(hdr.a); packet.extract(hdr.b); transition accept; }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    apply { hdr.a.x = hdr.a.x + 1; }
}
control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) { apply { } }
control MyComputeChecksum(inout headers hdr, inout metadata meta) { apply { } }

control MyDeparser(packet_out packet, in headers hdr) {
    @hidden action emit_all() {
        packet.emit(hdr.a);
        packet.emit(hdr.b);
    }
    @hidden table tbl_emit_all {
        actions = { emit_all(); }
        const default_action = emit_all();
    }
    apply { tbl_emit_all.apply(); }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
