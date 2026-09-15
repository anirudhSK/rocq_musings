/* deparse_table.p4 with the second emit dropped.  The control for that pair:
 * without it, a lowering that silently discards a table-dispatched deparser
 * body would make deparse_direct and deparse_table agree by both emitting
 * nothing, and the Equivalent verdict above would mean nothing.
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
    }
    @hidden table tbl_emit_all {
        actions = { emit_all(); }
        const default_action = emit_all();
    }
    apply { tbl_emit_all.apply(); }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
