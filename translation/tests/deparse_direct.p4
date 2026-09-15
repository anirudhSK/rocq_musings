/* A deparser written the way a person writes one: emits straight in `apply`. */
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
    apply {
        packet.emit(hdr.a);
        packet.emit(hdr.b);
    }
}

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
