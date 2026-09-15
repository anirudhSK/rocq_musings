/* The same dispatch written as an if/else chain, with the parameter inlined. */
#include <core.p4>
#include <v1model.p4>

header calc_t { bit<8> op; bit<32> a; bit<32> b; bit<32> res; }
struct headers  { calc_t calc; }
struct metadata { }

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
                inout standard_metadata_t sm) {
    state start { packet.extract(hdr.calc); transition accept; }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    action do_add()          { hdr.calc.res = hdr.calc.a + hdr.calc.b; }
    action do_sub()          { hdr.calc.res = hdr.calc.a - hdr.calc.b; }
    action set(bit<32> v)    { hdr.calc.res = v; }
    action do_zero()         { hdr.calc.res = 0; }

    apply {
        if (hdr.calc.op == 8w1) {
            do_add();
        } else {
            if (hdr.calc.op == 8w2) {
                do_sub();
            } else {
                if (hdr.calc.op == 8w3) {
                    hdr.calc.res = 32w0xdeadbeef;
                } else {
                    do_zero();
                }
            }
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) { apply { } }
control MyComputeChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyDeparser(packet_out packet, in headers hdr) { apply { packet.emit(hdr.calc); } }

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
