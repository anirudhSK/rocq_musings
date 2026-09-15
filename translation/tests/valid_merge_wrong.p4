/* The hand-written condition with the tunnelled protocol wrong: the control. */
#include <core.p4>
#include <v1model.p4>

header eth_t { bit<16> ety; }
header tun_t { bit<16> proto; }
header ip_t  { bit<32> src; }
header out_t { bit<32> res; }

struct headers  { eth_t eth; tun_t tun; ip_t ip; out_t result; }
struct metadata { }

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
                inout standard_metadata_t sm) {
    state start {
        packet.extract(hdr.eth);
        transition select(hdr.eth.ety) {
            16w0x1212: parse_tun;
            16w0x0800: parse_ip;
            default: accept;
        }
    }
    state parse_tun {
        packet.extract(hdr.tun);
        transition select(hdr.tun.proto) { 16w0x0800: parse_ip; default: accept; }
    }
    state parse_ip { packet.extract(hdr.ip); transition accept; }
}
control MyVerifyChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    action take() { hdr.result.res = hdr.ip.src; }
    action none() { hdr.result.res = 0; }

    apply {
        if (hdr.eth.ety == 16w0x0800
            || (hdr.eth.ety == 16w0x1212 && hdr.tun.proto == 16w0x0801)) {
            take();
        } else {
            none();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) { apply { } }
control MyComputeChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyDeparser(packet_out packet, in headers hdr) { apply { packet.emit(hdr.result); } }

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
