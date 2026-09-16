#include <core.p4>
#include <v1model.p4>

header ethernet_t {
    bit<48> dstAddr;
    bit<48> srcAddr;
    bit<16> etherType;
}

struct headers {
    ethernet_t eth;
}

parser MyParser(
    packet_in packet,
    out headers hdr,
    inout metadata meta,
    inout standard_metadata_t standard_metadata
) {
    state start {
        packet.extract(hdr.eth);
        transition accept;
    }
}

control MyIngress(
    inout headers hdr,
    inout metadata meta,
    inout standard_metadata_t standard_metadata
) {
    apply {
        if (hdr.eth.isValid() &&
            hdr.eth.etherType == 16w0x0800) {
            // continue
        } else {
            mark_to_drop(standard_metadata);
        }
    }
}

control MyEgress(
    inout headers hdr,
    inout metadata meta,
    inout standard_metadata_t standard_metadata
) {
    apply {
    }
}

control MyVerifyChecksum(
    inout headers hdr,
    inout metadata meta
) {
    apply {
    }
}

control MyComputeChecksum(
    inout headers hdr,
    inout metadata meta
) {
    apply {
    }
}

control MyDeparser(
    packet_out packet,
    in headers hdr
) {
    apply {
        packet.emit(hdr.eth);
    }
}

V1Switch(
    MyParser(),
    MyVerifyChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;
