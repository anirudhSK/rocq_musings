#include <core.p4>
#include <v1model.p4>

header MyHeader_h {
    bit<32> dstAddr;
    bit<32> srcAddr;
    bit<32> protocol;
}

struct Headers {
    MyHeader_h hdr;
}

struct Metadata {
}

parser MyParser(packet_in packet,
                out Headers headers,
                inout Metadata meta,
                inout standard_metadata_t sm) {
    state start {
        packet.extract(headers.hdr);
        transition accept;
    }
}

control MyIngress(inout Headers headers,
                  inout Metadata meta,
                  inout standard_metadata_t sm) {


    action drop_pkt() {
        headers.hdr.dstAddr = headers.hdr.dstAddr + 1;
        headers.hdr.dstAddr -=  1;
    }

    action forward_pkt() {
        headers.hdr.dstAddr = headers.hdr.dstAddr + 1;
    }



    table routing_table {
        key = {
            headers.hdr.dstAddr : exact; 
        }
        actions = {
            drop_pkt;
            forward_pkt;
        }
        
        const entries = {
            1  : drop_pkt();  
            6  : forward_pkt(); 
        }
    }

    apply {
        routing_table.apply();
    }
}


control MyComputeChecksum(inout Headers headers, inout Metadata meta) {
    apply { }
}

control MyEgress(inout Headers headers, inout Metadata meta, inout standard_metadata_t sm) {
    apply { }
}

control MyDeparser(packet_out packet, in Headers headers) {
    apply {
        packet.emit(headers.hdr);
    }
}

V1Switch(
    MyParser(),
    MyComputeChecksum(),
    MyIngress(),
    MyEgress(),
    MyComputeChecksum(),
    MyDeparser()
) main;