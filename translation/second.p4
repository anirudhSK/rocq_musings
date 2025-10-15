#include <core.p4>
#include <v1model.p4>

// Header definition
header H {
    bit<8> a;
}

// Headers struct - must contain all headers
struct Headers {
    H h;
}

// Metadata struct
struct Meta { }

// Parser
parser p(packet_in pkt, out Headers hdr, inout Meta meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract(hdr.h);
        transition accept;
    }
}

// Verify checksum control
control vrfy(inout Headers hdr, inout Meta meta) {
    apply { }
}

// Ingress control
control ingress(inout Headers hdr, inout Meta m, inout standard_metadata_t s) {
    action MyAction1() {
        hdr.h.a = 1;
    }
    
    table the_table {
        key = {
            hdr.h.a : exact;
        }
        actions = {
            MyAction1;
        }
        size = 1024;
        default_action = MyAction1();
    }
    
    apply {
        the_table.apply();
    }
}

// Egress control
control egress(inout Headers hdr, inout Meta m, inout standard_metadata_t s) {
    apply { }
}

// Update checksum control
control update(inout Headers hdr, inout Meta m) {
    apply { }
}

// Deparser
control deparser(packet_out pkt, in Headers hdr) {
    apply {
        pkt.emit(hdr.h);
    }
}

// Main switch instantiation
V1Switch(
    p(),
    vrfy(),
    ingress(),
    egress(),
    update(),
    deparser()
) main;