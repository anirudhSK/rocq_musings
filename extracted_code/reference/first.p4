#include <core.p4>
#include <v1model.p4>

header H {
    bit<8> a;
    bit<8> b;
}
struct Headers {
    H h;
}

struct Meta { }

parser p(packet_in pkt, out Headers hdr, inout Meta meta, inout standard_metadata_t stdmeta) {
    state start {
        pkt.extract(hdr.h);
        transition accept;
    }
}

control vrfy(inout Headers hdr, inout Meta meta) {
    apply { }
}

control ingress(inout Headers hdr, inout Meta m, inout standard_metadata_t s) {
    action MyAction1() {
        hdr.h.b = 1;
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

control egress(inout Headers hdr, inout Meta m, inout standard_metadata_t s) {
    apply { }
}

control update(inout Headers hdr, inout Meta m) {
    apply { }
}

control deparser(packet_out pkt, in Headers hdr) {
    apply {
        pkt.emit(hdr.h);
    }
}

V1Switch(
    p(),
    vrfy(),
    ingress(),
    egress(),
    update(),
    deparser()
) main;
