/* The same Tofino-native rotate, written with shifts.
 *
 * A minimal Tofino-native program: a sub-parser that extracts the intrinsic
 * metadata and advances past the port metadata, then the packet proper.  This
 * exercises the TNA path itself -- intrinsic metadata as Headers, pkt.advance,
 * and sub-parser inlining -- rather than anything about the arithmetic, which
 * rotl5_concat / rotl5_shift already cover for v1model.
 */
#include <core.p4>
#include <tna.p4>

header data_t { bit<32> v; bit<32> res; }
struct headers_t  { data_t data; }
struct meta_t     { bit<32> scratch; }

parser TofinoIngressParser(packet_in pkt, out ingress_intrinsic_metadata_t ig_intr_md) {
    state start {
        pkt.extract(ig_intr_md);
        pkt.advance(PORT_METADATA_SIZE);
        transition accept;
    }
}

parser SwitchIngressParser(packet_in pkt, out headers_t hdr, out meta_t ig_md,
                           out ingress_intrinsic_metadata_t ig_intr_md) {
    TofinoIngressParser() tofino_parser;
    state start {
        tofino_parser.apply(pkt, ig_intr_md);
        transition parse_data;
    }
    state parse_data {
        pkt.extract(hdr.data);
        transition accept;
    }
}

control SwitchIngress(inout headers_t hdr, inout meta_t ig_md,
                      in ingress_intrinsic_metadata_t ig_intr_md,
                      in ingress_intrinsic_metadata_from_parser_t ig_prsr_md,
                      inout ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md,
                      inout ingress_intrinsic_metadata_for_tm_t ig_tm_md) {
    action go() { hdr.data.res = (hdr.data.v << 5) | (hdr.data.v >> 27); }
    apply { go(); }
}

control SwitchIngressDeparser(packet_out pkt, inout headers_t hdr, in meta_t ig_md,
                              in ingress_intrinsic_metadata_for_deparser_t ig_dprsr_md) {
    apply { pkt.emit(hdr.data); }
}

parser SwitchEgressParser(packet_in pkt, out headers_t hdr, out meta_t eg_md,
                          out egress_intrinsic_metadata_t eg_intr_md) {
    state start { transition accept; }
}
control SwitchEgress(inout headers_t hdr, inout meta_t eg_md,
                     in egress_intrinsic_metadata_t eg_intr_md,
                     in egress_intrinsic_metadata_from_parser_t eg_prsr_md,
                     inout egress_intrinsic_metadata_for_deparser_t eg_dprsr_md,
                     inout egress_intrinsic_metadata_for_output_port_t eg_oport_md) {
    apply { }
}
control SwitchEgressDeparser(packet_out pkt, inout headers_t hdr, in meta_t eg_md,
                             in egress_intrinsic_metadata_for_deparser_t eg_dprsr_md) {
    apply { }
}

Pipeline(SwitchIngressParser(), SwitchIngress(), SwitchIngressDeparser(),
         SwitchEgressParser(), SwitchEgress(), SwitchEgressDeparser()) pipe;
Switch(pipe) main;
