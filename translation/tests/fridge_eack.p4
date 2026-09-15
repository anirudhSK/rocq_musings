/*
 * DERIVED FROM Princeton-Cabernet/p4-projects, Fridge-tofino/p4src/calc_tcp_eack.p4
 *
 *   Unbiased delay measurement in the data plane
 *   Copyright (C) 2021 Xiaoqi Chen, Princeton University
 *
 *   This program is free software: you can redistribute it and/or modify it
 *   under the terms of the GNU Affero General Public License as published by
 *   the Free Software Foundation, either version 3 of the License, or (at your
 *   option) any later version.  This program is distributed in the hope that it
 *   will be useful, but WITHOUT ANY WARRANTY; without even the implied warranty
 *   of MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU Affero
 *   General Public License for more details.  You should have received a copy
 *   of the GNU Affero General Public License along with this program.  If not,
 *   see <https://www.gnu.org/licenses/>.
 *
 * The arithmetic below is transcribed from that file; the harness around it
 * (v1model instead of TNA, a result header instead of an `out` parameter) is
 * ours.  See translation/tests/README.md.
 */
/* Fridge-tofino's calc_tcp_eack, as a v1model program.
 *
 * The original is a Tofino control module with an `out bit<32> eack`; here the
 * result lands in a header so the deparser can emit it and the checker can
 * compare it.  Everything else is the source's own shape: the shifts written
 * as concatenations with zero, the nested if/else, and the isValid test that
 * the parser's select is what really decides.
 */
#include <core.p4>
#include <v1model.p4>

#define TCP_FLAGS_S 8w2

header ipv4_t { bit<4> version; bit<4> ihl; bit<16> total_len; bit<8> protocol; }
header tcp_t  { bit<32> seq_no; bit<4> data_offset; bit<8> flags; }
header out_t  { bit<32> eack; }

struct headers  { ipv4_t ipv4; tcp_t tcp; out_t result; }
struct metadata {
    bit<32> tmp_1;
    bit<32> tmp_2;
    bit<32> tmp_3;
    bit<32> total_hdr_len_bytes;
    bit<32> total_body_len_bytes;
}

parser MyParser(packet_in packet, out headers hdr, inout metadata meta,
                inout standard_metadata_t sm) {
    state start {
        packet.extract(hdr.ipv4);
        transition select(hdr.ipv4.protocol) { 8w6: parse_tcp; default: accept; }
    }
    state parse_tcp { packet.extract(hdr.tcp); transition accept; }
}

control MyVerifyChecksum(inout headers hdr, inout metadata meta) { apply { } }

control MyIngress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) {
    action step1a() { meta.tmp_1 = (bit<32>) (hdr.ipv4.ihl ++ 2w0); }
    action step1b() { meta.tmp_2 = (bit<32>) (hdr.tcp.data_offset ++ 2w0); }
    action step1c() { meta.tmp_3 = 16w0 ++ hdr.ipv4.total_len; }
    action step2()  { meta.total_hdr_len_bytes = meta.tmp_1 + meta.tmp_2; }
    action step3()  { meta.total_body_len_bytes = meta.tmp_3 - meta.total_hdr_len_bytes; }
    action step4()  { hdr.result.eack = hdr.tcp.seq_no + meta.total_body_len_bytes; }
    action bump()   { hdr.result.eack = hdr.result.eack + 1; }
    action zero()   { hdr.result.eack = 0; }

    apply {
        if (hdr.tcp.isValid()) {
            step1a(); step1b(); step1c();
            step2();
            step3();
            step4();
            if (hdr.tcp.flags == TCP_FLAGS_S) { bump(); }
        } else {
            zero();
        }
    }
}

control MyEgress(inout headers hdr, inout metadata meta, inout standard_metadata_t sm) { apply { } }
control MyComputeChecksum(inout headers hdr, inout metadata meta) { apply { } }
control MyDeparser(packet_out packet, in headers hdr) { apply { packet.emit(hdr.result); } }

V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(),
         MyComputeChecksum(), MyDeparser()) main;
