/* p4lang/p4c issue #5765 -- GlobalCopyPropagation propagates a stale constant
 * across an out argument.  https://github.com/p4lang/p4c/issues/5765
 *
 * `temp` is assigned 100, then written by random() through its `out`
 * parameter, then read by an action.  The pass should drop `temp` from its
 * constant map at the call and does not: checkParametersForMap removes
 * variables matching the CALLEE's formal parameter name (`result`) rather than
 * the actual argument (`temp`).  So the action is rewritten to
 * `hdr.h.res = 32w100`, discarding what random wrote.
 *
 * The `hdr.h.a = temp` line is load-bearing: without a use, `temp = 100` is
 * dead-store-eliminated before the pass runs and there is no stale constant
 * left to propagate.
 *
 * Reproduced by run.sh; see that script for how the two compilations are
 * obtained without needing two compilers.
 */
#include <core.p4>
#include <v1model.p4>
header h_t { bit<32> a; bit<32> res; }
struct headers  { h_t h; }
struct metadata { }
parser MyParser(packet_in p, out headers hdr, inout metadata m, inout standard_metadata_t sm) {
    state start { p.extract(hdr.h); transition accept; }
}
control MyVerifyChecksum(inout headers hdr, inout metadata m) { apply { } }
control MyIngress(inout headers hdr, inout metadata m, inout standard_metadata_t sm) {
    bit<32> temp;
    action use_it() { hdr.h.res = temp; }   // reads temp
    apply {
        temp = 100;
        hdr.h.a = temp;                     // a use, so the store survives DCE
        random(temp, 32w0, 32w10);          // writes temp through an out param
        use_it();                            // must see what random wrote
    }
}
control MyEgress(inout headers hdr, inout metadata m, inout standard_metadata_t sm) { apply { } }
control MyComputeChecksum(inout headers hdr, inout metadata m) { apply { } }
control MyDeparser(packet_out p, in headers hdr) { apply { p.emit(hdr.h); } }
V1Switch(MyParser(), MyVerifyChecksum(), MyIngress(), MyEgress(), MyComputeChecksum(), MyDeparser()) main;
