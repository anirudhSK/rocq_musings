/*
 * Katran's xdp_pktcntr.c, verbatim from the map declarations onwards; only the
 * includes are replaced, by ex/ebpf-se/ebpf_se_common.h, so it builds without a
 * kernel tree.  A production XDP packet counter: two legacy-style maps, two
 * bpf_map_lookup_elem calls with constant keys, and a NULL check on each.
 *
 * It returns XDP_PASS on every path, so the emitted packet is constant: what
 * distinguishes it from ex/ebpf-se/xdp_pktcntr_alt.c is the counter it leaves
 * in the map region, and nothing else.
 *
 * Upstream: https://github.com/facebookincubator/katran, vendored in
 * https://github.com/dslab-epfl/ebpf-se (examples/katran).
 */
#include "ebpf_se_common.h"

#define CTRL_ARRAY_SIZE 2
#define CNTRS_ARRAY_SIZE 512




struct bpf_map_def SEC("maps") ctl_array = {
  .type = BPF_MAP_TYPE_ARRAY,
  .key_size = sizeof(__u32),
  .value_size = sizeof(__u32),
  .max_entries = CTRL_ARRAY_SIZE,
};

struct bpf_map_def SEC("maps") cntrs_array = {
  .type = BPF_MAP_TYPE_PERCPU_ARRAY,
  .key_size = sizeof(__u32),
  .value_size = sizeof(__u64),
  .max_entries = CNTRS_ARRAY_SIZE,
};

SEC("xdp-pktcntr")
int pktcntr(struct xdp_md *ctx) {
  void *data_end = (void *)(long)ctx->data_end;
  void *data = (void *)(long)ctx->data;
  __u32 ctl_flag_pos = 0;
  __u32 cntr_pos = 0;
  __u32* flag = bpf_map_lookup_elem(&ctl_array, &ctl_flag_pos);

  if (!flag || (*flag == 0)) {
    return XDP_PASS;
  };


  __u64* cntr_val = bpf_map_lookup_elem(&cntrs_array, &cntr_pos);
  if (cntr_val) {
    *cntr_val += 1;
  };
  return XDP_PASS;
}

char _license[] SEC("license") = "GPL";
