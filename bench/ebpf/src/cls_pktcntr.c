/*
 * Katran's adapter_integration_test_kern.c, verbatim from the map declarations
 * onwards.  The same counter over struct __sk_buff instead of struct xdp_md.
 *
 * Its section name is "cls-pktcntr", a katran convention rather than a libbpf
 * program type, so bpf_to_ir cannot infer the context from it and refuses --
 * pass --ctx=__sk_buff.  That refusal is the point: guessing would model a
 * different program.
 *
 * Upstream: https://github.com/facebookincubator/katran, vendored in
 * https://github.com/dslab-epfl/ebpf-se (examples/katran/adapter_integration_test_kern.c).
 */
#include "ebpf_se_common.h"

#define CTRL_ARRAY_SIZE 2
#define CNTRS_ARRAY_SIZE 512



/*
 * map_fd #0
 */

struct bpf_map_def SEC("maps") ctl_array = {
  .type = BPF_MAP_TYPE_ARRAY,
  .key_size = sizeof(__u32),
  .value_size = sizeof(__u32),
  .max_entries = CTRL_ARRAY_SIZE,
};


/*
 * map_fd #1
 */
struct bpf_map_def SEC("maps") cntrs_array = {
 // @lint-ignore TXT2 T25377293 Grandfathered in
	.type = BPF_MAP_TYPE_PERCPU_ARRAY,
  .key_size = sizeof(__u32),
  .value_size = sizeof(__u64),
  .max_entries = CNTRS_ARRAY_SIZE,
};

SEC("cls-pktcntr")
int pktcntr(struct __sk_buff *skb) {
  __u32 ctl_flag_pos = 0;
  __u32 cntr_pos = 0;
  __u32* flag = bpf_map_lookup_elem(&ctl_array, &ctl_flag_pos);

  if (!flag || (*flag == 0)) {
    return TC_ACT_OK;
  };


  __u64* cntr_val = bpf_map_lookup_elem(&cntrs_array, &cntr_pos);
  if (cntr_val) {
    *cntr_val += 1;
  };
  return TC_ACT_OK;
}

char _license[] SEC("license") = "GPL";
