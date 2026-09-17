#include "bootleg_bpf.h"

struct bpf_map_def {
  __u32 type, key_size, value_size, max_entries, map_flags;
};

struct bpf_map_def SEC("maps") counters = {
  .type = 1,
  .key_size = sizeof(__u32),
  .value_size = sizeof(__u64),
  .max_entries = 64,
  .map_flags = 0,
};

SEC("xdp") int prog(struct xdp_md *ctx)
{
    __u32 key = ctx->ingress_ifindex;
    __u64 *v = bpf_map_lookup_elem(&counters, &key);
    if (v)
        return 0;
    __u64 fresh = 7;
    bpf_map_update_elem(&counters, &key, &fresh, BPF_ANY);
    return 0;
}
