#include "bootleg_bpf.h"

#define SEC(NAME) __attribute__((section(NAME), used))
SEC("xdp")
int bpf_ex0(struct xdp_md *ctx) {
  void *data = (void *)(long)ctx->data;
  void *data_end = (void *)(long)ctx->data_end;
  struct ethhdr* hdr = data;
  if (data + sizeof(struct ethhdr) + 1 > data_end) {
    return XDP_ABORTED;
  }

  __u16 protocol = hdr->h_proto;
  if (protocol == __builtin_bswap16(ETH_P_IP)) {
    return XDP_PASS;
  } else {
    return XDP_DROP;
  }
}
char _license[] SEC("license") = "GPL";