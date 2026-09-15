/*
 * ebpf-se's examples/fw/xdp_map_access_kern.c, verbatim from the map
 * declaration onwards, with the unused swap_src_dst_mac helper dropped (it is
 * already commented out at both call sites upstream).
 *
 * This is the program bpf_map_update_elem was added for: a lookup, and on a
 * miss an update writing a fresh value back.  It returns XDP_DROP on every
 * path, so what distinguishes it from ex/ebpf-se/map_access_alt.c is only the
 * final contents of the map region.
 *
 * Upstream: https://github.com/dslab-epfl/ebpf-se (examples/fw).
 */
#include "ebpf_se_common.h"

struct {
	__uint(type, BPF_MAP_TYPE_PERCPU_HASH);
	__type(key, struct dummy_key);
	__type(value, long);
	__uint(max_entries, 256);
} rxcnt SEC(".maps");


SEC("xdp_map_acces")
int xdp_prog1(struct xdp_md *ctx)
{
	void *data_end = (void *)(long)ctx->data_end;
	void *data = (void *)(long)ctx->data;
	struct ethhdr *eth = data;
	struct dummy_key key = {0};
	int rc = XDP_DROP;
	long *value;
	u16 h_proto;
	u64 nh_off;
	long dummy_value = 1;

	nh_off = sizeof(*eth);
	if (data + nh_off > data_end)
		return rc;

//	swap_src_dst_mac(data);
//	rc = XDP_TX;

	h_proto = eth->h_proto;
	key.key = 23;
	
	value = bpf_map_lookup_elem(&rxcnt, &key);
	if (value){
		*value += 1;
	}else{
		bpf_map_update_elem(&rxcnt, &key, &dummy_value, BPF_ANY);
	}
	return rc;
}

char _license[] SEC("license") = "GPL";
