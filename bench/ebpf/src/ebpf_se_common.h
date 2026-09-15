/*
 * Enough of <linux/bpf.h>, <linux/if_ether.h>, <linux/pkt_cls.h> and libbpf's
 * bpf_helpers.h for the programs in this directory to build without a kernel
 * tree.  The field OFFSETS are what matter: the translator turns each context
 * access into a load at that offset into the ctx region, so a wrong one here
 * silently models a different program.  ex/ebpf-se/offsets.c static-asserts
 * the ones these programs read.
 */
#ifndef EBPF_SE_COMMON_H
#define EBPF_SE_COMMON_H

typedef unsigned char       __u8;
typedef unsigned short      __u16;
typedef unsigned int        __u32;
typedef unsigned long long  __u64;
typedef __u16 u16;
typedef __u64 u64;

#define SEC(N) __attribute__((section(N), used))
#define __uint(name, val) int (*name)[val]
#define __type(name, val) typeof(val) *name

/* map types (uapi values; only recorded, never interpreted) */
#define BPF_MAP_TYPE_ARRAY         2
#define BPF_MAP_TYPE_PERCPU_HASH   5
#define BPF_MAP_TYPE_PERCPU_ARRAY  6

/* update flags */
#define BPF_ANY     0
#define BPF_NOEXIST 1
#define BPF_EXIST   2

/* XDP and tc verdicts */
#define XDP_ABORTED 0
#define XDP_DROP    1
#define XDP_PASS    2
#define TC_ACT_OK   0
#define TC_ACT_SHOT 2

struct bpf_map_def {
    __u32 type, key_size, value_size, max_entries, map_flags;
};

struct xdp_md {
    __u32 data;            /*  0 */
    __u32 data_end;        /*  4 */
    __u32 data_meta;       /*  8 */
    __u32 ingress_ifindex; /* 12 */
    __u32 rx_queue_index;  /* 16 */
};

struct __sk_buff {
    __u32 len, pkt_type, mark, queue_mapping, protocol, vlan_present;
    __u32 vlan_tci, vlan_proto, priority, ingress_ifindex, ifindex, tc_index;
    __u32 cb[5];            /* 48 */
    __u32 hash, tc_classid, data, data_end, napi_id;
};

struct ethhdr { __u8 h_dest[6], h_source[6]; __u16 h_proto; };   /* h_proto @ 12 */

/* xdp_map_access's key type, from ebpf-se's xdp_map_access_common.h */
struct dummy_key { __u8 key; };

static void *(*bpf_map_lookup_elem)(void *map, const void *key) = (void *) 1;
static long (*bpf_map_update_elem)(void *map, const void *key,
                                   const void *value, __u64 flags) = (void *) 2;

#endif
