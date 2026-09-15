/*
 * Enough of <linux/bpf.h>, <linux/if_ether.h>, <linux/ip.h>, <linux/ipv6.h>
 * and Suricata's llvm_bpfload.h for ex/sur_filter*.c to build without a
 * kernel tree.  The field OFFSETS are what matter: the translator turns each
 * access into a load at that offset into the ctx or packet region, so a wrong
 * one here silently models a different program.  ex/sur_offsets.c
 * static-asserts the ones the filter uses.
 */
#ifndef SUR_H
#define SUR_H
typedef unsigned char  __u8;
typedef unsigned short __u16;
typedef unsigned int   __u32;
typedef unsigned long long __u64;
#define SEC(N) __attribute__((section(N), used))
#define __uint(name, val) int (*name)[val]
#define __type(name, val) typeof(val) *name
#define __always_inline inline __attribute__((always_inline))
#define offsetof(t, m) __builtin_offsetof(t, m)

#define BPF_MAP_TYPE_PERCPU_HASH 5
#define ETH_HLEN        14
#define ETH_P_IP        0x0800
#define ETH_P_IPV6      0x86DD
#define ETH_P_8021Q     0x8100
#define ETH_P_8021AD    0x88A8

struct __sk_buff {
    __u32 len, pkt_type, mark, queue_mapping, protocol, vlan_present;
    __u32 vlan_tci, vlan_proto, priority, ingress_ifindex, ifindex, tc_index;
    __u32 cb[5];            /* 48 */
    __u32 hash, tc_classid, data, data_end, napi_id;
};
struct ethhdr { __u8 h_dest[6], h_source[6]; __u16 h_proto; };   /* h_proto @ 12 */
struct iphdr {
    __u8 vihl, tos; __u16 tot_len, id, frag_off; __u8 ttl, protocol;
    __u16 check; __u32 saddr; __u32 daddr;                       /* saddr @ 12 */
};

unsigned long long load_word(void *skb, unsigned long long off) asm("llvm.bpf.load.word");
unsigned long long load_half(void *skb, unsigned long long off) asm("llvm.bpf.load.half");
unsigned long long load_byte(void *skb, unsigned long long off) asm("llvm.bpf.load.byte");
static void *(*bpf_map_lookup_elem)(void *map, const void *key) = (void *) 1;
#endif
#define ETH_TLEN 2
struct in6_addr_shim { __u32 w[4]; };
struct ipv6hdr {
    __u8 prio_ver; __u8 fl[3]; __u16 payload_len; __u8 nexthdr, hop_limit;
    struct in6_addr_shim saddr;   /* 8  */
    struct in6_addr_shim daddr;   /* 24 */
};
#define __section(x) __attribute__((section(x), used))
