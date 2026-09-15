/*
 * Suricata's ebpf/vlan_filter.c, verbatim apart from the includes, which are
 * replaced by ex/skb_common.h so it builds without a kernel tree.  It is a
 * real production socket filter and translates with no diagnostics.
 *
 * Upstream: https://github.com/OISF/suricata (GPL-2.0-only)
 * Copyright (C) 2018 Open Information Security Foundation
 */
#include "sur_common.h"

int SEC("filter") hashfilter(struct __sk_buff *skb) {
    __u16 vlan_id = skb->vlan_tci & 0x0fff;
    /* accept VLAN 2 and 4 and drop the rest */
    switch (vlan_id) {
        case 2:
        case 4:
            return -1;
        default:
            return 0;
    }
    return 0;
}
