// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
 *
 * KernelPatch Module (KPM) - [HMKPM] Netlink Version
 */

#include <asm/current.h>
#include <common.h>
#include <compiler.h>
#include <hook.h>
#include <kconfig.h>
#include <kpmodule.h>
#include <kputils.h>
#include <ksyms.h>
#include <ktypes.h>
#include <linux/bitops.h>
#include <linux/err.h>
#include <linux/errno.h>
#include <linux/kernel.h>
#include <linux/mm_types.h>
#include <linux/sched.h>
#include <linux/printk.h>
#include <syscall.h>
#include <uapi/asm-generic/unistd.h>
#include <asm-generic/rwonce.h>

#define HMKPM_VERSION_MAJOR	2
#define HMKPM_VERSION_MINOR	9
#define HMKPM_VERSION_PATCH	0
#define HMKPM_VERSION_STR	"2.9.0-nl"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("KernelPatch Module (KPM) HMKPM Netlink");

#define HMKPM_TAG			"[HMKPM] "
#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_warn(fmt, ...)        logkw(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

// 解决 KPM 没有 libc 的问题
void *memset(void *s, int c, size_t count)
{
    unsigned char *p = (unsigned char *)s;
    while (count--)
        *p++ = (unsigned char)c;
    return s;
}

static bool init_error = false;

static inline void make_cfi_name(char *dst, size_t dst_size, const char *name)
{
	const char *suffix = ".cfi_jt";
	size_t i = 0;

	while (name && *name && i + 1 < dst_size)
		dst[i++] = *name++;

	while (*suffix && i + 1 < dst_size)
		dst[i++] = *suffix++;

	dst[i] = '\0';
}

static unsigned long hmkpm_lookup_symbol(const char *name)
{
	unsigned long addr;

	if (!name || !kallsyms_lookup_name)
		return 0;

	addr = kallsyms_lookup_name(name);
	if (!addr) {
		char cfi_name[64];
		make_cfi_name(cfi_name, sizeof(cfi_name), name);
		addr = kallsyms_lookup_name(cfi_name);
	}
	return addr;
}

#define hkfunc_match(func)							\
do {										\
	kf_##func = (typeof(kf_##func))hmkpm_lookup_symbol(#func);		\
	if (!kf_##func) {							\
		hmkpm_error("Failed to find kfunc %s\n", #func);		\
		init_error = true;						\
	}									\
} while (0)

#define hkvar_match(var)							\
do {										\
	kv_##var = (typeof(kv_##var))hmkpm_lookup_symbol(#var);			\
	if (!kv_##var) {							\
		hmkpm_error("Failed to find kvar %s\n", #var);			\
		init_error = true;						\
	}									\
} while (0)

void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
unsigned long kfunc_def(__arch_clear_user)(void __user *to, unsigned long n);
long kfunc_def(probe_kernel_read)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);
void kfunc_def(__rcu_read_lock)(void);
void kfunc_def(__rcu_read_unlock)(void);

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);

static inline long hmkpm_copy_from_kernel_nofault(void *dst, const void *src, size_t size)
{
	kfunc_call(probe_kernel_read, dst, src, size);
	return -ENOSYS;
}

/* ========================================================================
 * 页表遍历与物理内存读取核心
 * ======================================================================== */
static uint64_t pgt_va_bits;
static uint64_t pgt_phys_offset;
static uint64_t pgt_page_offset;
static uint64_t pgt_linear_voffset;
static uint64_t pgt_page_shift;
static uint64_t pgt_page_size;
static uint64_t pgt_pgd_align_mask;
static uint64_t pgt_pgd_size;
static uint64_t pgt_page_level;
static uint64_t pgt_user_limit;
static uint64_t pgt_phys_limit;
static uint64_t pgt_high_memory;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }
static inline uint64_t pgt_virt_to_phys(uint64_t addr) { return addr - pgt_linear_voffset; }

static bool sw_pan_enabled = false;
static uint64_t reserved_ttbr0_val = 0;

static void hmkpm_sw_pan_init(void)
{
	if (kp_kconfig_enabled("CONFIG_ARM64_SW_TTBR0_PAN"))
		sw_pan_enabled = true;

	unsigned long sym_reserved = hmkpm_lookup_symbol("reserved_ttbr0");
	if (sym_reserved) {
		uint64_t pa = 0;
		if (hmkpm_copy_from_kernel_nofault(&pa, (const void *)sym_reserved, sizeof(pa)) == 0 && pa) {
			reserved_ttbr0_val = pa;
			sw_pan_enabled = true;
		}
	}
}

static inline uint64_t hmkpm_uaccess_enable(void)
{
	uint64_t old_ttbr0 = 0;
	if (unlikely(sw_pan_enabled)) {
		asm volatile("mrs %0, ttbr0_el1" : "=r"(old_ttbr0));
		struct task_struct *cur = current;
		if (cur) {
			struct mm_struct *mm = NULL;
			if (task_struct_offset.active_mm_offset > 0) {
				hmkpm_copy_from_kernel_nofault(&mm, (const void *)((uintptr_t)cur + task_struct_offset.active_mm_offset), sizeof(mm));
			} else if (kf_get_task_mm) {
				mm = kfunc(get_task_mm)(cur);
			}
			if (mm && mm_struct_offset.pgd_offset >= 0) {
				uint64_t cur_pgd_va = 0;
				if (hmkpm_copy_from_kernel_nofault(&cur_pgd_va, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(cur_pgd_va)) == 0 && cur_pgd_va) {
					uint64_t cur_pgd_pa = pgt_virt_to_phys(cur_pgd_va);
					uint64_t asid_mask = 0xFFFF000000000000ULL;
					uint64_t new_ttbr0 = (cur_pgd_pa & ~asid_mask) | (old_ttbr0 & asid_mask);
					asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(new_ttbr0) : "memory");
				}
			}
		}
	}
	return old_ttbr0;
}

static inline void hmkpm_uaccess_disable(uint64_t old_ttbr0)
{
	if (unlikely(sw_pan_enabled)) {
		if (old_ttbr0) asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(old_ttbr0) : "memory");
		else if (reserved_ttbr0_val) asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(reserved_ttbr0_val) : "memory");
	}
}

static inline unsigned long hmkpm_copy_to_user(void __user *to, const void *from, unsigned long n)
{
	uint64_t flags = hmkpm_uaccess_enable();
	unsigned long ret = kfunc(__arch_copy_to_user)(to, from, n);
	hmkpm_uaccess_disable(flags);
	return ret;
}

static inline unsigned long hmkpm_copy_from_user(void *to, const void __user *from, unsigned long n)
{
	uint64_t flags = hmkpm_uaccess_enable();
	unsigned long ret = kfunc(__arch_copy_from_user)(to, from, n);
	hmkpm_uaccess_disable(flags);
	return ret;
}

static inline int validate_virt_range(uint64_t va, uint64_t size)
{
	uint64_t last;
	if (unlikely(size == 0)) return -EINVAL;
	if (unlikely(va < pgt_page_offset)) return -EFAULT;
	if (unlikely(va > U64_MAX - size)) return -EFAULT;
	last = va + size - 1;
	if (unlikely(last >= pgt_high_memory)) return -EFAULT;
	return 0;
}

static inline int validate_phys_range(uint64_t phys, uint64_t size)
{
	uint64_t va;
	if (unlikely(size == 0)) return -EINVAL;
	if (unlikely((phys >> 48) != 0)) return -EFAULT;
	if (unlikely(phys > U64_MAX - size)) return -EFAULT;
	va = pgt_phys_to_virt(phys);
	return validate_virt_range(va, size);
}

static inline uint64_t pgt_untag_user_va(uint64_t va) { return va & 0x00FFFFFFFFFFFFFFULL; }
static inline uint64_t pgt_desc_to_phys(uint64_t desc) {
	uint64_t addr_mask = (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
	return desc & addr_mask;
}

static inline bool pgt_block_allowed(int lv) {
	if (pgt_page_shift == 14) return (lv == 2);
	else return (lv == 1 || lv == 2);
}

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write)
{
	uint64_t table_va, pxd_bits, pxd_ptrs;
	int64_t start, lv;

	if (!pgd || (pgd & pgt_pgd_align_mask)) return 0;
	if (validate_virt_range(pgd, pgt_pgd_size)) return 0;

	va = pgt_untag_user_va(va);
	if (va >> pgt_va_bits) return 0;

	table_va = pgd;
	pxd_bits = pgt_page_shift - 3;
	pxd_ptrs = 1ULL << pxd_bits;
	start = 4 - (int64_t)pgt_page_level;

	for (lv = start; lv < 4; lv++) {
		uint64_t pxd_shift, pxd_index, top_bits, entry_va, desc = 0, type;
		uint64_t cur_table_size = (lv == start) ? pgt_pgd_size : pgt_page_size;
		if (validate_virt_range(table_va, cur_table_size)) return 0;

		pxd_shift = (pgt_page_shift - 3) * (4 - lv) + 3;
		if (pxd_shift >= pgt_va_bits) return 0;

		pxd_index = (va >> pxd_shift) & (pxd_ptrs - 1);
		top_bits = pgt_va_bits - pxd_shift;
		if (top_bits > pxd_bits) top_bits = pxd_bits;
		if (top_bits == 0 || pxd_index >= (1ULL << top_bits)) return 0;

		entry_va = table_va + pxd_index * 8;
		if (hmkpm_copy_from_kernel_nofault(&desc, (const void *)entry_va, sizeof(desc)) != 0) return 0;

		type = desc & 3ULL;
		if (type == 0ULL || type == 2ULL) return 0;

		if (lv == 3) {
			uint64_t base;
			if (type != 3ULL) return 0;
			if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51))) return 0;
			base = pgt_desc_to_phys(desc);
			if (base & (pgt_page_size - 1)) return 0;
			if (validate_phys_range(base, pgt_page_size)) return 0;
			return base | (va & (pgt_page_size - 1));
		}

		if (type == 1ULL) {
			uint64_t block_bits, block_size, block_mask, base;
			if (!pgt_block_allowed((int)lv)) return 0;
			if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51))) return 0;
			block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
			if (block_bits >= 64) return 0;
			block_size = 1ULL << block_bits;
			block_mask = block_size - 1;
			base = pgt_desc_to_phys(desc);
			if (base & block_mask) return 0;
			if (validate_phys_range(base, block_size)) return 0;
			return (base & ~block_mask) | (va & block_mask);
		}

		if (is_write && (desc & (1ULL << 62))) return 0;
		uint64_t next_pa = pgt_desc_to_phys(desc);
		if (next_pa & (pgt_page_size - 1)) return 0;
		if (validate_phys_range(next_pa, pgt_page_size)) return 0;
		table_va = pgt_phys_to_virt(next_pa);
	}
	return 0;
}

static int pgt_pgtable_init(void)
{
	uint64_t tcr_el1, t1sz, va1_bits, t0sz, va0_bits, tg0, pxd_bits;
	int64_t start;
	asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
	t1sz = (tcr_el1 >> 16) & 0x3F;
	va1_bits = 64 - t1sz;
	t0sz = tcr_el1 & 0x3F;
	va0_bits = 64 - t0sz;
	tg0 = (tcr_el1 >> 14) & 0x3ULL;

	if (va0_bits > 48 || va0_bits < 36) return -EINVAL;
	pgt_va_bits = va0_bits;
	pgt_user_limit = (1ULL << va0_bits) - 1;

	if (tg0 == 0) pgt_page_shift = 12;
	else if (tg0 == 2) pgt_page_shift = 14;
	else return -EINVAL;

	pxd_bits = pgt_page_shift - 3;
	pgt_page_level = (va0_bits - 4) / pxd_bits;
	if (pgt_page_level != 2 && pgt_page_level != 3 && pgt_page_level != 4) return -EINVAL;
	start = 4 - (int64_t)pgt_page_level;
	if (start < 0 || start > 2) return -EINVAL;
	pgt_page_size = 1ULL << pgt_page_shift;

	int64_t root_lv = 4 - (int64_t)pgt_page_level;
	uint64_t root_shift = (pgt_page_shift - 3) * (4 - root_lv) + 3;
	if (pgt_va_bits > root_shift) {
		uint64_t root_bits = pgt_va_bits - root_shift;
		pgt_pgd_size = (1ULL << root_bits) * 8;
		if (pgt_pgd_size < pgt_page_size) pgt_pgd_align_mask = pgt_pgd_size - 1;
		else { pgt_pgd_size = pgt_page_size; pgt_pgd_align_mask = pgt_page_size - 1; }
	} else { pgt_pgd_size = pgt_page_size; pgt_pgd_align_mask = pgt_page_size - 1; }

	if (kver >= VERSION(5, 4, 0)) { pgt_pgd_size = pgt_page_size; pgt_pgd_align_mask = pgt_page_size - 1; }
	if (kver >= VERSION(5, 4, 0)) pgt_page_offset = -(UL(1) << va1_bits);
	else pgt_page_offset = -(UL(1) << (va1_bits - 1));

	hkvar_match(memstart_addr);
	if (!kv_memstart_addr) return -EFAULT;
	pgt_phys_offset = kvar_val(memstart_addr);
	pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

	bool prev_init_error = init_error;
	hkvar_match(high_memory);
	if (kv_high_memory) pgt_high_memory = (uint64_t)kvar_val(high_memory);
	else { pgt_high_memory = ~0ULL; init_error = prev_init_error; }
	pgt_phys_limit = pgt_virt_to_phys(pgt_high_memory);

	return 0;
}

#define HMKPM_BOUNCE_SIZE 512U

static inline void hmkpm_fast_copy(void *dst, const void *src, size_t n)
{
	uint8_t *d = (uint8_t *)dst;
	const uint8_t *s = (const uint8_t *)src;
	while (n >= 8) { *(uint64_t *)d = *(const uint64_t *)s; d += 8; s += 8; n -= 8; }
	while (n > 0) { *d++ = *s++; n--; }
}

// 强制无锁读取
static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len, void __user *local_buf, bool is_write)
{
	ssize_t total = 0;
	uint64_t pgd = 0;
	uint8_t bounce[HMKPM_BOUNCE_SIZE];

	if (!mm || mm_struct_offset.pgd_offset < 0) return -EINVAL;
	if (is_write) return -EOPNOTSUPP; // 无锁模式下禁止写入

	if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd) return -EFAULT;

	while (len > 0) {
		unsigned long page_off = remote_va & (pgt_page_size - 1);
		size_t page_left = (size_t)(pgt_page_size - page_off);
		size_t chunk = min(len, page_left);
		chunk = min(chunk, (size_t)HMKPM_BOUNCE_SIZE);

		uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va, false);
		if (!tkpa) {
			if (total > 0) break;
			return -EFAULT;
		}

		void *tkva = (void *)pgt_phys_to_virt(tkpa);
		hmkpm_fast_copy(bounce, tkva, chunk);

		unsigned long not_copied = hmkpm_copy_to_user(local_buf, bounce, chunk);
		if (not_copied) {
			size_t copied = chunk - not_copied;
			total += (ssize_t)copied;
			break;
		}

		total += (ssize_t)chunk;
		local_buf = (void __user *)((uintptr_t)local_buf + chunk);
		remote_va += chunk;
		len -= chunk;
	}
	return total;
}

static ssize_t pgt_rw(pid_t pid, uint64_t remote_va, size_t len, void __user *local_buf, bool is_write)
{
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;
	ssize_t ret;

	if (pid <= 0) return -EINVAL;
	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)(pid);
	if (!task) { kfunc(__rcu_read_unlock)(); return -ESRCH; }
	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();
	if (!mm) return -ESRCH;

	ret = pgt_rw_mm(mm, remote_va, len, local_buf, is_write);
	kfunc(mmput)(mm);
	return ret;
}

/* ========================================================================
 * Netlink 通信模块
 * ======================================================================== */
struct sock;
struct sk_buff;
struct netlink_kernel_cfg {
    unsigned int groups;
    void (*input)(struct sk_buff *skb);
    void *cb_mutex;
    void *bind;
    void *unbind;
};

#define HMKPM_NL_CMD_READ 0x55

struct hmkpm_nl_req {
    int32_t pid;
    uint32_t _pad;
    uint64_t addr;
    uint64_t size;
    uint64_t user_buf;
};

static struct sock *(*kf_netlink_kernel_create)(void *net, int unit, void *module, struct netlink_kernel_cfg *cfg);
static int (*kf_netlink_unicast)(struct sock *ssk, struct sk_buff *skb, uint32_t portid, int nonblock);
static void (*kf_netlink_kernel_release)(struct sock *sk);
static struct sk_buff *(*kf_alloc_skb)(unsigned int size, int gfp_mask);
static void *kv_init_net = NULL;

static struct sock *g_nl_sk = NULL;
static int g_nl_proto = -1;

static void hmkpm_netlink_input(struct sk_buff *skb)
{
    struct nlmsghdr *nlh;
    struct hmkpm_nl_req *req;
    struct sk_buff *skb_out;
    struct nlmsghdr *nlh_out;
    int *status_out;
    ssize_t read_ret;
    uint32_t user_pid;

    if (!skb) return;

    nlh = (struct nlmsghdr *)skb->data;
    if (!nlh || nlh->nlmsg_len < sizeof(struct hmkpm_nl_req) || nlh->nlmsg_type != HMKPM_NL_CMD_READ)
        return;

    req = (struct hmkpm_nl_req *)NLMSG_DATA(nlh);
    user_pid = nlh->nlmsg_pid; 

    read_ret = pgt_rw((pid_t)req->pid, req->addr, req->size, (void __user *)(uintptr_t)req->user_buf, false);

    if (!kf_alloc_skb || !kf_netlink_unicast) return;
    skb_out = kf_alloc_skb(32, 0); // GFP_ATOMIC
    if (!skb_out) return;

    nlh_out = (struct nlmsghdr *)skb_put(skb_out, NLMSG_SPACE(sizeof(int)));
    nlh_out->nlmsg_len = NLMSG_SPACE(sizeof(int));
    nlh_out->nlmsg_type = 0; 
    nlh_out->nlmsg_flags = 0;
    nlh_out->nlmsg_seq = 0;
    nlh_out->nlmsg_pid = 0;

    status_out = (int *)NLMSG_DATA(nlh_out);
    *status_out = (read_ret == req->size) ? 0 : -1;

    kf_netlink_unicast(g_nl_sk, skb_out, user_pid, 0);
}

static int hmkpm_netlink_init(void)
{
    struct netlink_kernel_cfg cfg;
    int try_protos[] = {22, 23, 24, 25, 26}; // 动态探测
    int i;

    kf_netlink_kernel_create = (void *)hmkpm_lookup_symbol("__netlink_kernel_create");
    kf_netlink_unicast       = (void *)hmkpm_lookup_symbol("netlink_unicast");
    kf_netlink_kernel_release= (void *)hmkpm_lookup_symbol("netlink_kernel_release");
    kf_alloc_skb             = (void *)hmkpm_lookup_symbol("__alloc_skb");
    kv_init_net              = (void *)hmkpm_lookup_symbol("init_net");

    if (!kf_netlink_kernel_create || !kf_netlink_unicast || !kf_alloc_skb || !kv_init_net) {
        hmkpm_error("netlink symbols not found\n");
        return -ENOENT;
    }

    memset(&cfg, 0, sizeof(cfg));
    cfg.input = hmkpm_netlink_input;

    for (i = 0; i < 5; i++) {
        g_nl_sk = kf_netlink_kernel_create(kv_init_net, try_protos[i], NULL, &cfg);
        if (g_nl_sk) {
            g_nl_proto = try_protos[i];
            hmkpm_info("netlink registered on proto %d\n", g_nl_proto);
            return 0;
        }
    }
    return -ENOENT;
}

static void hmkpm_netlink_exit(void)
{
    if (g_nl_sk && kf_netlink_kernel_release) {
        kf_netlink_kernel_release(g_nl_sk);
        g_nl_sk = NULL;
    }
}

/* ========================================================================
 * 模块生命周期
 * ======================================================================== */
static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
	if (kver < VERSION(4, 0, 0) || kver >= VERSION(6, 13, 0)) {
		hmkpm_error("Kernel version not supported\n");
		return -EINVAL;
	}

	if (pgt_pgtable_init() != 0) {
		hmkpm_error("Page table initialization failed\n");
		return -ENOENT;
	}

	hmkpm_sw_pan_init();

	static const char *const arm64_memset_aliases[] = {
        "__memset", "memset", "__pi___memset", "__pi_memset", 
        "__asan_memset", "__hwasan_memset", "__mte_memset", "__arch_memset", NULL
    };

    for (int i = 0; arm64_memset_aliases[i] != NULL; i++) {
        kf_memset = (typeof(kf_memset))hmkpm_lookup_symbol(arm64_memset_aliases[i]);
        if (kf_memset) break;
    }
	if (!kf_memset) init_error = true;

	kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__arch_copy_to_user");
	if (!kf___arch_copy_to_user) kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__copy_to_user");
	if (!kf___arch_copy_to_user) init_error = true;

	kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__arch_copy_from_user");
	if (!kf___arch_copy_from_user) kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__copy_from_user");
	if (!kf___arch_copy_from_user) init_error = true;

	hkfunc_match(probe_kernel_read);
	hkfunc_match(find_task_by_vpid);
	hkfunc_match(get_task_mm);
	hkfunc_match(mmput);
	hkfunc_match(__rcu_read_lock);
	hkfunc_match(__rcu_read_unlock);

	if (init_error) {
		hmkpm_error("Symbol resolution failed, aborting...\n");
		return -ENOENT;
	}

	if (hmkpm_netlink_init() != 0) {
		hmkpm_error("netlink init failed\n");
		return -ENOENT;
	}

	hmkpm_info("module loaded successfully (Netlink mode)\n");
	return 0;
}

static long module_control_handler(const char *args, char __user *out_msg, int outlen)
{
    if (out_msg && outlen > 0) {
        const char *ok = "Netlink KPM Active\n";
        compat_copy_to_user(out_msg, ok, 18);
    }
	return 0;
}

static long module_cleanup_handler(void *__user reserved)
{
    hmkpm_netlink_exit();
	hmkpm_info("module cleaned up\n");
	return 0;
}

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
