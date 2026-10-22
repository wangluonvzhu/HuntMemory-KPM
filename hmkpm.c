// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
 *
 * KernelPatch Module (KPM) - [HMKPM]
 * Read-only build with Netlink 31 channel (Anti-ACE optimized)
 * Target OS: Android GKI 5.10.x
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
#include <uapi/asm-generic/unistd.h>
#include <asm-generic/rwonce.h>

#define HMKPM_VERSION_MAJOR	2
#define HMKPM_VERSION_MINOR	9
#define HMKPM_VERSION_PATCH	2
#define HMKPM_VERSION_CODE	(((uint32_t)HMKPM_VERSION_MAJOR << 16) | \
				 ((uint32_t)HMKPM_VERSION_MINOR << 8) | \
				 ((uint32_t)HMKPM_VERSION_PATCH))
#define HMKPM_VERSION_STR	"2.9.2-nl31"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("KernelPatch Module (KPM) HMKPM");

static bool hook_active = true;
static bool init_error = false;
static unsigned long fsnotify_addr = 0;
static bool fsnotify_hooked = false;

struct inode;

#define PROC_SUPER_MAGIC	0x9fa0
#define SUPER_BLOCK_OFF 40
#define MAGIC_OFF 96

#define U64_MAX				((u64)~0ULL)
#define HMKPM_TAG			"[HMKPM] "

#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_warn(fmt, ...)        logkw(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

/* 内核 5.10 结构体偏移定义 */
#define MM_MMAP_OFFSET       0x00
#define MM_ARG_START_OFFSET  0x130
#define VMA_VM_START_OFFSET  0x00
#define VMA_VM_FILE_OFFSET   0x80
#define VMA_VM_NEXT_OFFSET   0xA0
#define FILE_F_PATH_DENTRY_OFFSET 0x18
#define DENTRY_D_NAME_NAME_OFFSET 0x38

void *memset(void *s, int c, size_t count)
{
    unsigned char *p = (unsigned char *)s;
    while (count--)
        *p++ = (unsigned char)c;
    return s;
}

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

/* 函数声明 */
void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
long kfunc_def(probe_kernel_read)(void *dst, const void *src, size_t size);
long kfunc_def(copy_from_kernel_nofault)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);
void kfunc_def(__rcu_read_lock)(void);
void kfunc_def(__rcu_read_unlock)(void);

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);

/* Netlink 符号声明 */
struct sock;
struct sk_buff;
struct netlink_kernel_cfg { unsigned int groups; void (*input)(struct sk_buff *skb); void *cb_mutex; void *bind; void *unbind; };
static struct sock *(*kf_netlink_create)(void *net, int unit, void *module, struct netlink_kernel_cfg *cfg);
static int (*kf_netlink_unicast)(struct sock *ssk, struct sk_buff *skb, uint32_t portid, int nonblock);
static void *(*kf_alloc_skb)(unsigned int size, int gfp_mask);
static void *(*kf_skb_put)(struct sk_buff *skb, unsigned int len);
static unsigned char *(*kf_skb_pull)(struct sk_buff *skb, unsigned int len);
static void (*kf_kfree_skb)(struct sk_buff *skb);
static void *kv_init_net = NULL;
static struct sock *g_nl_sk = NULL;

struct inode_min { char pad[SUPER_BLOCK_OFF]; void *i_sb; };
struct super_block_min { char pad[MAGIC_OFF]; unsigned long s_magic; };

static inline bool is_proc_inode(const struct inode *inode)
{
    const struct inode_min *i = (const struct inode_min *)inode;
    const struct super_block_min *sb;
    if (!i) return false;
    sb = (const struct super_block_min *)READ_ONCE(i->i_sb);
    if (!sb) return false;
    return (READ_ONCE(sb->s_magic) == PROC_SUPER_MAGIC);
}

static void before_fsnotify(hook_fargs7_t *args, void *udata)
{
    struct inode *dir, *inode, *target;
    if (!READ_ONCE(hook_active) || !args) return;
    dir = (struct inode *)args->arg3;
    inode = (struct inode *)args->arg5;
    target = inode ? inode : dir;
    if (target && is_proc_inode(target)) {
        args->skip_origin = 1;
        args->ret = 0;
    }
}

static inline long hmkpm_copy_from_kernel_nofault(void *dst, const void *src, size_t size)
{
	if (kf_copy_from_kernel_nofault) return kfunc(copy_from_kernel_nofault)(dst, src, size);
	if (kf_probe_kernel_read) return kfunc(probe_kernel_read)(dst, src, size);
	return -ENOSYS;
}

static uint64_t pgt_va_bits, pgt_phys_offset, pgt_page_offset, pgt_linear_voffset;
static uint64_t pgt_page_shift, pgt_page_size, pgt_pgd_align_mask, pgt_pgd_size;
static uint64_t pgt_page_level, pgt_user_limit, pgt_phys_limit, pgt_high_memory;
static bool pgt_tbi0;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }
static inline uint64_t pgt_virt_to_phys(uint64_t addr) { return addr - pgt_linear_voffset; }

/* SW PAN Support */
static bool sw_pan_enabled = false;
static uint64_t reserved_ttbr0_val = 0;

static void hmkpm_sw_pan_init(void)
{
	if (kp_kconfig_enabled("CONFIG_ARM64_SW_TTBR0_PAN")) sw_pan_enabled = true;
	unsigned long sym_reserved = hmkpm_lookup_symbol("reserved_ttbr0");
	if (sym_reserved) {
		uint64_t pa = 0;
		if (hmkpm_copy_from_kernel_nofault(&pa, (const void *)sym_reserved, sizeof(pa)) == 0 && pa) {
			reserved_ttbr0_val = pa;
			sw_pan_enabled = true;
		}
	}
	if (!sw_pan_enabled && sym_reserved) {
		uint64_t mmfr1;
		asm volatile("mrs %0, id_aa64mmfr1_el1" : "=r"(mmfr1));
		if (((mmfr1 >> 20) & 0xFULL) == 0) sw_pan_enabled = true;
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
			bool need_mmput = false;
			if (task_struct_offset.active_mm_offset > 0) {
				hmkpm_copy_from_kernel_nofault(&mm, (const void *)((uintptr_t)cur + task_struct_offset.active_mm_offset), sizeof(mm));
			} else if (task_struct_offset.mm_offset > 0) {
				hmkpm_copy_from_kernel_nofault(&mm, (const void *)((uintptr_t)cur + task_struct_offset.mm_offset), sizeof(mm));
			} else if (kf_get_task_mm) {
				mm = kfunc(get_task_mm)(cur);
				need_mmput = true;
			}
			if (mm && mm_struct_offset.pgd_offset >= 0) {
				uint64_t cur_pgd_va = 0;
				if (hmkpm_copy_from_kernel_nofault(&cur_pgd_va, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(cur_pgd_va)) == 0 && cur_pgd_va) {
					uint64_t cur_pgd_pa = pgt_virt_to_phys(cur_pgd_va);
					uint64_t new_ttbr0 = (cur_pgd_pa & ~0xFFFF000000000000ULL) | (old_ttbr0 & 0xFFFF000000000000ULL);
					asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(new_ttbr0) : "memory");
				}
			}
			if (mm && need_mmput && kf_mmput) kfunc(mmput)(mm);
		}
	}
	return old_ttbr0;
}

static inline void hmkpm_uaccess_disable(uint64_t old_ttbr0)
{
	if (unlikely(sw_pan_enabled)) {
		if (old_ttbr0) {
			asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(old_ttbr0) : "memory");
		} else if (reserved_ttbr0_val) {
			asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(reserved_ttbr0_val) : "memory");
		}
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

/* 页表遍历 */
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
static inline uint64_t pgt_desc_to_phys(uint64_t desc)
{
	return desc & (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
}

static inline bool pgt_block_allowed(int lv) { return (pgt_page_shift == 14) ? (lv == 2) : (lv == 1 || lv == 2); }

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write)
{
	uint64_t table_va, pxd_bits, pxd_ptrs;
	int64_t start, lv;
	
    // 【修复点】：去掉对 pgd 的 validate_virt_range 检查，它是内核地址
	if (!pgd || (pgd & pgt_pgd_align_mask)) return 0;
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
			if (type != 3ULL || (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51)))) return 0;
			base = pgt_desc_to_phys(desc);
			if ((base & (pgt_page_size - 1)) || validate_phys_range(base, pgt_page_size)) return 0;
			return base | (va & (pgt_page_size - 1));
		}

		if (type == 1ULL) {
			uint64_t block_bits, block_size, block_mask, base;
			if (!pgt_block_allowed((int)lv) || (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51)))) return 0;
			block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
			if (block_bits >= 64) return 0;
			block_size = 1ULL << block_bits;
			block_mask = block_size - 1;
			base = pgt_desc_to_phys(desc);
			if ((base & block_mask) || validate_phys_range(base, block_size)) return 0;
			return (base & ~block_mask) | (va & block_mask);
		}

		if (is_write && (desc & (1ULL << 62))) return 0;
		uint64_t next_pa = pgt_desc_to_phys(desc);
		if ((next_pa & (pgt_page_size - 1)) || validate_phys_range(next_pa, pgt_page_size)) return 0;
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

    // 【修复点】：5.10 内核 PAGE_OFFSET 计算修正，必须 -1
	if (kver >= VERSION(4, 6, 0)) pgt_page_offset = -(UL(1) << (va1_bits - 1));
	else pgt_page_offset = -(UL(1) << va1_bits);

	hkvar_match(memstart_addr);
	if (!kv_memstart_addr) return -EFAULT;
	pgt_phys_offset = kvar_val(memstart_addr);
	pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

	bool prev_init_error = init_error;
	hkvar_match(high_memory);
	if (kv_high_memory) pgt_high_memory = (uint64_t)kvar_val(high_memory);
	else { pgt_high_memory = ~0ULL; init_error = prev_init_error; }

	pgt_phys_limit = pgt_virt_to_phys(pgt_high_memory);
	pgt_tbi0 = !!(tcr_el1 & (1ULL << 37));
	return 0;
}

static inline int hmkpm_user_range_ok(const void __user *ptr, uint64_t len)
{
	uint64_t u;
	if (!ptr || len == 0) return 0;
	u = pgt_untag_user_va((uint64_t)ptr);
	if (u > pgt_user_limit) return 0;
	if (len - 1 > pgt_user_limit - u) return 0;
	return 1;
}

#define min(a, b) ((a) < (b) ? (a) : (b))
#define HMKPM_BOUNCE_SIZE 512U

static inline void hmkpm_fast_copy(void *dst, const void *src, size_t n)
{
	uint8_t *d = (uint8_t *)dst;
	const uint8_t *s = (const uint8_t *)src;
	while (n >= 8 && !(((uintptr_t)d | (uintptr_t)s) & 7)) { *(uint64_t *)d = *(const uint64_t *)s; d += 8; s += 8; n -= 8; }
	while (n >= 4 && !(((uintptr_t)d | (uintptr_t)s) & 3)) { *(uint32_t *)d = *(const uint32_t *)s; d += 4; s += 4; n -= 4; }
	while (n > 0) { *d++ = *s++; n--; }
}

static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len, void *local_buf, bool is_write)
{
	ssize_t total = 0;
	uint64_t pgd = 0;
	uint8_t bounce[HMKPM_BOUNCE_SIZE];

	if (!mm || is_write) return -EOPNOTSUPP; 
	if (mm_struct_offset.pgd_offset <= 0) return -EINVAL;

	if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd)
		return -EFAULT;

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
		hmkpm_fast_copy((uint8_t *)local_buf + total, tkva, chunk);

		total += (ssize_t)chunk;
		remote_va += chunk;
		len -= chunk;
	}
	return total;
}

static ssize_t pgt_rw(pid_t pid, uint64_t remote_va, size_t len, void *local_buf, bool is_write)
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

// ==========================================
// Netlink 通信层
// ==========================================
struct nlmsghdr { uint32_t nlmsg_len; uint16_t nlmsg_type; uint16_t nlmsg_flags; uint32_t nlmsg_seq; uint32_t nlmsg_pid; };
#define NLMSG_HDRLEN ((int)((sizeof(struct nlmsghdr)+3)&~3))
#define NLMSG_LENGTH(len) ((len) + NLMSG_HDRLEN)
#define NLMSG_SPACE(len) (((NLMSG_LENGTH(len))+3)&~3)
#define NLMSG_DATA(nlh) ((void*)(((char*)nlh) + NLMSG_LENGTH(0)))

#define HMKPM_NL_CMD_READ     0x55
#define HMKPM_NL_CMD_GET_PID  0x56
#define HMKPM_NL_CMD_GET_BASE 0x57

struct hmkpm_nl_req { int32_t pid; uint32_t _pad; uint64_t addr; uint64_t size; uint64_t user_buf; char pkg_name[64]; char mod_name[64]; };

static int hmkpm_strstr(const char *haystack, const char *needle) {
    if (!*needle) return 1;
    for (; *haystack; ++haystack) {
        const char *h = haystack; const char *n = needle;
        while (*h && *n && *h == *n) { h++; n++; }
        if (!*n) return 1;
    }
    return 0;
}

static void netlink_recv(struct sk_buff *skb) {
    if (!skb || !g_nl_sk) return;

    char *skb_data = NULL;
    if (kf_skb_pull) {
        skb_data = kf_skb_pull(skb, 0); 
    }
    if (!skb_data) return;

    struct nlmsghdr *nlh = (struct nlmsghdr *)skb_data;
    if (nlh->nlmsg_len < sizeof(struct hmkpm_nl_req)) return;

    struct hmkpm_nl_req *req = (struct hmkpm_nl_req *)NLMSG_DATA(nlh);
    uint32_t user_pid = nlh->nlmsg_pid;
    uint64_t result = 0;

    if (nlh->nlmsg_type == HMKPM_NL_CMD_READ) {
        if (req->pid > 0) {
            uintptr_t clean_buf = (uintptr_t)req->user_buf & 0x00FFFFFFFFFFFFFFULL;
            ssize_t r = pgt_rw((pid_t)req->pid, req->addr, req->size, (void *)clean_buf, false);
            result = (r == req->size) ? 0 : (uint64_t)-1;
        }
    } 
    else if (nlh->nlmsg_type == HMKPM_NL_CMD_GET_PID) {
        for (int i = 1; i < 32768; i++) {
            struct task_struct *task = NULL;
            struct mm_struct *mm = NULL;
            kfunc(__rcu_read_lock)(); 
            task = kfunc(find_task_by_vpid)(i);
            if (task) mm = kfunc(get_task_mm)(task);
            kfunc(__rcu_read_unlock)();

            if (mm) {
                uint64_t arg_start = 0;
                // MM_ARG_START_OFFSET = 0x130 (5.10 GKI)
                hmkpm_copy_from_kernel_nofault(&arg_start, (const void *)((uintptr_t)mm + MM_ARG_START_OFFSET), 8);
                if (arg_start) {
                    char kbuf[128] = {0};
                    if (pgt_rw(i, arg_start, 127, (void *)kbuf, false) > 0) {
                        if (hmkpm_strstr(kbuf, req->pkg_name)) {
                            result = (uint64_t)i;
                            kfunc(mmput)(mm);
                            break;
                        }
                    }
                }
                kfunc(mmput)(mm);
            }
        }
    }
    else if (nlh->nlmsg_type == HMKPM_NL_CMD_GET_BASE) {
        struct task_struct *task = NULL; struct mm_struct *mm = NULL;
        kfunc(__rcu_read_lock)(); 
        task = kfunc(find_task_by_vpid)(req->pid);
        if (task) mm = kfunc(get_task_mm)(task);
        kfunc(__rcu_read_unlock)();

        if (mm) {
            uintptr_t vma = 0;
            // MM_MMAP_OFFSET = 0x00 (5.10 GKI)
            hmkpm_copy_from_kernel_nofault(&vma, (const void *)((uintptr_t)mm + MM_MMAP_OFFSET), 8);
            
            while (vma) {
                uintptr_t file = 0;
                // VMA_VM_FILE_OFFSET = 0x80 (5.10 GKI)
                hmkpm_copy_from_kernel_nofault(&file, (const void *)(vma + VMA_VM_FILE_OFFSET), 8);
                
                if (file) {
                    uintptr_t dentry = 0;
                    // FILE_F_PATH_DENTRY_OFFSET = 0x18 (5.10 GKI)
                    hmkpm_copy_from_kernel_nofault(&dentry, (const void *)(file + FILE_F_PATH_DENTRY_OFFSET), 8);
                    
                    if (dentry) {
                        char *name_ptr = NULL;
                        // DENTRY_D_NAME_NAME_OFFSET = 0x38 (5.10 GKI)
                        hmkpm_copy_from_kernel_nofault(&name_ptr, (const void *)(dentry + DENTRY_D_NAME_NAME_OFFSET), 8);
                        
                        if (name_ptr) {
                            char iname[64] = {0};
                            hmkpm_copy_from_kernel_nofault(iname, name_ptr, 63);
                            if (hmkpm_strstr(iname, req->mod_name)) { 
                                // VMA_VM_START_OFFSET = 0x00
                                hmkpm_copy_from_kernel_nofault(&result, (const void *)(vma + VMA_VM_START_OFFSET), 8);
                                break; 
                            }
                        }
                    }
                }
                uintptr_t next_vma = 0;
                // VMA_VM_NEXT_OFFSET = 0xA0 (5.10 GKI) 
                hmkpm_copy_from_kernel_nofault(&next_vma, (const void *)(vma + VMA_VM_NEXT_OFFSET), 8);
                vma = next_vma;
            }
            kfunc(mmput)(mm);
        }
    }

    if (kf_alloc_skb && kf_netlink_unicast && kf_skb_put) {
        struct sk_buff *skb_out = kf_alloc_skb(64, 0); 
        if (skb_out) {
            struct nlmsghdr *nlh_out = (struct nlmsghdr *)kf_skb_put(skb_out, NLMSG_SPACE(8));
            nlh_out->nlmsg_len = NLMSG_SPACE(8); nlh_out->nlmsg_type = 0; nlh_out->nlmsg_pid = 0;
            *(uint64_t*)NLMSG_DATA(nlh_out) = result;
            kf_netlink_unicast(g_nl_sk, skb_out, user_pid, 0);
        }
    }
    if (kf_kfree_skb) kf_kfree_skb(skb);
}

static int netlink_init(void) {
    kf_netlink_create = (void*)hmkpm_lookup_symbol("__netlink_kernel_create");
    if (!kf_netlink_create) kf_netlink_create = (void*)hmkpm_lookup_symbol("netlink_kernel_create");

    kf_netlink_unicast = (void*)hmkpm_lookup_symbol("netlink_unicast");
    kf_alloc_skb = (void*)hmkpm_lookup_symbol("__alloc_skb");
    kf_skb_put = (void*)hmkpm_lookup_symbol("skb_put");
    kf_skb_pull = (void*)hmkpm_lookup_symbol("skb_pull");
    kf_kfree_skb = (void*)hmkpm_lookup_symbol("kfree_skb");
    kv_init_net = (void*)hmkpm_lookup_symbol("init_net");

    if (!kf_netlink_create || !kf_netlink_unicast || !kf_alloc_skb || !kf_skb_put || !kv_init_net) {
        hmkpm_error("Netlink symbols missing\n"); return -1;
    }
    struct netlink_kernel_cfg cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.input = netlink_recv;

    g_nl_sk = kf_netlink_create(kv_init_net, 31, NULL, &cfg);
    if (!g_nl_sk) return -1;
    hmkpm_info("Netlink registered on port 31 (Lockless)\n");
    return 0;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
	hook_err_t err;

	if (kver < VERSION(4, 0, 0) || kver >= VERSION(6, 13, 0)) return -EINVAL;

	if (pgt_pgtable_init() != 0) return -ENOENT;
	hmkpm_sw_pan_init();

	static const char *const arm64_memset_aliases[] = {
        "__memset", "memset", "__pi___memset", "__pi_memset", "__asan_memset", "__hwasan_memset", "__mte_memset", "__arch_memset", NULL
    };
    for (int i = 0; arm64_memset_aliases[i] != NULL; i++) {
        kf_memset = (typeof(kf_memset))hmkpm_lookup_symbol(arm64_memset_aliases[i]);
        if (kf_memset) break;
	}

	kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__arch_copy_to_user");
	if (!kf___arch_copy_to_user) kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__copy_to_user");

	kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__arch_copy_from_user");
	if (!kf___arch_copy_from_user) kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__copy_from_user");

	hkfunc_match(find_task_by_vpid);
	hkfunc_match(get_task_mm);
	hkfunc_match(mmput);
	hkfunc_match(__rcu_read_lock);
	hkfunc_match(__rcu_read_unlock);

	kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
	if (!kf_copy_from_kernel_nofault) hkfunc_match(probe_kernel_read);

	if (init_error) return -ENOENT;

	if (kver >= VERSION(5, 10, 0)) {
		fsnotify_addr = hmkpm_lookup_symbol("fsnotify");
		if (fsnotify_addr) {
			err = hook_wrap7((void *)fsnotify_addr, before_fsnotify, 0, 0);
			if (!err) fsnotify_hooked = true;
		}
	}

	if (netlink_init() != 0) return -ENOENT;

	hmkpm_info("module loaded successfully\n");
	return 0;
}

static long module_control_handler(const char *args, char __user *out_msg, int outlen)
{
    if (out_msg && outlen > 0) compat_copy_to_user(out_msg, "Active\n", 7);
	return 0;
}

static long module_cleanup_handler(void *__user reserved)
{
	if (fsnotify_hooked && fsnotify_addr) {
		hook_unwrap((void *)fsnotify_addr, before_fsnotify, 0);
		fsnotify_hooked = false;
	}
    if (g_nl_sk) {
        void (*release_nl)(struct sock*) = (void*)hmkpm_lookup_symbol("netlink_kernel_release");
        if (release_nl) release_nl(g_nl_sk);
        g_nl_sk = NULL;
    }
	hmkpm_info("module cleaned up\n");
	return 0;
}

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
