// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
 *
 * KernelPatch Module (KPM) - [HMKPM]
 * 2.9.2 - Socket 通信 + WC 读取（修复初始化卡死）
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

#ifndef HMKPM_USE_SOCKET_CHANNEL
#define HMKPM_USE_SOCKET_CHANNEL 1
#endif

#ifndef HMKPM_STEALTH_BUILD
#define HMKPM_STEALTH_BUILD 0
#endif

#define HMKPM_VERSION_MAJOR	2
#define HMKPM_VERSION_MINOR	9
#define HMKPM_VERSION_PATCH	2
#define HMKPM_VERSION_CODE	(((uint32_t)HMKPM_VERSION_MAJOR << 16) | \
				 ((uint32_t)HMKPM_VERSION_MINOR << 8) | \
				 ((uint32_t)HMKPM_VERSION_PATCH))
#define HMKPM_VERSION_STR	"2.9.2"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("KernelPatch Module (KPM) HMKPM");

static bool hook_active = true;
static bool init_error = false;
static int mmap_lock_sem_offset = -1;
static unsigned long fsnotify_addr = 0;
static bool fsnotify_hooked = false;

struct inode;

#define PROC_SUPER_MAGIC	0x9fa0
#define SUPER_BLOCK_OFF 40
#define MAGIC_OFF 96

struct rw_semaphore;

#define U64_MAX				((u64)~0ULL)
#define HMKPM_TAG			"[HMKPM] "

#if HMKPM_STEALTH_BUILD
#define hmkpm_info(fmt, ...)        do {} while (0)
#define hmkpm_warn(fmt, ...)        do {} while (0)
#else
#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_warn(fmt, ...)        logkw(HMKPM_TAG fmt, ##__VA_ARGS__)
#endif
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

#ifndef MEMREMAP_WC
#define MEMREMAP_WC (1UL << 2)
#endif

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
	while (name && *name && i + 1 < dst_size) dst[i++] = *name++;
	while (*suffix && i + 1 < dst_size) dst[i++] = *suffix++;
	dst[i] = '\0';
}

static unsigned long hmkpm_lookup_symbol(const char *name)
{
	unsigned long addr;
	if (!name || !kallsyms_lookup_name) return 0;
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
long kfunc_def(probe_kernel_write)(void *dst, const void *src, size_t size);
long kfunc_def(copy_from_kernel_nofault)(void *dst, const void *src, size_t size);
long kfunc_def(copy_to_kernel_nofault)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);
void kfunc_def(__rcu_read_lock)(void);
void kfunc_def(__rcu_read_unlock)(void);
void kfunc_def(down_read)(struct rw_semaphore *sem);
void kfunc_def(up_read)(struct rw_semaphore *sem);

void *kfunc_def(kzalloc)(size_t size, unsigned int flags);
void kfunc_def(kfree)(const void *obj);
int kfunc_def(sock_register)(void *ops);
void kfunc_def(sock_unregister)(int family);
void *kfunc_def(memremap)(u64 offset, size_t size, unsigned long flags);
void kfunc_def(memunmap)(void *addr);

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);
void *kvar_def(init_net);

#define HMKPM_IOCTL_BASE        0xC0484800U
#define HMKPM_IOCTL_PROBE       (HMKPM_IOCTL_BASE + 1)
#define HMKPM_IOCTL_READ        (HMKPM_IOCTL_BASE + 2)
#define HMKPM_IOCTL_WRITE       (HMKPM_IOCTL_BASE + 3)
#define HMKPM_IOCTL_READ_BATCH  (HMKPM_IOCTL_BASE + 4)
#define HMKPM_IOCTL_WRITE_BATCH (HMKPM_IOCTL_BASE + 5)
#define HMKPM_IOCTL_V2P_BATCH   (HMKPM_IOCTL_BASE + 6)
#define HMKPM_IOCTL_SCAN        (HMKPM_IOCTL_BASE + 7)

#define HMKPM_SOCKET_SK_OFFSET   0x18
#define HMKPM_SOCKET_OPS_OFFSET  0x20
#define HMKPM_SOCKET_TYPE_OFFSET 0x04
#define HMKPM_SKC_NET_OFFSET     0x30
#define HMKPM_SOCK_RAW           3
#define HMKPM_FAKE_SK_SIZE       2048
#define HMKPM_FAMILY_START       12
#define HMKPM_FAMILY_END         40

struct inode_min {
    char pad[SUPER_BLOCK_OFF];
    void *i_sb;
};

struct super_block_min {
    char pad[MAGIC_OFF];
    unsigned long s_magic;
};

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
    if (!target) return;
    if (is_proc_inode(target)) {
        args->skip_origin = 1;
        args->ret = 0;
    }
}

#define HMKPM_MAGIC			0x484D4B504DULL
#define HMKPM_MAGIC_READ		(HMKPM_MAGIC + 1)
#define HMKPM_MAGIC_WRITE		(HMKPM_MAGIC + 2)
#define HMKPM_MAGIC_READ_BATCH		(HMKPM_MAGIC + 3)
#define HMKPM_MAGIC_WRITE_BATCH		(HMKPM_MAGIC + 4)
#define HMKPM_MAGIC_V2P_BATCH		(HMKPM_MAGIC + 5)
#define HMKPM_MAGIC_SCAN_KERNEL		(HMKPM_MAGIC + 6)
#define HMKPM_MAGIC_MAX			HMKPM_MAGIC_SCAN_KERNEL

#define HMKPM_FEATURE_READ		(1ULL << 0)
#define HMKPM_FEATURE_WRITE		(1ULL << 1)
#define HMKPM_FEATURE_READ_BATCH	(1ULL << 2)
#define HMKPM_FEATURE_WRITE_BATCH	(1ULL << 3)
#define HMKPM_FEATURE_V2P_BATCH		(1ULL << 4)
#define HMKPM_FEATURE_SCAN_KERNEL	(1ULL << 5)
#define HMKPM_FEATURE_LOCKLESS		(1ULL << 6)
#define HMKPM_FEATURE_WC_READ		(1ULL << 7)

struct hmkpm_version_info {
	uint64_t magic;
	uint32_t version_code;
	uint16_t version_major;
	uint16_t version_minor;
	uint16_t version_patch;
	uint8_t  is_lockless;
	uint8_t  is_wc_read;
	int32_t  mmap_lock_offset;
	uint64_t features;
	char version_str[16];
};

#define HMKPM_BATCH_CHUNK_ENTRIES	64U
#define HMKPM_MAX_BATCH_ENTRIES		65536U
#define HMKPM_MAX_ENTRY_SIZE		(64ULL << 20)
#define HMKPM_MAX_SINGLE_SIZE		(64ULL << 20)
#define HMKPM_MAX_BATCH_TOTAL_SIZE	(128ULL << 20)

#define HMKPM_PAGE_FLAG_PRESENT		(1U << 0)
#define HMKPM_PAGE_FLAG_RO		(1U << 1)
#define HMKPM_PAGE_FLAG_DIRTY		(1U << 2)
#define HMKPM_PAGE_FLAG_BLOCK		(1U << 3)

#define HMKPM_V2P_CHUNK_ENTRIES		64U
#define HMKPM_MAX_V2P_ENTRIES		65536U

struct hmkpm_v2p_hdr {
	int32_t pid;
	uint32_t _pad;
	uint64_t count;
};

struct hmkpm_v2p_entry {
	uint64_t va;
	uint64_t pa;
	uint32_t flags;
	uint32_t page_size;
};

#define HMKPM_V2P_HDR_SIZE		((uint64_t)sizeof(struct hmkpm_v2p_hdr))
#define HMKPM_V2P_ENTRY_SIZE		((uint64_t)sizeof(struct hmkpm_v2p_entry))

enum hmkpm_scan_type {
	HMKPM_SCAN_TYPE_I8	= 1,
	HMKPM_SCAN_TYPE_U8	= 2,
	HMKPM_SCAN_TYPE_I16	= 3,
	HMKPM_SCAN_TYPE_U16	= 4,
	HMKPM_SCAN_TYPE_I32	= 5,
	HMKPM_SCAN_TYPE_U32	= 6,
	HMKPM_SCAN_TYPE_I64	= 7,
	HMKPM_SCAN_TYPE_U64	= 8,
	HMKPM_SCAN_TYPE_F32	= 9,
	HMKPM_SCAN_TYPE_F64	= 10,
	HMKPM_SCAN_TYPE_BYTES	= 11,
};

enum hmkpm_scan_op {
	HMKPM_SCAN_OP_EXACT	= 1,
	HMKPM_SCAN_OP_RANGE	= 2,
	HMKPM_SCAN_OP_MASK	= 3,
};

#define HMKPM_MAX_SCAN_RANGES		4096U
#define HMKPM_MAX_PATTERN_LEN		256U
#define HMKPM_MAX_SCAN_MATCHES		1048576U
#define HMKPM_SCAN_MATCH_CHUNK		64U

struct hmkpm_scan_range {
	uint64_t start_va;
	uint64_t size;
};

struct hmkpm_scan_hdr {
	int32_t pid;
	uint8_t type;
	uint8_t op;
	uint8_t align;
	uint8_t _pad;
	uint32_t range_count;
	uint32_t max_matches;
	uint64_t pattern_len;
	union {
		struct { uint64_t val; uint64_t mask; } exact;
		struct { uint64_t min; uint64_t max; } range_u;
		struct { int64_t min; int64_t max; } range_i;
	} criteria;
	uint64_t matches_found;
};

#define HMKPM_SCAN_HDR_SIZE		((uint64_t)sizeof(struct hmkpm_scan_hdr))
#define HMKPM_SCAN_RANGE_SIZE		((uint64_t)sizeof(struct hmkpm_scan_range))

struct hmkpm_batch_hdr {
	int32_t pid;
	uint32_t _pad;
	uint64_t count;
	uint64_t data_total;
};

struct hmkpm_batch_entry {
	uint64_t addr;
	uint64_t size;
};

struct hmkpm_req {
	int32_t pid;
	uint32_t _pad;
	uint64_t addr;
	uint64_t size;
};

#define HMKPM_BATCH_HDR_SIZE		((uint64_t)sizeof(struct hmkpm_batch_hdr))
#define HMKPM_BATCH_ENTRY_SIZE		((uint64_t)sizeof(struct hmkpm_batch_entry))
#define HMKPM_REQ_SIZE			((uint64_t)sizeof(struct hmkpm_req))

static inline long hmkpm_copy_from_kernel_nofault(void *dst, const void *src, size_t size)
{
	kfunc_call(copy_from_kernel_nofault, dst, src, size);
	kfunc_call(probe_kernel_read, dst, src, size);
	return -ENOSYS;
}

static inline long __maybe_unused hmkpm_copy_to_kernel_nofault(void *dst, const void *src, size_t size)
{
	kfunc_call(copy_to_kernel_nofault, dst, src, size);
	kfunc_call(probe_kernel_write, dst, src, size);
	return -ENOSYS;
}

static uint64_t pgt_va_bits, pgt_phys_offset, pgt_page_offset, pgt_linear_voffset;
static uint64_t pgt_page_shift, pgt_page_size, pgt_pgd_align_mask, pgt_pgd_size;
static uint64_t pgt_page_level, pgt_user_limit, pgt_phys_limit, pgt_high_memory;
static bool pgt_tbi0;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }
static inline uint64_t pgt_virt_to_phys(uint64_t addr) { return addr - pgt_linear_voffset; }

static bool sw_pan_enabled = false;
static uint64_t reserved_ttbr0_val = 0;

/*
 * GKI 5.10 使用硬件 PAN（CONFIG_ARM64_PAN），SW PAN 在运行时默认不启用。
 * reserved_ttbr0 符号存在只说明编译时包含了 SW_PAN 相关代码，
 * 不代表运行时内核真正切换到软件 PAN 模式。
 *
 * 之前的代码只要检测到 reserved_ttbr0 符号存在就设置 sw_pan_enabled = true，
 * 导致 hmkpm_uaccess_enable() 去切换 TTBR0，而 mm_struct->pgd 的偏移
 * 在不同内核版本下可能不同，一旦偏移错误，写入非法物理地址，MMU 崩溃，系统卡死。
 *
 * 修复：强制禁用 SW_PAN。硬件 PAN 由内核的 __arch_copy_to_user/__arch_copy_from_user
 * 自动处理，不需要我们手动干预 TTBR0。
 */
static void hmkpm_sw_pan_init(void)
{
	sw_pan_enabled = false;
	reserved_ttbr0_val = 0;
	hmkpm_info("SW PAN forced disabled (GKI uses HW PAN)\n");
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
			if (task_struct_offset.active_mm_offset > 0)
				hmkpm_copy_from_kernel_nofault(&mm, (const void *)((uintptr_t)cur + task_struct_offset.active_mm_offset), sizeof(mm));
			else if (task_struct_offset.mm_offset > 0)
				hmkpm_copy_from_kernel_nofault(&mm, (const void *)((uintptr_t)cur + task_struct_offset.mm_offset), sizeof(mm));
			else if (kf_get_task_mm) { mm = kfunc(get_task_mm)(cur); need_mmput = true; }
			if (mm && mm_struct_offset.pgd_offset >= 0) {
				uint64_t cur_pgd_va = 0;
				if (hmkpm_copy_from_kernel_nofault(&cur_pgd_va, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(cur_pgd_va)) == 0 && cur_pgd_va) {
					uint64_t cur_pgd_pa = pgt_virt_to_phys(cur_pgd_va);
					uint64_t asid_mask = 0xFFFF000000000000ULL;
					uint64_t new_ttbr0 = (cur_pgd_pa & ~asid_mask) | (old_ttbr0 & asid_mask);
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

static inline uint64_t pgt_desc_to_phys(uint64_t desc)
{
	uint64_t addr_mask = (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
	return desc & addr_mask;
}

static inline bool pgt_block_allowed(int lv)
{
	if (pgt_page_shift == 14) return (lv == 2);
	return (lv == 1 || lv == 2);
}

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write)
{
	uint64_t table_va, pxd_bits, pxd_ptrs;
	int64_t start, lv;
	if (!pgd) return 0;
	if (pgd & pgt_pgd_align_mask) return 0;
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
		if (top_bits == 0) return 0;
		if (pxd_index >= (1ULL << top_bits)) return 0;
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

static uint64_t pgt_pgtable_inspect(uint64_t pgd, uint64_t va, uint32_t *out_flags, uint32_t *out_page_size)
{
	uint64_t table_va, pxd_bits, pxd_ptrs;
	int64_t start, lv;
	if (out_flags) *out_flags = 0;
	if (out_page_size) *out_page_size = 0;
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
		if (top_bits == 0) return 0;
		if (pxd_index >= (1ULL << top_bits)) return 0;
		entry_va = table_va + pxd_index * 8;
		if (hmkpm_copy_from_kernel_nofault(&desc, (const void *)entry_va, sizeof(desc)) != 0) return 0;
		type = desc & 3ULL;
		if (type == 0ULL || type == 2ULL) return 0;
		if (lv == 3) {
			uint64_t base;
			uint32_t flags = HMKPM_PAGE_FLAG_PRESENT;
			if (type != 3ULL) return 0;
			if ((desc & (1ULL << 7)) && !(desc & (1ULL << 51))) flags |= HMKPM_PAGE_FLAG_RO;
			if (desc & ((1ULL << 55) | (1ULL << 51))) flags |= HMKPM_PAGE_FLAG_DIRTY;
			base = pgt_desc_to_phys(desc);
			if (base & (pgt_page_size - 1)) return 0;
			if (validate_phys_range(base, pgt_page_size)) return 0;
			if (out_flags) *out_flags = flags;
			if (out_page_size) *out_page_size = (uint32_t)pgt_page_size;
			return base | (va & (pgt_page_size - 1));
		}
		if (type == 1ULL) {
			uint64_t block_bits, block_size, block_mask, base;
			uint32_t flags = HMKPM_PAGE_FLAG_PRESENT | HMKPM_PAGE_FLAG_BLOCK;
			if (!pgt_block_allowed((int)lv)) return 0;
			if ((desc & (1ULL << 7)) && !(desc & (1ULL << 51))) flags |= HMKPM_PAGE_FLAG_RO;
			if (desc & ((1ULL << 55) | (1ULL << 51))) flags |= HMKPM_PAGE_FLAG_DIRTY;
			block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
			if (block_bits >= 64) return 0;
			block_size = 1ULL << block_bits;
			block_mask = block_size - 1;
			base = pgt_desc_to_phys(desc);
			if (base & block_mask) return 0;
			if (validate_phys_range(base, block_size)) return 0;
			if (out_flags) *out_flags = flags;
			if (out_page_size) *out_page_size = (uint32_t)block_size;
			return (base & ~block_mask) | (va & block_mask);
		}
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
	t1sz = (tcr_el1 >> 16) & 0x3F; va1_bits = 64 - t1sz;
	t0sz = tcr_el1 & 0x3F; va0_bits = 64 - t0sz;
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
	else if (kver >= VERSION(4, 6, 0)) pgt_page_offset = -(UL(1) << (va1_bits - 1));
	else pgt_page_offset = -(UL(1) << va1_bits);
	hkvar_match(memstart_addr);
	if (!kv_memstart_addr) return -EFAULT;
	pgt_phys_offset = kvar_val(memstart_addr);
	pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;
	bool prev = init_error;
	hkvar_match(high_memory);
	if (kv_high_memory) pgt_high_memory = (uint64_t)kvar_val(high_memory);
	else { pgt_high_memory = ~0ULL; init_error = prev; }
	pgt_phys_limit = pgt_virt_to_phys(pgt_high_memory);
	pgt_tbi0 = !!(tcr_el1 & (1ULL << 37));
	hmkpm_info("pgt_init ok, va_bits=%llu shift=%llu\n", va0_bits, pgt_page_shift);
	return 0;
}

static inline bool hmkpm_is_lockless(void) { return (mmap_lock_sem_offset < 0); }

static inline uint64_t hmkpm_get_active_features(void)
{
	uint64_t feat = HMKPM_FEATURE_READ | HMKPM_FEATURE_READ_BATCH |
			HMKPM_FEATURE_V2P_BATCH | HMKPM_FEATURE_SCAN_KERNEL;
	if (!hmkpm_is_lockless()) feat |= (HMKPM_FEATURE_WRITE | HMKPM_FEATURE_WRITE_BATCH);
	else feat |= HMKPM_FEATURE_LOCKLESS;
	if (kf_memremap && kf_memunmap) feat |= HMKPM_FEATURE_WC_READ;
	return feat;
}

static inline void hmkpm_mmap_read_lock(struct mm_struct *mm)
{
	if (mm && !hmkpm_is_lockless() && kf_down_read) {
		struct rw_semaphore *sem = (struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset);
		kfunc(down_read)(sem);
	}
}

static inline void hmkpm_mmap_read_unlock(struct mm_struct *mm)
{
	if (mm && !hmkpm_is_lockless() && kf_up_read) {
		struct rw_semaphore *sem = (struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset);
		kfunc(up_read)(sem);
	}
}

#define HMKPM_BOUNCE_SIZE 512U
#define min(a, b) ((a) < (b) ? (a) : (b))

static void hmkpm_zero_user(void __user *dst, size_t size)
{
	static const uint8_t zero_chunk[256] = {0};
	if (kf___arch_clear_user) {
		uint64_t flags = hmkpm_uaccess_enable();
		kfunc(__arch_clear_user)(dst, size);
		hmkpm_uaccess_disable(flags);
		return;
	}
	uint64_t flags = hmkpm_uaccess_enable();
	while (size > 0) {
		size_t chunk = min(size, sizeof(zero_chunk));
		if (kfunc(__arch_copy_to_user)(dst, zero_chunk, chunk) != 0) break;
		dst = (void __user *)((uintptr_t)dst + chunk);
		size -= chunk;
	}
	hmkpm_uaccess_disable(flags);
}

static inline void hmkpm_fast_copy(void *dst, const void *src, size_t n)
{
	uint8_t *d = (uint8_t *)dst;
	const uint8_t *s = (const uint8_t *)src;
	while (n >= 8 && !(((uintptr_t)d | (uintptr_t)s) & 7)) { *(uint64_t *)d = *(const uint64_t *)s; d += 8; s += 8; n -= 8; }
	while (n >= 4 && !(((uintptr_t)d | (uintptr_t)s) & 3)) { *(uint32_t *)d = *(const uint32_t *)s; d += 4; s += 4; n -= 4; }
	while (n > 0) { *d++ = *s++; n--; }
}

static inline void *hmkpm_wc_map_page(uint64_t page_phys)
{
	if (!kf_memremap) return NULL;
	return kfunc(memremap)(page_phys, pgt_page_size, MEMREMAP_WC);
}

static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len,
			 void __user *local_buf, bool is_write)
{
	ssize_t total = 0;
	uint64_t pgd = 0;
	uint8_t bounce[HMKPM_BOUNCE_SIZE];
	if (!mm) return -ESRCH;
	if (mm_struct_offset.pgd_offset < 0) return -EINVAL;
	if (is_write && hmkpm_is_lockless()) return -EOPNOTSUPP;
	if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd)
		return -EFAULT;
	while (len > 0) {
		unsigned long page_off = remote_va & (pgt_page_size - 1);
		size_t page_left = (size_t)(pgt_page_size - page_off);
		size_t chunk = min(len, page_left);
		chunk = min(chunk, (size_t)HMKPM_BOUNCE_SIZE);
		if (is_write) {
			unsigned long nc = hmkpm_copy_from_user(bounce, local_buf, chunk);
			if (nc) { if (nc == chunk) { if (total > 0) break; return -EFAULT; } chunk -= nc; }
		}
		hmkpm_mmap_read_lock(mm);
		uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va, is_write);
		if (!tkpa) {
			hmkpm_mmap_read_unlock(mm);
			if (total > 0) break;
			return -EFAULT;
		}
		if (is_write) {
			void *tkva = (void *)pgt_phys_to_virt(tkpa);
			hmkpm_fast_copy(tkva, bounce, chunk);
		} else {
			uint64_t page_phys = tkpa & ~(pgt_page_size - 1);
			size_t   page_off2 = (size_t)(tkpa & (pgt_page_size - 1));
			void *mapped = hmkpm_wc_map_page(page_phys);
			if (mapped) {
				hmkpm_fast_copy(bounce, (const uint8_t *)mapped + page_off2, chunk);
				kfunc(memunmap)(mapped);
			} else if (kf_memremap) {
				hmkpm_mmap_read_unlock(mm);
				if (total > 0) break;
				return -EFAULT;
			} else {
				void *tkva = (void *)pgt_phys_to_virt(tkpa);
				hmkpm_fast_copy(bounce, tkva, chunk);
			}
		}
		hmkpm_mmap_read_unlock(mm);
		if (!is_write) {
			unsigned long nc = hmkpm_copy_to_user(local_buf, bounce, chunk);
			if (nc) { size_t copied = chunk - nc; total += (ssize_t)copied; break; }
		}
		total += (ssize_t)chunk;
		local_buf = (void __user *)((uintptr_t)local_buf + chunk);
		remote_va += chunk;
		len -= chunk;
	}
	return total;
}

static ssize_t pgt_rw(pid_t pid, uint64_t remote_va, size_t len,
		      void __user *local_buf, bool is_write)
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

static int hmkpm_do_probe(void __user *arg)
{
	struct hmkpm_version_info info;
	if (!arg) return -EINVAL;
	kfunc(memset)(&info, 0, sizeof(info));
	info.magic = HMKPM_MAGIC;
	info.version_code = HMKPM_VERSION_CODE;
	info.version_major = HMKPM_VERSION_MAJOR;
	info.version_minor = HMKPM_VERSION_MINOR;
	info.version_patch = HMKPM_VERSION_PATCH;
	info.is_lockless = hmkpm_is_lockless() ? 1 : 0;
	info.is_wc_read = (kf_memremap && kf_memunmap) ? 1 : 0;
	info.mmap_lock_offset = mmap_lock_sem_offset;
	info.features = hmkpm_get_active_features();
	const char *v = HMKPM_VERSION_STR;
	for (size_t i = 0; i < sizeof(info.version_str) - 1 && v[i]; i++)
		info.version_str[i] = v[i];
	return hmkpm_copy_to_user(arg, &info, sizeof(info)) ? -EFAULT : 0;
}

static int hmkpm_do_single(void __user *user_ptr, bool write_op)
{
	struct hmkpm_req req;
	void __user *data_ptr;
	ssize_t ret;
	if (!user_ptr) return -EINVAL;
	if (hmkpm_copy_from_user(&req, user_ptr, HMKPM_REQ_SIZE) != 0) return -EFAULT;
	if (req.size == 0) return 0;
	if ((uint64_t)req.size > HMKPM_MAX_SINGLE_SIZE) return -E2BIG;
	if (req.pid <= 0) return -EINVAL;
	req.addr = pgt_untag_user_va(req.addr);
	if (req.addr > U64_MAX - (uint64_t)req.size) return -EINVAL;
	data_ptr = (void __user *)((uint8_t __user *)user_ptr + HMKPM_REQ_SIZE);
	ret = pgt_rw((pid_t)req.pid, req.addr, req.size, data_ptr, write_op);
	if (ret < 0) return (int)ret;
	if ((uint64_t)ret != req.size) return -EFAULT;
	return 0;
}

static int hmkpm_do_batch(void __user *user_ptr, bool write_op)
{
	struct hmkpm_batch_hdr hdr;
	struct hmkpm_batch_entry chunk[HMKPM_BATCH_CHUNK_ENTRIES];
	uint64_t entries_bytes, entries_end, data_start, data_off = 0;
	uint32_t done = 0;
	int rc = 0;
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;
	if (!user_ptr) return -EINVAL;
	if (hmkpm_copy_from_user(&hdr, user_ptr, HMKPM_BATCH_HDR_SIZE) != 0) return -EFAULT;
	if (hdr.count == 0) return 0;
	if (hdr.count > HMKPM_MAX_BATCH_ENTRIES) return -E2BIG;
	if (hdr.data_total > HMKPM_MAX_BATCH_TOTAL_SIZE) return -E2BIG;
	if (hdr.pid <= 0) return -EINVAL;
	entries_bytes = (uint64_t)hdr.count * HMKPM_BATCH_ENTRY_SIZE;
	entries_end = HMKPM_BATCH_HDR_SIZE + entries_bytes;
	data_start = entries_end;
	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)((pid_t)hdr.pid);
	if (!task) { kfunc(__rcu_read_unlock)(); return -ESRCH; }
	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();
	if (!mm) return -ESRCH;
	while (done < hdr.count) {
		uint32_t chunk_count = hdr.count - done;
		uint64_t chunk_bytes;
		void __user *entry_src;
		uint32_t i;
		if (chunk_count > HMKPM_BATCH_CHUNK_ENTRIES) chunk_count = HMKPM_BATCH_CHUNK_ENTRIES;
		chunk_bytes = (uint64_t)chunk_count * HMKPM_BATCH_ENTRY_SIZE;
		entry_src = (void __user *)((uint8_t __user *)user_ptr + HMKPM_BATCH_HDR_SIZE + (uint64_t)done * HMKPM_BATCH_ENTRY_SIZE);
		if (hmkpm_copy_from_user((void *)chunk, entry_src, chunk_bytes) != 0) { rc = -EFAULT; goto out_mm; }
		for (i = 0; i < chunk_count; ++i) {
			struct hmkpm_batch_entry *e = &chunk[i];
			uint64_t req_size = e->size;
			void __user *data_ptr;
			ssize_t ret;
			if (req_size == 0) continue;
			if (req_size > HMKPM_MAX_ENTRY_SIZE) { rc = -E2BIG; goto out_mm; }
			if (req_size > hdr.data_total - data_off) { rc = -EINVAL; goto out_mm; }
			e->addr = pgt_untag_user_va(e->addr);
			if (e->addr > U64_MAX - req_size) {
				e->size = 0;
				if (!write_op) hmkpm_zero_user((void __user *)((uint8_t __user *)user_ptr + data_start + data_off), req_size);
				data_off += req_size;
				continue;
			}
			data_ptr = (void __user *)((uint8_t __user *)user_ptr + data_start + data_off);
			ret = pgt_rw_mm(mm, e->addr, req_size, data_ptr, write_op);
			if (ret < 0) { e->size = 0; if (!write_op) hmkpm_zero_user(data_ptr, req_size); }
			else if ((uint64_t)ret < req_size) { e->size = (uint64_t)ret; if (!write_op) hmkpm_zero_user((void __user *)((uintptr_t)data_ptr + ret), req_size - (uint64_t)ret); }
			else e->size = req_size;
			data_off += req_size;
		}
		if (hmkpm_copy_to_user(entry_src, chunk, chunk_bytes) != 0) { rc = -EFAULT; goto out_mm; }
		done += chunk_count;
	}
out_mm:
	if (mm) kfunc(mmput)(mm);
	return rc;
}

static int hmkpm_do_v2p_batch(void __user *user_ptr)
{
	struct hmkpm_v2p_hdr hdr;
	struct hmkpm_v2p_entry chunk[HMKPM_V2P_CHUNK_ENTRIES];
	uint64_t entries_bytes;
	uint32_t done = 0;
	int rc = 0;
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;
	uint64_t pgd = 0;
	if (!user_ptr) return -EINVAL;
	if (hmkpm_copy_from_user(&hdr, user_ptr, HMKPM_V2P_HDR_SIZE) != 0) return -EFAULT;
	if (hdr.count == 0) return 0;
	if (hdr.count > HMKPM_MAX_V2P_ENTRIES) return -E2BIG;
	if (hdr.pid <= 0) return -EINVAL;
	entries_bytes = (uint64_t)hdr.count * HMKPM_V2P_ENTRY_SIZE;
	(void)entries_bytes;
	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)((pid_t)hdr.pid);
	if (!task) { kfunc(__rcu_read_unlock)(); return -ESRCH; }
	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();
	if (!mm) return -ESRCH;
	if (mm_struct_offset.pgd_offset < 0) { rc = -EINVAL; goto out_mm; }
	if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd) { rc = -EFAULT; goto out_mm; }
	while (done < hdr.count) {
		uint32_t chunk_count = hdr.count - done;
		uint64_t chunk_bytes;
		void __user *entry_ptr;
		uint32_t i;
		if (chunk_count > HMKPM_V2P_CHUNK_ENTRIES) chunk_count = HMKPM_V2P_CHUNK_ENTRIES;
		chunk_bytes = (uint64_t)chunk_count * HMKPM_V2P_ENTRY_SIZE;
		entry_ptr = (void __user *)((uint8_t __user *)user_ptr + HMKPM_V2P_HDR_SIZE + (uint64_t)done * HMKPM_V2P_ENTRY_SIZE);
		if (hmkpm_copy_from_user((void *)chunk, entry_ptr, chunk_bytes) != 0) { rc = -EFAULT; goto out_mm; }
		hmkpm_mmap_read_lock(mm);
		for (i = 0; i < chunk_count; ++i) {
			struct hmkpm_v2p_entry *e = &chunk[i];
			uint32_t flags = 0, page_sz = 0;
			e->pa = pgt_pgtable_inspect(pgd, e->va, &flags, &page_sz);
			e->flags = flags; e->page_size = page_sz;
		}
		hmkpm_mmap_read_unlock(mm);
		if (hmkpm_copy_to_user(entry_ptr, chunk, chunk_bytes) != 0) { rc = -EFAULT; goto out_mm; }
		done += chunk_count;
	}
out_mm:
	if (mm) kfunc(mmput)(mm);
	return rc;
}

static inline bool f32_is_nan(uint32_t u) { return ((u & 0x7F800000U) == 0x7F800000U) && (u & 0x007FFFFFU); }
static inline bool f64_is_nan(uint64_t u) { return ((u & 0x7FF0000000000000ULL) == 0x7FF0000000000000ULL) && (u & 0x000FFFFFFFFFFFFFULL); }
static inline int32_t f32_to_orderable(uint32_t u) {
	if (f32_is_nan(u)) return (-2147483647 - 1);
	if (u == 0x80000000U) return 0;
	if (u & 0x80000000U) return -(int32_t)(u & 0x7FFFFFFFU);
	return (int32_t)u;
}
static inline int64_t f64_to_orderable(uint64_t u) {
	if (f64_is_nan(u)) return (-9223372036854775807LL - 1);
	if (u == 0x8000000000000000ULL) return 0;
	if (u & 0x8000000000000000ULL) return -(int64_t)(u & 0x7FFFFFFFFFFFFFFFULL);
	return (int64_t)u;
}
static inline uint16_t get_unaligned_le16(const void *p) { const uint8_t *b = (const uint8_t *)p; return (uint16_t)b[0] | ((uint16_t)b[1] << 8); }
static inline uint32_t get_unaligned_le32(const void *p) { const uint8_t *b = (const uint8_t *)p; return (uint32_t)b[0] | ((uint32_t)b[1] << 8) | ((uint32_t)b[2] << 16) | ((uint32_t)b[3] << 24); }
static inline uint64_t get_unaligned_le64(const void *p) {
	const uint8_t *b = (const uint8_t *)p;
	return (uint64_t)b[0] | ((uint64_t)b[1] << 8) | ((uint64_t)b[2] << 16) | ((uint64_t)b[3] << 24) |
	       ((uint64_t)b[4] << 32) | ((uint64_t)b[5] << 40) | ((uint64_t)b[6] << 48) | ((uint64_t)b[7] << 56);
}
static inline uint32_t hmkpm_scan_type_size(uint8_t type, uint64_t pattern_len) {
	switch (type) {
	case HMKPM_SCAN_TYPE_I8: case HMKPM_SCAN_TYPE_U8: return 1;
	case HMKPM_SCAN_TYPE_I16: case HMKPM_SCAN_TYPE_U16: return 2;
	case HMKPM_SCAN_TYPE_I32: case HMKPM_SCAN_TYPE_U32: case HMKPM_SCAN_TYPE_F32: return 4;
	case HMKPM_SCAN_TYPE_I64: case HMKPM_SCAN_TYPE_U64: case HMKPM_SCAN_TYPE_F64: return 8;
	case HMKPM_SCAN_TYPE_BYTES: return (uint32_t)pattern_len;
	default: return 0;
	}
}

static inline bool hmkpm_check_match(const void *ptr, const struct hmkpm_scan_hdr *hdr,
				     const uint8_t *pat, const uint8_t *mask)
{
	switch (hdr->type) {
	case HMKPM_SCAN_TYPE_U8: { uint8_t v = *(const uint8_t *)ptr;
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (uint8_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (uint8_t)hdr->criteria.range_u.min && v <= (uint8_t)hdr->criteria.range_u.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return (v & (uint8_t)hdr->criteria.exact.mask) == ((uint8_t)hdr->criteria.exact.val & (uint8_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_I8: { int8_t v = *(const int8_t *)ptr;
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (int8_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (int8_t)hdr->criteria.range_i.min && v <= (int8_t)hdr->criteria.range_i.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return ((uint8_t)v & (uint8_t)hdr->criteria.exact.mask) == ((uint8_t)hdr->criteria.exact.val & (uint8_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_U16: { uint16_t v = get_unaligned_le16(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (uint16_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (uint16_t)hdr->criteria.range_u.min && v <= (uint16_t)hdr->criteria.range_u.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return (v & (uint16_t)hdr->criteria.exact.mask) == ((uint16_t)hdr->criteria.exact.val & (uint16_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_I16: { int16_t v = (int16_t)get_unaligned_le16(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (int16_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (int16_t)hdr->criteria.range_i.min && v <= (int16_t)hdr->criteria.range_i.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return ((uint16_t)v & (uint16_t)hdr->criteria.exact.mask) == ((uint16_t)hdr->criteria.exact.val & (uint16_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_U32: { uint32_t v = get_unaligned_le32(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (uint32_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (uint32_t)hdr->criteria.range_u.min && v <= (uint32_t)hdr->criteria.range_u.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return (v & (uint32_t)hdr->criteria.exact.mask) == ((uint32_t)hdr->criteria.exact.val & (uint32_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_I32: { int32_t v = (int32_t)get_unaligned_le32(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (int32_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= (int32_t)hdr->criteria.range_i.min && v <= (int32_t)hdr->criteria.range_i.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return ((uint32_t)v & (uint32_t)hdr->criteria.exact.mask) == ((uint32_t)hdr->criteria.exact.val & (uint32_t)hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_U64: { uint64_t v = get_unaligned_le64(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= hdr->criteria.range_u.min && v <= hdr->criteria.range_u.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return (v & hdr->criteria.exact.mask) == (hdr->criteria.exact.val & hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_I64: { int64_t v = (int64_t)get_unaligned_le64(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) return v == (int64_t)hdr->criteria.exact.val;
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return v >= hdr->criteria.range_i.min && v <= hdr->criteria.range_i.max;
		if (hdr->op == HMKPM_SCAN_OP_MASK) return ((uint64_t)v & hdr->criteria.exact.mask) == (hdr->criteria.exact.val & hdr->criteria.exact.mask);
		break; }
	case HMKPM_SCAN_TYPE_F32: { uint32_t v = get_unaligned_le32(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) {
			uint32_t t = (uint32_t)hdr->criteria.exact.val;
			if (v == t) return true;
			if ((v == 0x00000000U || v == 0x80000000U) && (t == 0x00000000U || t == 0x80000000U)) return true;
			return false;
		}
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return f32_to_orderable(v) >= f32_to_orderable((uint32_t)hdr->criteria.range_u.min) && f32_to_orderable(v) <= f32_to_orderable((uint32_t)hdr->criteria.range_u.max);
		break; }
	case HMKPM_SCAN_TYPE_F64: { uint64_t v = get_unaligned_le64(ptr);
		if (hdr->op == HMKPM_SCAN_OP_EXACT) {
			uint64_t t = hdr->criteria.exact.val;
			if (v == t) return true;
			if ((v == 0ULL || v == 0x8000000000000000ULL) && (t == 0ULL || t == 0x8000000000000000ULL)) return true;
			return false;
		}
		if (hdr->op == HMKPM_SCAN_OP_RANGE) return f64_to_orderable(v) >= f64_to_orderable(hdr->criteria.range_u.min) && f64_to_orderable(v) <= f64_to_orderable(hdr->criteria.range_u.max);
		break; }
	case HMKPM_SCAN_TYPE_BYTES: {
		const uint8_t *b = (const uint8_t *)ptr;
		uint64_t plen = hdr->pattern_len;
		if (hdr->op == HMKPM_SCAN_OP_EXACT) {
			for (uint64_t i = 0; i < plen; i++) if (b[i] != pat[i]) return false;
			return true;
		}
		if (hdr->op == HMKPM_SCAN_OP_MASK) {
			for (uint64_t i = 0; i < plen; i++) if ((b[i] & mask[i]) != (pat[i] & mask[i])) return false;
			return true;
		}
		break; }
	default: break;
	}
	return false;
}

static int hmkpm_do_scan(void __user *user_ptr)
{
	struct hmkpm_scan_hdr hdr;
	uint8_t pattern_buf[HMKPM_MAX_PATTERN_LEN];
	uint8_t mask_buf[HMKPM_MAX_PATTERN_LEN];
	uint64_t match_chunk[HMKPM_SCAN_MATCH_CHUNK];
	uint32_t match_chunk_count = 0;
	uint64_t total_matches = 0;
	uint64_t ranges_bytes, pattern_bytes = 0, mask_bytes = 0;
	uint64_t matches_start;
	uint32_t type_size, align_step;
	int rc = 0;
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;
	uint64_t pgd = 0;
	void __user *user_matches_ptr;

	if (!user_ptr) return -EINVAL;
	if (hmkpm_copy_from_user(&hdr, user_ptr, HMKPM_SCAN_HDR_SIZE) != 0) return -EFAULT;
	if (hdr.pid <= 0) return -EINVAL;
	if (hdr.range_count == 0 || hdr.range_count > HMKPM_MAX_SCAN_RANGES) return -EINVAL;
	if (hdr.type < HMKPM_SCAN_TYPE_I8 || hdr.type > HMKPM_SCAN_TYPE_BYTES) return -EINVAL;
	if (hdr.op < HMKPM_SCAN_OP_EXACT || hdr.op > HMKPM_SCAN_OP_MASK) return -EINVAL;
	if (hdr.type == HMKPM_SCAN_TYPE_BYTES && hdr.op == HMKPM_SCAN_OP_RANGE) return -EINVAL;
	if ((hdr.type == HMKPM_SCAN_TYPE_F32 || hdr.type == HMKPM_SCAN_TYPE_F64) && hdr.op == HMKPM_SCAN_OP_MASK) return -EINVAL;
	if (hdr.type == HMKPM_SCAN_TYPE_BYTES) {
		if (hdr.pattern_len == 0 || hdr.pattern_len > HMKPM_MAX_PATTERN_LEN) return -EINVAL;
		pattern_bytes = hdr.pattern_len;
		if (hdr.op == HMKPM_SCAN_OP_MASK) mask_bytes = hdr.pattern_len;
	}
	type_size = hmkpm_scan_type_size(hdr.type, hdr.pattern_len);
	if (type_size == 0) return -EINVAL;
	if (hdr.align == 0) align_step = (type_size <= 8 && hdr.type != HMKPM_SCAN_TYPE_BYTES) ? type_size : 1;
	else if (hdr.align == 1 || hdr.align == 2 || hdr.align == 4 || hdr.align == 8) align_step = hdr.align;
	else return -EINVAL;
	if (hdr.max_matches > HMKPM_MAX_SCAN_MATCHES) return -E2BIG;
	ranges_bytes = (uint64_t)hdr.range_count * HMKPM_SCAN_RANGE_SIZE;
	matches_start = HMKPM_SCAN_HDR_SIZE + ranges_bytes + pattern_bytes + mask_bytes;
	if (hdr.type == HMKPM_SCAN_TYPE_BYTES) {
		void __user *pat_ptr = (void __user *)((uint8_t __user *)user_ptr + HMKPM_SCAN_HDR_SIZE + ranges_bytes);
		if (hmkpm_copy_from_user(pattern_buf, pat_ptr, pattern_bytes) != 0) { rc = -EFAULT; goto out; }
		if (hdr.op == HMKPM_SCAN_OP_MASK) {
			void __user *mask_ptr = (void __user *)((uint8_t __user *)pat_ptr + pattern_bytes);
			if (hmkpm_copy_from_user(mask_buf, mask_ptr, mask_bytes) != 0) { rc = -EFAULT; goto out; }
		}
	}
	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)((pid_t)hdr.pid);
	if (!task) { kfunc(__rcu_read_unlock)(); return -ESRCH; }
	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();
	if (!mm) return -ESRCH;
	if (mm_struct_offset.pgd_offset < 0) { rc = -EINVAL; goto out_mm; }
	if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd) { rc = -EFAULT; goto out_mm; }
	user_matches_ptr = (void __user *)((uint8_t __user *)user_ptr + matches_start);
	for (uint32_t r_idx = 0; r_idx < hdr.range_count; ++r_idx) {
		struct hmkpm_scan_range r;
		void __user *r_ptr = (void __user *)((uint8_t __user *)user_ptr + HMKPM_SCAN_HDR_SIZE + (uint64_t)r_idx * HMKPM_SCAN_RANGE_SIZE);
		if (hmkpm_copy_from_user(&r, r_ptr, HMKPM_SCAN_RANGE_SIZE) != 0) { rc = -EFAULT; goto out_mm; }
		if (r.size == 0) continue;
		uint64_t start_va = pgt_untag_user_va(r.start_va);
		if (start_va > U64_MAX - r.size) continue;
		uint64_t end_va = start_va + r.size;
		uint64_t cur_va = start_va;
		if (cur_va % align_step != 0) cur_va += (align_step - (cur_va % align_step));
		if (cur_va >= end_va) continue;
		while (cur_va < end_va) {
			uint64_t page_base = cur_va & ~(pgt_page_size - 1);
			uint64_t page_off = cur_va - page_base;
			uint64_t bytes_left_in_page = pgt_page_size - page_off;
			uint64_t bytes_to_scan = min(bytes_left_in_page, end_va - cur_va);
			hmkpm_mmap_read_lock(mm);
			uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, cur_va, false);
			if (!tkpa) {
				hmkpm_mmap_read_unlock(mm);
				cur_va = page_base + pgt_page_size;
				if (cur_va % align_step != 0) cur_va += (align_step - (cur_va % align_step));
				if (cur_va >= end_va) break;
				continue;
			}
			const uint8_t *tkva = (const uint8_t *)pgt_phys_to_virt(tkpa);
			const uint8_t *scan_base = tkva;
			uint64_t off = 0;
			while (off + type_size <= bytes_to_scan) {
				if (hmkpm_check_match(scan_base + off, &hdr, pattern_buf, mask_buf)) {
					uint64_t match_va = cur_va + off;
					if (total_matches < (uint64_t)hdr.max_matches) {
						match_chunk[match_chunk_count++] = match_va;
						if (match_chunk_count == HMKPM_SCAN_MATCH_CHUNK) {
							uint64_t write_idx = total_matches - HMKPM_SCAN_MATCH_CHUNK + 1;
							void __user *dst = (void __user *)((uint64_t __user *)user_matches_ptr + write_idx);
							hmkpm_mmap_read_unlock(mm);
							if (hmkpm_copy_to_user(dst, match_chunk, sizeof(match_chunk)) != 0) { rc = -EFAULT; goto out_mm; }
							hmkpm_mmap_read_lock(mm);
							match_chunk_count = 0;
						}
					}
					total_matches++;
				}
				off += align_step;
			}
			if (off < bytes_to_scan && (cur_va + off + type_size <= end_va) && type_size > 1) {
				uint64_t next_page_va = page_base + pgt_page_size;
				uint64_t next_tkpa = pgt_pgtable_to_tkpa(pgd, next_page_va, false);
				if (next_tkpa) {
					const uint8_t *next_tkva = (const uint8_t *)pgt_phys_to_virt(next_tkpa);
					uint8_t boundary_buf[HMKPM_MAX_PATTERN_LEN];
					while (off < bytes_to_scan && (cur_va + off + type_size <= end_va)) {
						uint64_t first_part = bytes_to_scan - off;
						uint64_t second_part = type_size - first_part;
						if (first_part <= sizeof(boundary_buf) && second_part <= sizeof(boundary_buf) - first_part) {
							for (uint64_t b_i = 0; b_i < first_part; b_i++) boundary_buf[b_i] = scan_base[off + b_i];
							for (uint64_t b_i = 0; b_i < second_part; b_i++) boundary_buf[first_part + b_i] = next_tkva[b_i];
							if (hmkpm_check_match(boundary_buf, &hdr, pattern_buf, mask_buf)) {
								uint64_t match_va = cur_va + off;
								if (total_matches < (uint64_t)hdr.max_matches) {
									match_chunk[match_chunk_count++] = match_va;
									if (match_chunk_count == HMKPM_SCAN_MATCH_CHUNK) {
										uint64_t write_idx = total_matches - HMKPM_SCAN_MATCH_CHUNK + 1;
										void __user *dst = (void __user *)((uint64_t __user *)user_matches_ptr + write_idx);
										hmkpm_mmap_read_unlock(mm);
										if (hmkpm_copy_to_user(dst, match_chunk, sizeof(match_chunk)) != 0) { rc = -EFAULT; goto out_mm; }
										hmkpm_mmap_read_lock(mm);
										match_chunk_count = 0;
									}
								}
								total_matches++;
							}
						}
						off += align_step;
					}
				}
			}
			hmkpm_mmap_read_unlock(mm);
			cur_va += bytes_to_scan;
		}
	}
	if (match_chunk_count > 0) {
		uint64_t stored = min(total_matches, (uint64_t)hdr.max_matches);
		uint64_t write_idx = stored - match_chunk_count;
		void __user *dst = (void __user *)((uint64_t __user *)user_matches_ptr + write_idx);
		if (hmkpm_copy_to_user(dst, match_chunk, (uint64_t)match_chunk_count * sizeof(uint64_t)) != 0) { rc = -EFAULT; goto out_mm; }
	}
	{
		void __user *mf_dst = (void __user *)((uint8_t __user *)user_ptr + __builtin_offsetof(struct hmkpm_scan_hdr, matches_found));
		if (hmkpm_copy_to_user(mf_dst, &total_matches, sizeof(total_matches)) != 0) rc = -EFAULT;
	}
out_mm:
	if (mm) kfunc(mmput)(mm);
out:
	return rc;
}

#if HMKPM_USE_SOCKET_CHANNEL

struct hmkpm_proto_ops_layout {
	int family;
	void *owner;
	int (*release)(void *sock);
	int (*bind)(void *sock, void *addr, int len);
	int (*connect)(void *sock, void *addr, int len, int flags);
	int (*socketpair)(void *s1, void *s2);
	int (*accept)(void *sock, void *newsock, int flags, int kern);
	int (*getname)(void *sock, void *addr, int peer);
	void *poll;
	int (*ioctl)(void *sock, unsigned int cmd, unsigned long arg);
	void *compat_ioctl;
	void *gettstamp;
	int (*listen)(void *sock, int len);
	int (*shutdown)(void *sock, int flags);
	int (*setsockopt)(void *sock, int l, int o, void *opt, unsigned int len);
	int (*getsockopt)(void *sock, int l, int o, char *opt, int *len);
	void *show_fdinfo;
	int (*sendmsg)(void *sock, void *msg, size_t len);
	int (*recvmsg)(void *sock, void *msg, size_t len, int flags);
	int (*mmap)(void *file, void *sock, void *vma);
	void *sendpage;
	void *splice_read;
	void *set_peek_off;
};

struct hmkpm_net_proto_family {
	int family;
	int (*create)(void *net, void *sock, int protocol, int kern);
	void *owner;
};

static int hmkpm_sock_noop3(void *a, void *b, int c) { (void)a; (void)b; (void)c; return -EOPNOTSUPP; }
static int hmkpm_sock_noop4(void *a, void *b, int c, int d) { (void)a; (void)b; (void)c; (void)d; return -EOPNOTSUPP; }

static int hmkpm_sock_release(void *sock);
static int hmkpm_sock_ioctl(void *sock, unsigned int cmd, unsigned long arg);

static struct hmkpm_proto_ops_layout hmkpm_proto_ops_inst = {
	.family = 0, .owner = NULL,
	.release = hmkpm_sock_release,
	.bind = hmkpm_sock_noop3,
	.connect = hmkpm_sock_noop4,
	.socketpair = (void *)hmkpm_sock_noop3,
	.accept = hmkpm_sock_noop4,
	.getname = hmkpm_sock_noop3,
	.poll = NULL, .ioctl = hmkpm_sock_ioctl,
	.compat_ioctl = NULL, .gettstamp = NULL,
	.listen = hmkpm_sock_noop3, .shutdown = hmkpm_sock_noop3,
	.setsockopt = NULL, .getsockopt = NULL, .show_fdinfo = NULL,
	.sendmsg = NULL, .recvmsg = NULL,
	.mmap = hmkpm_sock_noop3,
	.sendpage = NULL, .splice_read = NULL, .set_peek_off = NULL,
};

static struct hmkpm_net_proto_family hmkpm_family_inst = { .family = 0, .create = NULL, .owner = NULL };

static int hmkpm_sock_release(void *sock)
{
	/*
	 * create 时未分配 sk，release 无需释放任何资源。
	 * 不读 sock->sk，避免万一被外部改写成垃圾值。
	 */
	(void)sock;
	return 0;
}

static int hmkpm_sock_ioctl(void *sock, unsigned int cmd, unsigned long arg)
{
	(void)sock;
	void __user *uarg = (void __user *)arg;
	if (!READ_ONCE(hook_active)) return -ENODEV;
	switch (cmd) {
	case HMKPM_IOCTL_PROBE:       return hmkpm_do_probe(uarg);
	case HMKPM_IOCTL_READ:        return hmkpm_do_single(uarg, false);
	case HMKPM_IOCTL_WRITE:       return hmkpm_do_single(uarg, true);
	case HMKPM_IOCTL_READ_BATCH:  return hmkpm_do_batch(uarg, false);
	case HMKPM_IOCTL_WRITE_BATCH: return hmkpm_do_batch(uarg, true);
	case HMKPM_IOCTL_V2P_BATCH:   return hmkpm_do_v2p_batch(uarg);
	case HMKPM_IOCTL_SCAN:        return hmkpm_do_scan(uarg);
	default:                      return -EINVAL;
	}
}

static int hmkpm_sock_create(void *net, void *sock, int protocol, int kern)
{
	(void)net; (void)protocol; (void)kern;
	if (!sock) return -EINVAL;

	short stype = *(short *)((char *)sock + HMKPM_SOCKET_TYPE_OFFSET);
	if (stype != HMKPM_SOCK_RAW) return -ENOKEY;

	/*
	 * 关键：此函数在 RCU 读锁内被 __sock_create() 调用。
	 * 绝不能调用 kzalloc(GFP_KERNEL)（会 sleep），否则触发
	 * "BUG: scheduling while atomic"，系统卡死。
	 *
	 * sock->sk 必须显式置 NULL：
	 *   1. SELinux 的 security_socket_post_create() 会检查 `if (!sock->sk) return 0;`，
	 *      NULL 是合法的。
	 *   2. sock_alloc() 分配 inode 时 sock->sk 可能是垃圾值，
	 *      如果不显式清 NULL，后续路径可能误访问它导致崩溃。
	 */
	*(void **)((char *)sock + HMKPM_SOCKET_SK_OFFSET) = NULL;
	*(void **)((char *)sock + HMKPM_SOCKET_OPS_OFFSET) = (void *)&hmkpm_proto_ops_inst;
	*(int *)((char *)sock) = 1;  /* SS_UNCONNECTED */

	return 0;
}

static int hmkpm_proto_family_id = -1;

static int hmkpm_register_family(void)
{
	hmkpm_family_inst.create = hmkpm_sock_create;
	hmkpm_family_inst.owner = NULL;
	for (int f = HMKPM_FAMILY_START; f < HMKPM_FAMILY_END; f++) {
		hmkpm_family_inst.family = f;
		if (kfunc(sock_register)(&hmkpm_family_inst) == 0) {
			hmkpm_proto_ops_inst.family = f;
			hmkpm_proto_family_id = f;
			return 0;
		}
	}
	return -ENOENT;
}

#endif

#if !HMKPM_USE_SOCKET_CHANNEL
static void hmkpm_handle(hook_fargs3_t *args, void *udata)
{
	void __user *user_ptr;
	uint64_t magic = syscall_argn(args, 0);
	if (likely(!(magic >= HMKPM_MAGIC && magic <= HMKPM_MAGIC_MAX))) return;
	if (!READ_ONCE(hook_active)) return;
	if (current_uid() != 0) return;
	args->skip_origin = 1;
	if (magic == HMKPM_MAGIC) { args->ret = (uint64_t)(long)hmkpm_do_probe((void __user *)syscall_argn(args, 1)); return; }
	user_ptr = (void __user *)syscall_argn(args, 1);
	if (magic == HMKPM_MAGIC_READ) { args->ret = (uint64_t)(long)hmkpm_do_single(user_ptr, false); return; }
	if (magic == HMKPM_MAGIC_WRITE) { args->ret = (uint64_t)(long)hmkpm_do_single(user_ptr, true); return; }
	if (magic == HMKPM_MAGIC_READ_BATCH) { args->ret = (uint64_t)(long)hmkpm_do_batch(user_ptr, false); return; }
	if (magic == HMKPM_MAGIC_WRITE_BATCH) { args->ret = (uint64_t)(long)hmkpm_do_batch(user_ptr, true); return; }
	if (magic == HMKPM_MAGIC_V2P_BATCH) { args->ret = (uint64_t)(long)hmkpm_do_v2p_batch(user_ptr); return; }
	if (magic == HMKPM_MAGIC_SCAN_KERNEL) { args->ret = (uint64_t)(long)hmkpm_do_scan(user_ptr); return; }
	args->ret = (uint64_t)(long)-EINVAL;
}
#endif

static inline int get_mm_mmap_lock_offset(void)
{
	if (kver >= VERSION(6, 12, 0)) return 136;
	else if (kver >= VERSION(6, 6, 0)) return 144;
	else if (kver >= VERSION(6, 1, 0)) return 96;
	else if (kver >= VERSION(5, 15, 0)) return 104;
	else if (kver >= VERSION(5, 10, 0)) return 112;
	else return -1;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
	hook_err_t err;
	(void)args; (void)event; (void)reserved;

	if (kver < VERSION(4, 0, 0) || kver >= VERSION(6, 13, 0)) {
		hmkpm_error("Kernel version not supported\n");
		return -EINVAL;
	}
	if (pgt_pgtable_init() != 0) {
		hmkpm_error("pgt init failed\n");
		return -ENOENT;
	}
	hmkpm_sw_pan_init();

	static const char *const memset_aliases[] = {
		"__memset", "memset", "__pi___memset", "__pi_memset",
		"__asan_memset", "__hwasan_memset", "__mte_memset", "__arch_memset", NULL
	};
	for (int i = 0; memset_aliases[i]; i++) {
		kf_memset = (typeof(kf_memset))hmkpm_lookup_symbol(memset_aliases[i]);
		if (kf_memset) break;
	}
	if (!kf_memset) { hmkpm_error("no memset\n"); init_error = true; }

	kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__arch_copy_to_user");
	if (!kf___arch_copy_to_user) kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__copy_to_user");
	if (!kf___arch_copy_to_user) { hmkpm_error("no copy_to_user\n"); init_error = true; }

	kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__arch_copy_from_user");
	if (!kf___arch_copy_from_user) kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__copy_from_user");
	if (!kf___arch_copy_from_user) { hmkpm_error("no copy_from_user\n"); init_error = true; }

	kf___arch_clear_user = (typeof(kf___arch_clear_user))hmkpm_lookup_symbol("__arch_clear_user");
	if (!kf___arch_clear_user) kf___arch_clear_user = (typeof(kf___arch_clear_user))hmkpm_lookup_symbol("__clear_user");
	if (!kf___arch_clear_user) kf___arch_clear_user = (typeof(kf___arch_clear_user))hmkpm_lookup_symbol("clear_user");

	hkfunc_match(find_task_by_vpid);
	hkfunc_match(get_task_mm);
	hkfunc_match(mmput);
	hkfunc_match(__rcu_read_lock);
	hkfunc_match(__rcu_read_unlock);

	kf_down_read = (typeof(kf_down_read))hmkpm_lookup_symbol("down_read");
	if (!kf_down_read) kf_down_read = (typeof(kf_down_read))hmkpm_lookup_symbol("_down_read");
	if (!kf_down_read) kf_down_read = (typeof(kf_down_read))hmkpm_lookup_symbol("__down_read");

	kf_up_read = (typeof(kf_up_read))hmkpm_lookup_symbol("up_read");
	if (!kf_up_read) kf_up_read = (typeof(kf_up_read))hmkpm_lookup_symbol("_up_read");
	if (!kf_up_read) kf_up_read = (typeof(kf_up_read))hmkpm_lookup_symbol("__up_read");

	kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
	if (!kf_copy_from_kernel_nofault) hkfunc_match(probe_kernel_read);
	kf_copy_to_kernel_nofault = (typeof(kf_copy_to_kernel_nofault))hmkpm_lookup_symbol("copy_to_kernel_nofault");
	if (!kf_copy_to_kernel_nofault) hkfunc_match(probe_kernel_write);

	kf_memremap = (typeof(kf_memremap))hmkpm_lookup_symbol("memremap");
	kf_memunmap = (typeof(kf_memunmap))hmkpm_lookup_symbol("memunmap");
	if (kf_memremap && kf_memunmap) {
		hmkpm_error("[HMKPM] memremap=%lx memunmap=%lx WC active\n",
			    (unsigned long)kf_memremap, (unsigned long)kf_memunmap);
	} else {
		hmkpm_error("[HMKPM] WARN: memremap/memunmap missing\n");
	}

	mmap_lock_sem_offset = get_mm_mmap_lock_offset();
	if (mmap_lock_sem_offset < 0 || !kf_down_read || !kf_up_read) {
		hmkpm_warn("lockless mode\n");
		mmap_lock_sem_offset = -1;
	}

	if (init_error) {
		hmkpm_error("symbol resolve failed\n");
		return -ENOENT;
	}

	if (kver >= VERSION(5, 10, 0)) {
		fsnotify_addr = hmkpm_lookup_symbol("fsnotify");
		if (fsnotify_addr) {
			err = hook_wrap7((void *)fsnotify_addr, before_fsnotify, 0, 0);
			fsnotify_hooked = (err == 0);
		}
	}

#if HMKPM_USE_SOCKET_CHANNEL
	kf_kzalloc = (typeof(kf_kzalloc))hmkpm_lookup_symbol("kzalloc");
	kf_kfree = (typeof(kf_kfree))hmkpm_lookup_symbol("kfree");
	kf_sock_register = (typeof(kf_sock_register))hmkpm_lookup_symbol("sock_register");
	if (!kf_sock_register) kf_sock_register = (typeof(kf_sock_register))hmkpm_lookup_symbol("__sock_register");
	kf_sock_unregister = (typeof(kf_sock_unregister))hmkpm_lookup_symbol("sock_unregister");
	kv_init_net = (void *)hmkpm_lookup_symbol("init_net");

	if (!kf_sock_register || !kf_sock_unregister) {
		hmkpm_error("sock_register/sock_unregister missing\n");
		return -ENOENT;
	}

	if (hmkpm_register_family() != 0) {
		hmkpm_error("register family failed\n");
		return -ENOENT;
	}
	hmkpm_error("[HMKPM] socket channel ready family=%d\n", hmkpm_proto_family_id);
#else
	err = hook_syscalln(__NR_getresuid, 3, (void *)hmkpm_handle, 0, 0);
	if (err) {
		hmkpm_error("hook getresuid failed: %d\n", err);
		if (fsnotify_hooked) { hook_unwrap((void *)fsnotify_addr, before_fsnotify, 0); fsnotify_hooked = false; }
		return -ENOENT;
	}
	hmkpm_error("[HMKPM] getresuid channel ready\n");
#endif

	hmkpm_error("[HMKPM] loaded\n");
	return 0;
}

static long module_cleanup_handler(void *__user reserved)
{
	(void)reserved;
	if (fsnotify_hooked && fsnotify_addr) {
		hook_unwrap((void *)fsnotify_addr, before_fsnotify, 0);
		fsnotify_hooked = false;
	}
#if HMKPM_USE_SOCKET_CHANNEL
	if (hmkpm_proto_family_id >= 0 && kf_sock_unregister) {
		kf_sock_unregister(hmkpm_proto_family_id);
		hmkpm_proto_family_id = -1;
	}
#else
	unhook_syscalln(__NR_getresuid, (void *)hmkpm_handle, 0);
#endif
	hmkpm_error("[HMKPM] cleanup\n");
	return 0;
}

static inline int kpm_isspace(char c) { return (c == ' ' || c == '\t' || c == '\n' || c == '\r'); }
static const char *kpm_skip_spaces(const char *s) { if (!s) return ""; while (*s && kpm_isspace(*s)) s++; return s; }
static bool kpm_streq(const char *s1, const char *s2) {
	if (!s1 || !s2) return false;
	while (*s1 && *s2) { if (*s1 != *s2) return false; s1++; s2++; }
	while (*s1 && kpm_isspace(*s1)) s1++;
	return (*s1 == '\0' && *s2 == '\0');
}
static void send_user_msg(char __user *out_msg, int outlen, const char *msg) {
	int len = 0; char zero = '\0';
	if (!out_msg || outlen <= 0 || !msg) return;
	while (msg[len] && len < outlen - 1) len++;
	if (len > 0) compat_copy_to_user(out_msg, msg, len);
	compat_copy_to_user((char __user *)out_msg + len, &zero, 1);
}

static long module_control_handler(const char *args, char __user *out_msg, int outlen)
{
	const char *cmd = kpm_skip_spaces(args);
	if (kpm_streq(cmd, "enable") || kpm_streq(cmd, "on") || kpm_streq(cmd, "1")) {
		WRITE_ONCE(hook_active, true); send_user_msg(out_msg, outlen, "enabled\n"); return 0;
	}
	if (kpm_streq(cmd, "disable") || kpm_streq(cmd, "off") || kpm_streq(cmd, "0")) {
		WRITE_ONCE(hook_active, false); send_user_msg(out_msg, outlen, "disabled\n"); return 0;
	}
	if (kpm_streq(cmd, "status") || kpm_streq(cmd, "state")) {
		send_user_msg(out_msg, outlen, READ_ONCE(hook_active) ? "active\n" : "inactive\n"); return 0;
	}
	if (kpm_streq(cmd, "toggle")) {
		WRITE_ONCE(hook_active, !hook_active);
		send_user_msg(out_msg, outlen, hook_active ? "enabled\n" : "disabled\n"); return 0;
	}
	send_user_msg(out_msg, outlen, "unknown\n");
	return -EINVAL;
}

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
