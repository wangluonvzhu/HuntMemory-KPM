// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
 *
 * KernelPatch Module (KPM) - [HMKPM] (read-only build)
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
#define HMKPM_VERSION_PATCH	1
#define HMKPM_VERSION_CODE	(((uint32_t)HMKPM_VERSION_MAJOR << 16) | \
				 ((uint32_t)HMKPM_VERSION_MINOR << 8) | \
				 ((uint32_t)HMKPM_VERSION_PATCH))
#define HMKPM_VERSION_STR	"2.9.1-ro"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("KernelPatch Module (KPM) HMKPM - read-only");

static bool hook_active = true;
static bool init_error = false;
static unsigned long fsnotify_addr = 0;
static bool fsnotify_hooked = false;

struct inode;

#define PROC_SUPER_MAGIC	0x9fa0

// gki 5.10 to 6.12 same offset
#define SUPER_BLOCK_OFF 40
#define MAGIC_OFF 96

#define U64_MAX				((u64)~0ULL)
#define HMKPM_TAG			"[HMKPM] "

#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_warn(fmt, ...)        logkw(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

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

    if (!i)
        return false;

    sb = (const struct super_block_min *)READ_ONCE(i->i_sb);
    if (!sb)
        return false;

    return (READ_ONCE(sb->s_magic) == PROC_SUPER_MAGIC);
}

static void before_fsnotify(hook_fargs7_t *args, void *udata)
{
    struct inode *dir;
    struct inode *inode;
    struct inode *target;

    if (!READ_ONCE(hook_active) || !args)
        return;

    dir   = (struct inode *)args->arg3;
    inode = (struct inode *)args->arg5;
    target = inode ? inode : dir;

    if (!target)
        return;

    if (is_proc_inode(target)) {
        args->skip_origin = 1;
        args->ret = 0;
    }
}

/* ========================================================================
 * Channel: getresuid, intercepted when arg0 == HMKPM_MAGIC.
 * ======================================================================== */

#define HMKPM_MAGIC			0x484D4B504DULL /* "HMKPM" */
#define HMKPM_MAGIC_READ		(HMKPM_MAGIC + 1)
#define HMKPM_MAGIC_READ_BATCH		(HMKPM_MAGIC + 3)
#define HMKPM_MAGIC_MAX			HMKPM_MAGIC_READ_BATCH

/* Feature Flags */
#define HMKPM_FEATURE_READ		(1ULL << 0)
#define HMKPM_FEATURE_READ_BATCH	(1ULL << 2)
#define HMKPM_FEATURE_LOCKLESS		(1ULL << 6)
#define HMKPM_ALL_FEATURES		(HMKPM_FEATURE_READ | HMKPM_FEATURE_READ_BATCH | HMKPM_FEATURE_LOCKLESS)

/* Probe & Version Information */
struct hmkpm_version_info {
	uint64_t magic;            
	uint32_t version_code;     
	uint16_t version_major;    
	uint16_t version_minor;    
	uint16_t version_patch;    
	uint8_t  is_lockless;      
	uint8_t  _pad;
	int32_t  mmap_lock_offset; 
	uint64_t features;         
	char version_str[16];      
};

#define HMKPM_BATCH_CHUNK_ENTRIES	64U
#define HMKPM_MAX_BATCH_ENTRIES		65536U
#define HMKPM_MAX_ENTRY_SIZE		(64ULL << 20)
#define HMKPM_MAX_SINGLE_SIZE		(64ULL << 20)
#define HMKPM_MAX_BATCH_TOTAL_SIZE	(128ULL << 20)

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
	if (kf_copy_from_kernel_nofault)
		return kfunc(copy_from_kernel_nofault)(dst, src, size);
	if (kf_probe_kernel_read)
		return kfunc(probe_kernel_read)(dst, src, size);
	return -ENOSYS;
}

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
static bool pgt_tbi0;

static inline uint64_t pgt_phys_to_virt(uint64_t phys)
{
	return phys + pgt_linear_voffset;
}

static inline uint64_t pgt_virt_to_phys(uint64_t addr)
{
	return addr - pgt_linear_voffset;
}

/* ========================================================================
 * Software PAN Support
 * ======================================================================== */

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

	if (!sw_pan_enabled && sym_reserved) {
		uint64_t mmfr1;
		asm volatile("mrs %0, id_aa64mmfr1_el1" : "=r"(mmfr1));
		if (((mmfr1 >> 20) & 0xFULL) == 0) {
			sw_pan_enabled = true;
		}
	}

	if (sw_pan_enabled) {
		hmkpm_info("SW PAN detected: reserved_ttbr0=0x%llx\n", reserved_ttbr0_val);
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
				hmkpm_copy_from_kernel_nofault(&mm,
					(const void *)((uintptr_t)cur + task_struct_offset.active_mm_offset),
					sizeof(mm));
			} else if (task_struct_offset.mm_offset > 0) {
				hmkpm_copy_from_kernel_nofault(&mm,
					(const void *)((uintptr_t)cur + task_struct_offset.mm_offset),
					sizeof(mm));
			} else if (kf_get_task_mm) {
				mm = kfunc(get_task_mm)(cur);
				need_mmput = true;
			}

			if (mm && mm_struct_offset.pgd_offset >= 0) {
				uint64_t cur_pgd_va = 0;
				if (hmkpm_copy_from_kernel_nofault(&cur_pgd_va,
					(const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset),
					sizeof(cur_pgd_va)) == 0 && cur_pgd_va) {
					uint64_t cur_pgd_pa = pgt_virt_to_phys(cur_pgd_va);
					uint64_t asid_mask = 0xFFFF000000000000ULL;
					uint64_t new_ttbr0 = (cur_pgd_pa & ~asid_mask) | (old_ttbr0 & asid_mask);
					asm volatile("msr ttbr0_el1, %0\n isb\n" :: "r"(new_ttbr0) : "memory");
				}
			}

			if (mm && need_mmput && kf_mmput) {
				kfunc(mmput)(mm);
			}
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

static inline int validate_virt_range(uint64_t va, uint64_t size)
{
	uint64_t last;

	if (unlikely(size == 0))
		return -EINVAL;

	if (unlikely(va < pgt_page_offset))
		return -EFAULT;

	if (unlikely(va > U64_MAX - size))
		return -EFAULT;

	last = va + size - 1;
	if (unlikely(last >= pgt_high_memory))
		return -EFAULT;

	return 0;
}

static inline int validate_phys_range(uint64_t phys, uint64_t size)
{
	uint64_t va;

	if (unlikely(size == 0))
		return -EINVAL;

	if (unlikely((phys >> 48) != 0))
		return -EFAULT;

	if (unlikely(phys > U64_MAX - size))
		return -EFAULT;

	va = pgt_phys_to_virt(phys);
	return validate_virt_range(va, size);
}

static inline uint64_t pgt_untag_user_va(uint64_t va)
{
	return va & 0x00FFFFFFFFFFFFFFULL;
}

static inline uint64_t pgt_desc_to_phys(uint64_t desc)
{
	uint64_t addr_mask =
		(((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
	return desc & addr_mask;
}

static inline bool pgt_block_allowed(int lv)
{
	if (pgt_page_shift == 14)
		return (lv == 2);
	else
		return (lv == 1 || lv == 2);
}

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va)
{
	uint64_t table_va;
	uint64_t pxd_bits;
	uint64_t pxd_ptrs;
	int64_t start;
	int64_t lv;

	if (!pgd)
		return 0;

	if (pgd & pgt_pgd_align_mask)
		return 0;

	if (validate_virt_range(pgd, pgt_pgd_size))
		return 0;

	va = pgt_untag_user_va(va);

	if (va >> pgt_va_bits)
		return 0;

	table_va = pgd;
	pxd_bits = pgt_page_shift - 3;
	pxd_ptrs = 1ULL << pxd_bits;
	start = 4 - (int64_t)pgt_page_level;

	for (lv = start; lv < 4; lv++) {
		uint64_t pxd_shift;
		uint64_t pxd_index;
		uint64_t top_bits;
		uint64_t entry_va;
		uint64_t desc = 0;
		uint64_t type;

		uint64_t cur_table_size = (lv == start) ? pgt_pgd_size : pgt_page_size;
		if (validate_virt_range(table_va, cur_table_size))
			return 0;

		pxd_shift = (pgt_page_shift - 3) * (4 - lv) + 3;

		if (pxd_shift >= pgt_va_bits)
			return 0;

		pxd_index = (va >> pxd_shift) & (pxd_ptrs - 1);

		top_bits = pgt_va_bits - pxd_shift;

		if (top_bits > pxd_bits)
			top_bits = pxd_bits;

		if (top_bits == 0)
			return 0;

		if (pxd_index >= (1ULL << top_bits))
			return 0;

		entry_va = table_va + pxd_index * 8;

		if (hmkpm_copy_from_kernel_nofault(&desc, (const void *)entry_va, sizeof(desc)) != 0)
			return 0;

		type = desc & 3ULL;

		if (type == 0ULL || type == 2ULL)
			return 0;

		if (lv == 3) {
			uint64_t base;

			if (type != 3ULL)
				return 0;

			base = pgt_desc_to_phys(desc);

			if (base & (pgt_page_size - 1))
				return 0;

			if (validate_phys_range(base, pgt_page_size))
				return 0;

			return base | (va & (pgt_page_size - 1));
		}

		if (type == 1ULL) {
			uint64_t block_bits;
			uint64_t block_size;
			uint64_t block_mask;
			uint64_t base;

			if (!pgt_block_allowed((int)lv))
				return 0;

			block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;

			if (block_bits >= 64)
				return 0;

			block_size = 1ULL << block_bits;
			block_mask = block_size - 1;

			base = pgt_desc_to_phys(desc);

			if (base & block_mask)
				return 0;

			if (validate_phys_range(base, block_size))
				return 0;

			return (base & ~block_mask) | (va & block_mask);
		}

		uint64_t next_pa = pgt_desc_to_phys(desc);

		if (next_pa & (pgt_page_size - 1))
			return 0;

		if (validate_phys_range(next_pa, pgt_page_size))
			return 0;

		table_va = pgt_phys_to_virt(next_pa);
	}

	return 0;
}

static int pgt_pgtable_init(void)
{
	uint64_t tcr_el1;
	uint64_t t1sz;
	uint64_t va1_bits;
	uint64_t t0sz;
	uint64_t va0_bits;
	uint64_t tg0;
	uint64_t pxd_bits;
	int64_t start;

	asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));

	t1sz = (tcr_el1 >> 16) & 0x3F;
	va1_bits = 64 - t1sz;

	t0sz = tcr_el1 & 0x3F;
	va0_bits = 64 - t0sz;

	tg0 = (tcr_el1 >> 14) & 0x3ULL;

	if (va0_bits > 48 || va0_bits < 36) {
		hmkpm_error("Unsupported VA bits: %llu\n", va0_bits);
		return -EINVAL;
	}

	pgt_va_bits = va0_bits;
	pgt_user_limit = (1ULL << va0_bits) - 1;

	if (tg0 == 0) {
		pgt_page_shift = 12;
	} else if (tg0 == 2) {
		pgt_page_shift = 14;
	} else {
		hmkpm_error("Unsupported tg0: %llu\n", tg0);
		return -EINVAL;
	}

	pxd_bits = pgt_page_shift - 3;
	pgt_page_level = (va0_bits - 4) / pxd_bits;

	if (pgt_page_level != 2 && pgt_page_level != 3 && pgt_page_level != 4)
		return -EINVAL;

	start = 4 - (int64_t)pgt_page_level;

	if (start < 0 || start > 2)
		return -EINVAL;

	pgt_page_size = 1ULL << pgt_page_shift;

	int64_t root_lv = 4 - (int64_t)pgt_page_level;
	uint64_t root_shift = (pgt_page_shift - 3) * (4 - root_lv) + 3;

	if (pgt_va_bits > root_shift) {
		uint64_t root_bits = pgt_va_bits - root_shift;
		pgt_pgd_size = (1ULL << root_bits) * 8;
		if (pgt_pgd_size < pgt_page_size) {
			pgt_pgd_align_mask = pgt_pgd_size - 1;
		} else {
			pgt_pgd_size = pgt_page_size;
			pgt_pgd_align_mask = pgt_page_size - 1;
		}
	} else {
		pgt_pgd_size = pgt_page_size;
		pgt_pgd_align_mask = pgt_page_size - 1;
	}

	if (kver >= VERSION(5, 4, 0)) {
		pgt_pgd_size = pgt_page_size;
		pgt_pgd_align_mask = pgt_page_size - 1;
	}

	if (kver >= VERSION(5, 4, 0)) {
		pgt_page_offset = -(UL(1) << va1_bits);
	} else if (kver >= VERSION(4, 6, 0)) {
		pgt_page_offset = -(UL(1) << (va1_bits - 1));
	} else {
		pgt_page_offset = -(UL(1) << va1_bits);
	}

	hkvar_match(memstart_addr);
	if (!kv_memstart_addr) {
		hmkpm_error("Failed to resolve memstart_addr\n");
		return -EFAULT;
	}
	pgt_phys_offset = kvar_val(memstart_addr);
	pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

	bool prev_init_error = init_error;
	hkvar_match(high_memory);
	if (kv_high_memory) {
		pgt_high_memory = (uint64_t)kvar_val(high_memory);
	} else {
		pgt_high_memory = ~0ULL;
		init_error = prev_init_error;
	}
	pgt_phys_limit = pgt_virt_to_phys(pgt_high_memory);

	pgt_tbi0 = !!(tcr_el1 & (1ULL << 37));

	hmkpm_info("Page table config: va0_bits=%llu, shift=%llu, size=0x%llx, pgd_size=0x%llx, level=%llu, tbi0=%d\n",
		   va0_bits, pgt_page_shift, pgt_page_size, pgt_pgd_size, pgt_page_level, pgt_tbi0);
	hmkpm_info("phys_offset=0x%llx, page_offset=0x%llx, linear_voffset=0x%llx, high_mem=0x%llx, pgd_align_mask=0x%llx\n",
		   pgt_phys_offset, pgt_page_offset, pgt_linear_voffset, pgt_high_memory, pgt_pgd_align_mask);

	return 0;
}

static inline int hmkpm_user_range_ok(const void __user *ptr, uint64_t len)
{
	uint64_t u;

	if (!ptr || len == 0)
		return 0;

	u = pgt_untag_user_va((uint64_t)ptr);

	if (u > pgt_user_limit)
		return 0;

	if (len - 1 > pgt_user_limit - u)
		return 0;

	return 1;
}

static __always_inline bool is_hmkpm_magic(uint64_t magic)
{
	return magic >= HMKPM_MAGIC && magic <= HMKPM_MAGIC_MAX;
}

#ifndef min
#define min(a, b) ((a) < (b) ? (a) : (b))
#endif

#define HMKPM_BOUNCE_SIZE 512U

static inline void hmkpm_fast_copy(void *dst, const void *src, size_t n)
{
	uint8_t *d = (uint8_t *)dst;
	const uint8_t *s = (const uint8_t *)src;

	while (n >= 8 && !(((uintptr_t)d | (uintptr_t)s) & 7)) {
		*(uint64_t *)d = *(const uint64_t *)s;
		d += 8;
		s += 8;
		n -= 8;
	}
	while (n >= 4 && !(((uintptr_t)d | (uintptr_t)s) & 3)) {
		*(uint32_t *)d = *(const uint32_t *)s;
		d += 4;
		s += 4;
		n -= 4;
	}
	while (n > 0) {
		*d++ = *s++;
		n--;
	}
}

static ssize_t pgt_read_mm(struct mm_struct *mm, uint64_t remote_va, size_t len,
			   void __user *local_buf)
{
	ssize_t total = 0;
	uint64_t pgd = 0;
	uint8_t bounce[HMKPM_BOUNCE_SIZE];

	if (!mm)
		return -ESRCH;

	if (mm_struct_offset.pgd_offset < 0)
		return -EINVAL;

	if (hmkpm_copy_from_kernel_nofault(&pgd,
					   (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset),
					   sizeof(pgd)) != 0 || !pgd)
		return -EFAULT;

	while (len > 0) {
		unsigned long page_off = remote_va & (pgt_page_size - 1);
		size_t page_left = (size_t)(pgt_page_size - page_off);
		size_t chunk = min(len, page_left);
		chunk = min(chunk, (size_t)HMKPM_BOUNCE_SIZE);

		uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va);
		if (!tkpa) {
			if (total > 0)
				break;
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

static ssize_t pgt_read(pid_t pid, uint64_t remote_va, size_t len,
			void __user *local_buf)
{
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;
	ssize_t ret;

	if (pid <= 0)
		return -EINVAL;

	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)(pid);
	if (!task) {
		kfunc(__rcu_read_unlock)();
		return -ESRCH;
	}

	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();

	if (!mm)
		return -ESRCH;

	ret = pgt_read_mm(mm, remote_va, len, local_buf);

	kfunc(mmput)(mm);
	return ret;
}

static void hmkpm_handle_single(hook_fargs3_t *args, void __user *user_ptr, uint64_t total_len)
{
	struct hmkpm_req req;
	void __user *data_ptr;
	ssize_t ret;

	if (total_len < HMKPM_REQ_SIZE) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	if (hmkpm_copy_from_user(&req, user_ptr, HMKPM_REQ_SIZE) != 0) {
		args->ret = (uint64_t)(long)-EFAULT;
		return;
	}

	if (req.size == 0) {
		if (total_len != HMKPM_REQ_SIZE)
			args->ret = (uint64_t)(long)-EINVAL;
		else
			args->ret = 0;
		return;
	}

	if ((uint64_t)req.size > HMKPM_MAX_SINGLE_SIZE) {
		args->ret = (uint64_t)(long)-E2BIG;
		return;
	}

	if (total_len != HMKPM_REQ_SIZE + (uint64_t)req.size) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	if (req.pid <= 0) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	req.addr = pgt_untag_user_va(req.addr);

	if (req.addr > U64_MAX - (uint64_t)req.size) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	data_ptr = (void __user *)((uint8_t __user *)user_ptr + HMKPM_REQ_SIZE);

	ret = pgt_read((pid_t)req.pid, req.addr, req.size, data_ptr);
	if (ret < 0) {
		args->ret = (uint64_t)(long)ret;
	} else if ((uint64_t)ret != req.size) {
		args->ret = (uint64_t)(long)-EFAULT;
	} else {
		args->ret = 0;
	}
}

static void hmkpm_handle_batch(hook_fargs3_t *args, void __user *user_ptr, uint64_t total_len)
{
	struct hmkpm_batch_hdr hdr;
	struct hmkpm_batch_entry chunk[HMKPM_BATCH_CHUNK_ENTRIES];
	uint64_t entries_bytes;
	uint64_t entries_end;
	uint64_t data_start;
	uint64_t io_end;
	uint64_t data_off = 0;
	uint32_t done = 0;
	int rc = 0;
	struct task_struct *task = NULL;
	struct mm_struct *mm = NULL;

	if (total_len < HMKPM_BATCH_HDR_SIZE) {
		rc = -EINVAL;
		goto out;
	}

	if (hmkpm_copy_from_user(&hdr, user_ptr, HMKPM_BATCH_HDR_SIZE) != 0) {
		rc = -EFAULT;
		goto out;
	}

	if (hdr.count == 0) {
		if (hdr.data_total != 0) {
			rc = -EINVAL;
			goto out;
		}
		if (total_len < HMKPM_BATCH_HDR_SIZE)
			rc = -EINVAL;
		goto out;
	}

	if (hdr.count > HMKPM_MAX_BATCH_ENTRIES) {
		rc = -E2BIG;
		goto out;
	}

	if (hdr.data_total > HMKPM_MAX_BATCH_TOTAL_SIZE) {
		rc = -E2BIG;
		goto out;
	}

	if (hdr.pid <= 0) {
		rc = -EINVAL;
		goto out;
	}

	entries_bytes = (uint64_t)hdr.count * HMKPM_BATCH_ENTRY_SIZE;

	if (entries_bytes > U64_MAX - HMKPM_BATCH_HDR_SIZE) {
		rc = -E2BIG;
		goto out;
	}

	entries_end = HMKPM_BATCH_HDR_SIZE + entries_bytes;

	if (hdr.data_total > U64_MAX - entries_end) {
		rc = -E2BIG;
		goto out;
	}

	io_end = entries_end + hdr.data_total;

	if (total_len < io_end) {
		rc = -ERANGE;
		goto out;
	}

	kfunc(__rcu_read_lock)();
	task = kfunc(find_task_by_vpid)((pid_t)hdr.pid);
	if (!task) {
		kfunc(__rcu_read_unlock)();
		rc = -ESRCH;
		goto out;
	}
	mm = kfunc(get_task_mm)(task);
	kfunc(__rcu_read_unlock)();

	if (!mm) {
		rc = -ESRCH;
		goto out;
	}

	data_start = entries_end;

	while (done < hdr.count) {
		uint32_t chunk_count = hdr.count - done;
		uint64_t chunk_bytes;
		void __user *entry_src;
		uint32_t i;

		if (chunk_count > HMKPM_BATCH_CHUNK_ENTRIES)
			chunk_count = HMKPM_BATCH_CHUNK_ENTRIES;

		chunk_bytes = (uint64_t)chunk_count * HMKPM_BATCH_ENTRY_SIZE;

		entry_src = (void __user *)((uint8_t __user *)user_ptr +
					    HMKPM_BATCH_HDR_SIZE +
					    (uint64_t)done * HMKPM_BATCH_ENTRY_SIZE);

		if (hmkpm_copy_from_user((void *)chunk, entry_src, chunk_bytes) != 0) {
			rc = -EFAULT;
			goto out_mm;
		}

		for (i = 0; i < chunk_count; ++i) {
			struct hmkpm_batch_entry *e = &chunk[i];
			uint64_t req_size = e->size;
			void __user *data_ptr;
			ssize_t ret;

			if (req_size == 0)
				continue;

			if (req_size > HMKPM_MAX_ENTRY_SIZE) {
				rc = -E2BIG;
				goto out_mm;
			}

			if (req_size > hdr.data_total - data_off) {
				rc = -EINVAL;
				goto out_mm;
			}

			e->addr = pgt_untag_user_va(e->addr);

			if (e->addr > U64_MAX - req_size) {
				e->size = 0;
				data_off += req_size;
				continue;
			}

			data_ptr = (void __user *)((uint8_t __user *)user_ptr + data_start + data_off);

			ret = pgt_read_mm(mm, e->addr, req_size, data_ptr);
			if (ret < 0 || (uint64_t)ret < req_size) {
				e->size = 0;
			} else {
				e->size = req_size;
			}

			data_off += req_size;
		}

		if (hmkpm_copy_to_user(entry_src, chunk, chunk_bytes) != 0) {
			rc = -EFAULT;
			goto out_mm;
		}

		done += chunk_count;
	}

	if (unlikely(data_off != hdr.data_total)) {
		rc = -EINVAL;
		goto out_mm;
	}

out_mm:
	if (mm)
		kfunc(mmput)(mm);

out:
	args->ret = (uint64_t)(long)rc;
}

static void hmkpm_handle(hook_fargs3_t *args, void *udata)
{
	void __user *user_ptr;
	uint64_t total_len;
	uint64_t magic = syscall_argn(args, 0);
	uid_t uid;

	if (likely(!is_hmkpm_magic(magic)))
		return;

	if (!READ_ONCE(hook_active))
		return;

	uid = current_uid();
	if (uid != 0)
		return;

	args->skip_origin = 1;

	if (magic == HMKPM_MAGIC) {
		user_ptr = (void __user *)syscall_argn(args, 1);
		total_len = syscall_argn(args, 2);

		if (user_ptr && total_len > 0) {
			if (hmkpm_user_range_ok(user_ptr, total_len)) {
				struct hmkpm_version_info info;
				memset(&info, 0, sizeof(info)); // 使用本地 memset 避免符号解析问题
				info.magic = HMKPM_MAGIC;
				info.version_code = HMKPM_VERSION_CODE;
				info.version_major = HMKPM_VERSION_MAJOR;
				info.version_minor = HMKPM_VERSION_MINOR;
				info.version_patch = HMKPM_VERSION_PATCH;
				info.is_lockless = 1;
				info._pad = 0;
				info.mmap_lock_offset = -1;
				info.features = HMKPM_ALL_FEATURES;

				const char *vstr = HMKPM_VERSION_STR;
				size_t vlen = 0;
				while (vstr[vlen] && vlen < sizeof(info.version_str) - 1) {
					info.version_str[vlen] = vstr[vlen];
					vlen++;
				}
				info.version_str[vlen] = '\0';

				int copy_rc = 0;
				if (total_len >= sizeof(struct hmkpm_version_info)) {
					copy_rc = hmkpm_copy_to_user(user_ptr, &info, sizeof(info));
				} else if (total_len >= sizeof(uint32_t)) {
					copy_rc = hmkpm_copy_to_user(user_ptr, &info.version_code, sizeof(uint32_t));
				}

				if (copy_rc != 0) {
					args->ret = (uint64_t)(long)-EFAULT;
					return;
				}
			}
		}

		args->ret = (((uint64_t)HMKPM_VERSION_CODE << 40) | (HMKPM_MAGIC & 0xFFFFFFFFFFULL));
		return;
	}

	user_ptr = (void __user *)syscall_argn(args, 1);
	total_len = syscall_argn(args, 2);

	if (total_len == 0) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	if (unlikely(!hmkpm_user_range_ok(user_ptr, total_len))) {
		args->ret = (uint64_t)(long)-EINVAL;
		return;
	}

	if (magic == HMKPM_MAGIC_READ) {
		hmkpm_handle_single(args, user_ptr, total_len);
		return;
	}

	if (magic == HMKPM_MAGIC_READ_BATCH) {
		hmkpm_handle_batch(args, user_ptr, total_len);
		return;
	}

	args->ret = (uint64_t)(long)-EINVAL;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
	hook_err_t err;

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
		"__memset",
		"memset",
		"__pi___memset",
		"__pi_memset",
		"__asan_memset",
		"__hwasan_memset",
		"__mte_memset",
		"__arch_memset",
		NULL
	};

	for (int i = 0; arm64_memset_aliases[i] != NULL; i++) {
		kf_memset = (typeof(kf_memset))hmkpm_lookup_symbol(arm64_memset_aliases[i]);
		if (kf_memset) {
			hmkpm_info("Resolved memset via symbol: %s\n", arm64_memset_aliases[i]);
			break;
		}
	}

	// 容错处理：如果找不到也没关系，我们用本地的
	if (!kf_memset) {
		hmkpm_warn("Kernel memset symbol not found, using local inline fallback\n");
	}

	kf___arch_copy_to_user =
		(typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__arch_copy_to_user");
	if (!kf___arch_copy_to_user)
		kf___arch_copy_to_user =
			(typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__copy_to_user");

	if (!kf___arch_copy_to_user) {
		hmkpm_error("Failed to find kfunc __arch_copy_to_user / __copy_to_user\n");
		init_error = true;
	}

	kf___arch_copy_from_user =
		(typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__arch_copy_from_user");
	if (!kf___arch_copy_from_user)
		kf___arch_copy_from_user =
			(typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__copy_from_user");

	if (!kf___arch_copy_from_user) {
		hmkpm_error("Failed to find kfunc __arch_copy_from_user / __copy_from_user\n");
		init_error = true;
	}

	hkfunc_match(find_task_by_vpid);
	hkfunc_match(get_task_mm);
	hkfunc_match(mmput);
	hkfunc_match(__rcu_read_lock);
	hkfunc_match(__rcu_read_unlock);

	kf_copy_from_kernel_nofault =
		(typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
	if (!kf_copy_from_kernel_nofault) {
		hmkpm_info("Failed to find kfunc copy_from_kernel_nofault, using probe_kernel_read instead\n");
		kf_probe_kernel_read = (typeof(kf_probe_kernel_read))hmkpm_lookup_symbol("probe_kernel_read");
		if (!kf_probe_kernel_read) {
			hmkpm_error("Failed to find kfunc probe_kernel_read either!\n");
			init_error = true;
		}
	}

	if (init_error) {
		hmkpm_error("Symbol resolution failed, aborting...\n");
		return -ENOENT;
	}

	if (kver >= VERSION(5, 10, 0)) {
		fsnotify_addr = hmkpm_lookup_symbol("fsnotify");
		if (fsnotify_addr) {
			err = hook_wrap7((void *)fsnotify_addr, before_fsnotify, 0, 0);
			if (err) {
				hmkpm_error("hook installation of fsnotify failed: %d\n", err);
				fsnotify_hooked = false;
			} else {
				fsnotify_hooked = true;
			}
		} else {
			hmkpm_info("fsnotify_addr not found, skipping fsnotify hook\n");
		}
	}

	err = hook_syscalln(__NR_getresuid, 3, (void *)hmkpm_handle, 0, 0);
	if (err) {
		hmkpm_error("install hook error: %d\n", err);
		if (fsnotify_hooked && fsnotify_addr) {
			hook_unwrap((void *)fsnotify_addr, before_fsnotify, 0);
			fsnotify_hooked = false;
		}
		return -ENOENT;
	}

	hmkpm_info("module loaded successfully (read-only)\n");
	return 0;
}

/* Userspace response utilities */
static inline int kpm_isspace(char c)
{
	return (c == ' ' || c == '\t' || c == '\n' || c == '\r');
}

static const char *kpm_skip_spaces(const char *s)
{
	if (!s)
		return "";
	while (*s && kpm_isspace(*s))
		s++;
	return s;
}

static bool kpm_streq(const char *s1, const char *s2)
{
	if (!s1 || !s2)
		return false;
	while (*s1 && *s2) {
		if (*s1 != *s2)
			return false;
		s1++;
		s2++;
	}
	while (*s1 && kpm_isspace(*s1))
		s1++;
	return (*s1 == '\0' && *s2 == '\0');
}

static void send_user_msg(char __user *out_msg, int outlen, const char *msg)
{
	int len = 0;
	char zero = '\0';

	if (!out_msg || outlen <= 0 || !msg)
		return;

	while (msg[len] && len < outlen - 1)
		len++;

	if (len > 0)
		compat_copy_to_user(out_msg, msg, len);

	compat_copy_to_user((char __user *)out_msg + len, &zero, 1);
}

static long module_control_handler(const char *args, char __user *out_msg, int outlen)
{
	const char *cmd = kpm_skip_spaces(args);
	long ret = 0;

	if (kpm_streq(cmd, "enable") || kpm_streq(cmd, "on") ||
	    kpm_streq(cmd, "start") || kpm_streq(cmd, "1")) {
		WRITE_ONCE(hook_active, true);
		send_user_msg(out_msg, outlen, "enabled\n");
	} else if (kpm_streq(cmd, "disable") || kpm_streq(cmd, "off") ||
		   kpm_streq(cmd, "stop") || kpm_streq(cmd, "0")) {
		WRITE_ONCE(hook_active, false);
		send_user_msg(out_msg, outlen, "disabled\n");
	} else if (kpm_streq(cmd, "status") || kpm_streq(cmd, "state") ||
		   kpm_streq(cmd, "get")) {
		if (READ_ONCE(hook_active))
			send_user_msg(out_msg, outlen, "active\n");
		else
			send_user_msg(out_msg, outlen, "inactive\n");
	} else if (kpm_streq(cmd, "toggle")) {
		if (READ_ONCE(hook_active)) {
			WRITE_ONCE(hook_active, false);
			send_user_msg(out_msg, outlen, "toggled to disabled\n");
		} else {
			WRITE_ONCE(hook_active, true);
			send_user_msg(out_msg, outlen, "toggled to enabled\n");
		}
	} else {
		hmkpm_info("unknown control command: '%s'\n", cmd ? cmd : "(null)");
		send_user_msg(out_msg, outlen,
			      "unknown command. Available: enable | disable | status | toggle\n");
		ret = -EINVAL;
	}

	return ret;
}

static long module_cleanup_handler(void *__user reserved)
{
	if (fsnotify_hooked && fsnotify_addr) {
		hook_unwrap((void *)fsnotify_addr, before_fsnotify, 0);
		fsnotify_hooked = false;
	}
	unhook_syscalln(__NR_getresuid, (void *)hmkpm_handle, 0);
	hmkpm_info("module cleaned up\n");
	return 0;
}

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
