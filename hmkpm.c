// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
 *
 * KernelPatch Module (KPM) - [HMKPM]
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
#define HMKPM_VERSION_MINOR	8
#define HMKPM_VERSION_PATCH	0
#define HMKPM_VERSION_CODE	(((uint32_t)HMKPM_VERSION_MAJOR << 16) | \
				 ((uint32_t)HMKPM_VERSION_MINOR << 8) | \
				 ((uint32_t)HMKPM_VERSION_PATCH))
#define HMKPM_VERSION_STR	"2.8.0"

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

// gki 5.10 to 6.12 same offset
#define SUPER_BLOCK_OFF 40
#define MAGIC_OFF 96

struct rw_semaphore;

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

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write)
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

			if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51)))
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

			if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51)))
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

		if (is_write && (desc & (1ULL << 62)))
			return 0;

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

#define min(a, b) ((a) < (b) ? (a) : (b))

static inline bool hmkpm_is_lockless(void)
{
	return (mmap_lock_sem_offset < 0);
}

static inline void hmkpm_mmap_read_lock(struct mm_struct *mm)
{
	if (mm && !hmkpm_is_lockless() && kf_down_read) {
		struct rw_semaphore *sem =
			(struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset);
		kfunc(down_read)(sem);
	}
}

static inline void hmkpm_mmap_read_unlock(struct mm_struct *mm)
{
	if (mm && !hmkpm_is_lockless() && kf_up_read) {
		struct rw_semaphore *sem =
			(struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset);
		kfunc(up_read)(sem);
	}
}

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

static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len,
			 void __user *local_buf, bool is_write)
{
	ssize_t total = 0;
	uint64_t pgd = 0;
	uint8_t bounce[512];

	if (!mm)
		return -ESRCH;

	if (mm_struct_offset.pgd_offset < 0)
		return -EINVAL;

	if (is_write && hmkpm_is_lockless())
		return -EOPNOTSUPP;

	if (hmkpm_copy_from_kernel_nofault(&pgd,
					   (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset),
					   sizeof(pgd)) != 0 || !pgd)
		return -EFAULT;

	while (len > 0) {
		unsigned long page_off = remote_va & (pgt_page_size - 1);
		size_t page_left = (size_t)(pgt_page_size - page_off);
		size_t chunk = min(len, page_left);
		chunk = min(chunk, (size_t)512);

		if (is_write) {
			unsigned long not_copied = hmkpm_copy_from_user(bounce, local_buf, chunk);
			if (not_copied) {
				if (not_copied == chunk) {
					if (total > 0)
						break;
					return -EFAULT;
				}
				chunk -= not_copied;
			}
		}

		hmkpm_mmap_read_lock(mm);

		uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va, is_write);
		if (!tkpa) {
			hmkpm_mmap_read_unlock(mm);
			if (total > 0)
				break;
			return -EFAULT;
		}

		void *tkva = (void *)pgt_phys_to_virt(tkpa);

		if (is_write) {
			hmkpm_fast_copy(tkva, bounce, chunk);
		} else {
			hmkpm_fast_copy(bounce, tkva, chunk);
		}

		hmkpm_mmap_read_unlock(mm);

		if (!is_write) {
			unsigned long not_copied = hmkpm_copy_to_user(local_buf, bounce, chunk);
			if (not_copied) {
				size_t copied = chunk - not_copied;
				total += (ssize_t)copied;
				break;
			}
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

	ret = pgt_rw_mm(mm, remote_va, len, local_buf, is_write);

	kfunc(mmput)(mm);
	return ret;
}

// ==========================================
// Netlink 通信层
// ==========================================
struct sock;
struct sk_buff;
struct nlmsghdr { uint32_t nlmsg_len; uint16_t nlmsg_type; uint16_t nlmsg_flags; uint32_t nlmsg_seq; uint32_t nlmsg_pid; };
#define NLMSG_HDRLEN ((int)((sizeof(struct nlmsghdr)+3)&~3))
#define NLMSG_LENGTH(len) ((len) + NLMSG_HDRLEN)
#define NLMSG_SPACE(len) (((NLMSG_LENGTH(len))+3)&~3)
#define NLMSG_DATA(nlh) ((void*)(((char*)nlh) + NLMSG_LENGTH(0)))

struct netlink_kernel_cfg { unsigned int groups; void (*input)(struct sk_buff *skb); void *cb_mutex; void *bind; void *unbind; };
static struct sock *(*kf_netlink_create)(void *net, int unit, void *module, struct netlink_kernel_cfg *cfg);
static int (*kf_netlink_unicast)(struct sock *ssk, struct sk_buff *skb, uint32_t portid, int nonblock);
static void *(*kf_alloc_skb)(unsigned int size, int gfp_mask);
static void *(*kf_skb_put)(struct sk_buff *skb, unsigned int len);
static void *kv_init_net = NULL;
static struct sock *g_nl_sk = NULL;

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
    if (!skb) return;
    char *skb_data = NULL;
    if (hmkpm_copy_from_kernel_nofault(&skb_data, (char*)skb + 0xD8, 8) != 0 || !skb_data) return;

    struct nlmsghdr *nlh = (struct nlmsghdr *)skb_data;
    if (nlh->nlmsg_len < sizeof(struct hmkpm_nl_req)) return;

    struct hmkpm_nl_req *req = (struct hmkpm_nl_req *)NLMSG_DATA(nlh);
    uint32_t user_pid = nlh->nlmsg_pid;
    uint64_t result = 0;

    if (nlh->nlmsg_type == HMKPM_NL_CMD_READ) {
        if (req->pid > 0) {
            uintptr_t clean_buf = (uintptr_t)req->user_buf & 0x00FFFFFFFFFFFFFFULL;
            ssize_t r = pgt_rw((pid_t)req->pid, req->addr, req->size, (void __user *)clean_buf, false);
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
                // 读 PID 偏移
                uint64_t arg_start = 0;
                hmkpm_copy_from_kernel_nofault(&arg_start, (const void *)((uintptr_t)mm + 0x130), 8);
                
                if (arg_start) {
                    char kbuf[128] = {0};
                    if (pgt_rw(i, arg_start, 127, (void __user *)kbuf, false) > 0) {
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
            // 读基址偏移
            uintptr_t vma = 0;
            hmkpm_copy_from_kernel_nofault(&vma, (const void *)((uintptr_t)mm + 0x00), 8);
            
            while (vma) {
                uintptr_t file = 0;
                hmkpm_copy_from_kernel_nofault(&file, (const void *)(vma + 0xA0), 8);
                
                if (file) {
                    uintptr_t dentry = 0;
                    hmkpm_copy_from_kernel_nofault(&dentry, (const void *)(file + 0x20), 8);
                    
                    if (dentry) {
                        char iname[32] = {0};
                        hmkpm_copy_from_kernel_nofault(iname, (const void *)(dentry + 0x38), 31);
                        
                        if (hmkpm_strstr(iname, req->mod_name)) { 
                            hmkpm_copy_from_kernel_nofault(&result, (const void *)(vma + 0x00), 8);
                            break; 
                        }
                    }
                }
                uintptr_t next_vma = 0;
                hmkpm_copy_from_kernel_nofault(&next_vma, (const void *)(vma + 0x08), 8);
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
}

static int netlink_init(void) {
    kf_netlink_create = (void*)hmkpm_lookup_symbol("__netlink_kernel_create");
    kf_netlink_unicast = (void*)hmkpm_lookup_symbol("netlink_unicast");
    kf_alloc_skb = (void*)hmkpm_lookup_symbol("__alloc_skb");
    kf_skb_put = (void*)hmkpm_lookup_symbol("skb_put");
    kv_init_net = (void*)hmkpm_lookup_symbol("init_net");

    if (!kf_netlink_create || !kf_netlink_unicast || !kf_alloc_skb || !kf_skb_put || !kv_init_net) {
        hmkpm_error("Netlink symbols missing\n"); return -1;
    }
    struct netlink_kernel_cfg cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.input = netlink_recv;

    g_nl_sk = kf_netlink_create(kv_init_net, 31, NULL, &cfg);
    if (!g_nl_sk) return -1;
    hmkpm_info("Netlink registered on 31 (Lockless)\n");
    return 0;
}

/* ========================================================================
 * Dynamic ARM64 Disassembly & mmap_sem Probe Scanner
 * ======================================================================== */

static inline unsigned int a64_insn_rd(u32 insn) { return insn & 0x1f; }
static inline unsigned int a64_insn_rn(u32 insn) { return (insn >> 5) & 0x1f; }
static inline unsigned int a64_insn_rm(u32 insn) { return (insn >> 16) & 0x1f; }
static inline bool insn_is_prologue_hint(u32 insn) { return (insn & 0xfffff000) == 0xd5032000; }

static bool insn_is_bl_or_b(unsigned long pc, u32 insn, unsigned long *target)
{
	u32 op = insn & 0xfc000000;
	s32 imm26;
	s64 delta;

	if (op != 0x94000000 && op != 0x14000000)
		return false;

	imm26 = (s32)(insn & 0x03ffffff);
	if (imm26 & 0x02000000)
		imm26 |= 0xfc000000;

	delta = (s64)imm26 * 4;
	*target = (unsigned long)((s64)pc + delta);

	return true;
}

static unsigned long resolve_branch_target(unsigned long target)
{
	unsigned long resolved = target;
	int hops = 0;

	while (resolved && hops++ < 4) {
		unsigned long cursor = resolved;
		bool found_b = false;
		int skip;

		for (skip = 0; skip < 3; skip++, cursor += 4) {
			u32 insn;
			unsigned long next;

			if (hmkpm_copy_from_kernel_nofault(&insn, (const void *)cursor, sizeof(insn)) != 0)
				break;

			if (insn_is_prologue_hint(insn))
				continue;

			if ((insn & 0xfc000000) == 0x14000000 && insn_is_bl_or_b(cursor, insn, &next)) {
				resolved = next;
				found_b = true;
			}
			break;
		}
		if (!found_b) break;
	}
	return resolved;
}

static inline bool is_ret_insn(u32 insn) { return (insn & 0xfffffc1f) == 0xd65f0000; }

static bool insn_is_function_exit(u32 insn)
{
	if (is_ret_insn(insn)) return true;
	if (insn == 0xd69f03e0) return true;
	if ((insn & 0xfffffc1f) == 0xd61f0000) return true;
	return false;
}

static bool insn_is_atomic_rwsem_op(u32 insn, unsigned int *rn)
{
    unsigned int r;
    if ((insn & 0xffa07c00) == 0xc8a07c00) {
        r = a64_insn_rn(insn);
        if (r == 31) return false;
        *rn = r;
        return true;
    }
    switch (insn & 0xff20fc00) {
    case 0xf8200000: case 0xf8201000: case 0xf8202000: case 0xf8203000: case 0xf8208000:
        r = a64_insn_rn(insn);
        if (r == 31) return false;
        *rn = r;
        return true;
    }
    if ((insn & 0xfffffc00) == 0xc85f7c00 || (insn & 0xfffffc00) == 0xc85ffc00) {
        r = a64_insn_rn(insn);
        if (r == 31) return false;
        *rn = r;
        return true;
    }
    if ((insn & 0xffe0fc00) == 0xc8007c00 || (insn & 0xffe0fc00) == 0xc800fc00) {
        r = a64_insn_rn(insn);
        if (r == 31) return false;
        *rn = r;
        return true;
    }
    return false;
}

static bool insn_add_imm(u32 insn, unsigned int *rd, unsigned int *rn, unsigned long *imm)
{
	u32 op = insn & 0xff800000;
	if (op != 0x91000000 && op != 0xb1000000) return false;
	*rd = a64_insn_rd(insn);
	*rn = a64_insn_rn(insn);
	*imm = (insn >> 10) & 0xfff;
	if ((insn >> 22) & 1) *imm <<= 12;
	return true;
}

static bool insn_is_mov_reg(u32 insn, unsigned int *rd, unsigned int *rm, bool *is64)
{
	if ((insn & 0xffe0ffe0) == 0xaa0003e0) { *rd = a64_insn_rd(insn); *rm = a64_insn_rm(insn); *is64 = true; return true; }
	if ((insn & 0xfffffc00) == 0xaa1f0000) { *rd = a64_insn_rd(insn); *rm = a64_insn_rn(insn); *is64 = true; return true; }
	if ((insn & 0xffe0ffe0) == 0x2a0003e0) { *rd = a64_insn_rd(insn); *rm = a64_insn_rm(insn); *is64 = false; return true; }
	if ((insn & 0xfffffc00) == 0x2a1f0000) { *rd = a64_insn_rd(insn); *rm = a64_insn_rn(insn); *is64 = false; return true; }
	if ((insn & 0xfffffc00) == 0x91000000) { *rd = a64_insn_rd(insn); *rm = a64_insn_rn(insn); *is64 = true; return true; }
	if ((insn & 0xfffffc00) == 0x11000000) { *rd = a64_insn_rd(insn); *rm = a64_insn_rn(insn); *is64 = false; return true; }
	return false;
}

static bool insn_is_add_reg(u32 insn, unsigned int *rd, unsigned int *rn, unsigned int *rm, bool *extended, unsigned int *shift)
{
	if ((insn & 0xffe00000) == 0x8b000000 || (insn & 0xffe00000) == 0xab000000) {
		*rd = a64_insn_rd(insn); *rn = a64_insn_rn(insn); *rm = a64_insn_rm(insn); *extended = false; *shift = (insn >> 10) & 0x3f; return true;
	}
	if ((insn & 0xffe00000) == 0x8b200000 || (insn & 0xffe00000) == 0xab200000) {
		*rd = a64_insn_rd(insn); *rn = a64_insn_rn(insn); *rm = a64_insn_rm(insn); *extended = true; *shift = (insn >> 10) & 0x7; return true;
	}
	return false;
}

enum need_kind { NEED_ADDR, NEED_CONST };
enum wide_imm_op { WIDE_MOVZ, WIDE_MOVK, WIDE_MOVN };

static bool insn_wide_imm(u32 insn, unsigned int *rd, unsigned int *hw, unsigned long *imm16, enum wide_imm_op *type)
{
	switch (insn & 0xff800000) {
	case 0xd2800000: *type = WIDE_MOVZ; break;
	case 0x52800000: *type = WIDE_MOVZ; break;
	case 0xf2800000: *type = WIDE_MOVK; break;
	case 0x72800000: *type = WIDE_MOVK; break;
	case 0x92800000: *type = WIDE_MOVN; break;
	case 0x12800000: *type = WIDE_MOVN; break;
	default: return false;
	}
	*rd = a64_insn_rd(insn); *hw = (insn >> 21) & 0x3; *imm16 = (insn >> 5) & 0xffff;
	return true;
}

#define MAX_PROBE_FUNCS           32
#define MAX_PROBE_VOTES           64
#define MAX_SCAN_INSNS            4096UL
#define BACK_SCAN_MAX             32
#define OFFSET_MIN                8U
#define OFFSET_MAX                4096U

struct offset_vote { u32 offset; u32 count; u32 func_mask; };
static struct offset_vote probe_votes[MAX_PROBE_VOTES];
static int nr_probe_votes;

static const char *const probe_func_names[] = {
	"vm_munmap", "__vm_munmap", "vm_brk_flags", "do_brk_flags", "exit_mmap", "vm_mmap_pgoff", "do_munmap", "__do_munmap",
	"ksys_mmap_pgoff", "vm_mmap", "apply_mlockall_flags", "setup_arg_pages", "sys_munmap", "do_mmap", "mmap_region", "dup_mmap",
	"copy_process", "sys_mmap_pgoff", "use_mm", "unuse_mm", "__vma_link_rb", "vma_adjust", "find_vma", "mmput",
};
#define NR_PROBE_FUNCS (sizeof(probe_func_names) / sizeof(probe_func_names[0]))

static const char *const lock_symbol_names[] = {
	"down_read", "_down_read", "__down_read", "down_write", "_down_write", "__down_write", "up_read", "_up_read", "__up_read", "up_write", "_up_write", "__up_write",
	"down_read_killable", "down_write_killable", "down_read_trylock", "_down_read_trylock", "__down_read_trylock", "down_write_trylock",
	"rwsem_down_read", "rwsem_down_write", "rwsem_down_read_failed", "__rwsem_down_read_failed", "rwsem_down_write_failed", "__rwsem_down_write_failed",
	"rwsem_down_write_failed_killable", "__rwsem_down_write_failed_killable", "rwsem_down_read_slow", "rwsem_down_write_slow",
	"__rwsem_down_read_slowpath", "__rwsem_down_write_slowpath", "rwsem_optimistic_spin", "rwsem_spin_on_owner", "rwsem_wake", "__rwsem_wake",
	"__rwsem_up_read_failed", "rwsem_up_read", "rwsem_up_write",
};
#define NR_PROBE_LOCKS (sizeof(lock_symbol_names) / sizeof(lock_symbol_names[0]))

_Static_assert(NR_PROBE_FUNCS <= MAX_PROBE_FUNCS, "MAX_PROBE_FUNCS must be greater than or equal to NR_PROBE_FUNCS");

static inline bool offset_is_valid(unsigned long imm) { return imm >= OFFSET_MIN && imm <= OFFSET_MAX && (imm & 7) == 0; }
static inline bool reg_is_likely_base(unsigned int r) { return r == 29 || (r >= 19 && r <= 28); }

static int choose_add_register_source(unsigned int rn, unsigned int rm, bool extended)
{
	if (rn == 31 && rm == 31) return -1;
	if (extended) return (rm != 31) ? (int)rm : (int)rn;
	if (rm == 31) return (int)rn;
	if (rn == 31) return (int)rm;
	if (reg_is_likely_base(rn) && !reg_is_likely_base(rm)) return (int)rm;
	if (reg_is_likely_base(rm) && !reg_is_likely_base(rn)) return (int)rn;
	return (int)rm;
}

static bool insn_may_write_reg(u32 insn, unsigned int reg)
{
	unsigned int rd = a64_insn_rd(insn);
	if (reg == 31 || rd != reg) return false;
	if ((insn & 0xff000010) == 0x54000000 || (insn & 0x7e000000) == 0x34000000 || (insn & 0x7e000000) == 0x36000000 || (insn & 0xfc000000) == 0x14000000) return false;
	if ((insn & 0xbfc00000) == 0xb9000000) return false;
	if ((insn & 0xffc00000) == 0x39000000 || (insn & 0xffc00000) == 0x79000000) return false;
	if ((insn & 0x3e400000) == 0x28000000) return false;
	if ((insn & 0x0e000000) == 0x0a000000) { if ((insn & 0x00400000) == 0) return false; return true; }
	if (insn_is_prologue_hint(insn)) return false;
	return true;
}

static void add_probe_vote(unsigned int offset, int func_idx)
{
	int i;
	if (!offset_is_valid(offset) || func_idx < 0 || func_idx >= MAX_PROBE_FUNCS) return;
	for (i = 0; i < nr_probe_votes; i++) {
		if (probe_votes[i].offset == offset) {
			probe_votes[i].count++;
			probe_votes[i].func_mask |= (u32)(1U << func_idx);
			return;
		}
	}
	if (nr_probe_votes < MAX_PROBE_VOTES) {
		probe_votes[nr_probe_votes].offset = offset;
		probe_votes[nr_probe_votes].count = 1;
		probe_votes[nr_probe_votes].func_mask = (u32)(1U << func_idx);
		nr_probe_votes++;
	}
}

static int find_offset_before_pc_reg(unsigned long start_pc, unsigned int start_reg, unsigned int *offset)
{
	int i;
	int need_reg = (int)start_reg;
	enum need_kind need_kind = NEED_ADDR;
	unsigned int need_shift = 0;
	bool have_partial = false;
	u64 partial_val = 0;
	u64 partial_mask = 0;

	if (need_reg < 0 || need_reg >= 31) return -EINVAL;

	for (i = 1; i <= BACK_SCAN_MAX; i++) {
		unsigned long pc;
		u32 insn;
		unsigned int rd, rn, rm, hw;
		unsigned long imm, imm16;
		bool extended;
		bool is64;
		unsigned int add_shift;
		enum wide_imm_op wtype;

		if ((unsigned long)i * 4 > start_pc) break;
		pc = start_pc - (unsigned long)i * 4;
		if (hmkpm_copy_from_kernel_nofault(&insn, (const void *)pc, sizeof(insn)) != 0) break;
		if (insn_is_function_exit(insn)) break;

		if (insn_is_mov_reg(insn, &rd, &rm, &is64)) {
			if (rd == (unsigned int)need_reg) {
				if (rm == 31) break;
				if (need_kind == NEED_ADDR && !is64) break;
				need_reg = (int)rm;
				continue;
			}
			continue;
		}

		if (insn_add_imm(insn, &rd, &rn, &imm)) {
			if (rd == (unsigned int)need_reg) {
				if (imm == 0) {
					if (rn == 31) break;
					need_reg = (int)rn;
					continue;
				}
				if (need_kind == NEED_ADDR && rn != 31 && offset_is_valid(imm)) {
					*offset = (unsigned int)imm;
					return 0;
				}
				break;
			}
			continue;
		}

		if (insn_is_add_reg(insn, &rd, &rn, &rm, &extended, &add_shift)) {
			if (rd == (unsigned int)need_reg) {
				int src;
				if (need_kind != NEED_ADDR) break;
				src = choose_add_register_source(rn, rm, extended);
				if (src < 0 || src == 31) break;
				need_reg = src;
				need_kind = NEED_CONST;
				need_shift = add_shift;
				have_partial = false;
				partial_val = 0;
				partial_mask = 0;
				continue;
			}
			continue;
		}

		if (insn_wide_imm(insn, &rd, &hw, &imm16, &wtype)) {
			if (rd == (unsigned int)need_reg) {
				if (need_kind != NEED_CONST) break;
				if (wtype == WIDE_MOVN) break;
				if (wtype == WIDE_MOVK) {
					u64 hw_mask = 0xffffULL << (hw * 16);
					if (!have_partial) {
						have_partial = true;
						partial_val = 0;
						partial_mask = 0;
					}
					if (!(partial_mask & hw_mask)) {
						partial_val |= (u64)imm16 << (hw * 16);
						partial_mask |= hw_mask;
					}
					continue;
				}
				if (wtype == WIDE_MOVZ) {
					u64 movz_bits = (u64)imm16 << (hw * 16);
					u64 val;
					if (have_partial) val = partial_val | (movz_bits & ~partial_mask);
					else val = movz_bits;
					if (need_shift >= 64) break;
					val <<= need_shift;
					if (offset_is_valid((unsigned long)val)) {
						*offset = (unsigned int)val;
						return 0;
					}
					break;
				}
			}
			continue;
		}

		if (insn_may_write_reg(insn, (unsigned int)need_reg)) break;
	}
	return -ENOENT;
}

static void scan_function_for_lock_offset(unsigned long func, unsigned long size, int func_idx, const unsigned long *lock_addr, const unsigned long *lock_resolved)
{
	unsigned long max_insns = size / 4;
	unsigned long i;
	if (!func || !size) return;
	if (max_insns > MAX_SCAN_INSNS) max_insns = MAX_SCAN_INSNS;

	for (i = 0; i < max_insns; i++) {
		unsigned long pc = func + i * 4;
		u32 insn;
		unsigned long target;
		unsigned long resolved_target;
		unsigned int atomic_rn = 0;
		int j;

		if (hmkpm_copy_from_kernel_nofault(&insn, (const void *)pc, sizeof(insn)) != 0) break;

		if (insn_is_atomic_rwsem_op(insn, &atomic_rn)) {
			unsigned int off = 0;
			if (find_offset_before_pc_reg(pc, atomic_rn, &off) == 0) {
				add_probe_vote(off, func_idx);
			}
			continue;
		}

		if (!insn_is_bl_or_b(pc, insn, &target)) continue;
		resolved_target = resolve_branch_target(target);

		for (j = 0; j < NR_PROBE_LOCKS; j++) {
			unsigned int off = 0;
			if (!lock_addr[j]) continue;
			if (target == lock_addr[j] || resolved_target == lock_addr[j] ||
			    (lock_resolved[j] && (target == lock_resolved[j] || resolved_target == lock_resolved[j]))) {
				if (find_offset_before_pc_reg(pc, 0, &off) == 0)
					add_probe_vote(off, func_idx);
				break;
			}
		}
	}
}

static int pick_consensus_offset(unsigned int *offset, int valid_funcs)
{
	int i;
	int best = -1, second = -1;
	int best_pop = -1, second_pop = -1;
	u32 best_count = 0, second_count = 0;

	for (i = 0; i < nr_probe_votes; i++) {
		int pop = hweight32(probe_votes[i].func_mask);
		if (pop > best_pop || (pop == best_pop && probe_votes[i].count > best_count)) {
			second = best; second_pop = best_pop; second_count = best_count;
			best = i; best_pop = pop; best_count = probe_votes[i].count;
		} else if (pop > second_pop || (pop == second_pop && probe_votes[i].count > second_count)) {
			second = i; second_pop = pop; second_count = probe_votes[i].count;
		}
	}

	if (best < 0) return -ENOENT;
	if (best_pop < 2 && best_count < 2 && !(valid_funcs == 1 && best_count >= 1)) return -ENOENT;
	if (second >= 0 && second_pop == best_pop && second_count == best_count) return -ENOENT;
	if (!offset_is_valid(probe_votes[best].offset)) return -EINVAL;

	*offset = probe_votes[best].offset;
	return 0;
}

static int find_mm_mmap_sem_offset(unsigned int *offset)
{
	unsigned long lock_addr[NR_PROBE_LOCKS] = {0};
	unsigned long lock_resolved[NR_PROBE_LOCKS] = {0};
	unsigned long func_addr[MAX_PROBE_FUNCS] = {0};
	unsigned long func_size[MAX_PROBE_FUNCS] = {0};
	int (*kf_kallsyms_lookup_size_offset)(unsigned long addr, unsigned long *symbolsize, unsigned long *offset) = NULL;
	unsigned int off = 0;
	int valid_funcs = 0, valid_locks = 0;
	int i, j, ret;

	if (!offset) return -EINVAL;
	nr_probe_votes = 0;
	kfunc(memset)(probe_votes, 0, sizeof(probe_votes));

	for (i = 0; i < NR_PROBE_LOCKS; i++) {
		lock_addr[i] = hmkpm_lookup_symbol(lock_symbol_names[i]);
		if (!lock_addr[i]) continue;
		lock_resolved[i] = resolve_branch_target(lock_addr[i]);
		valid_locks++;
	}
	if (valid_locks == 0) return -ENOENT;

	kf_kallsyms_lookup_size_offset = (typeof(kf_kallsyms_lookup_size_offset))hmkpm_lookup_symbol("kallsyms_lookup_size_offset");

	for (i = 0; i < NR_PROBE_FUNCS; i++) {
		func_addr[i] = hmkpm_lookup_symbol(probe_func_names[i]);
		if (!func_addr[i]) continue;
	}

	for (i = 0; i < NR_PROBE_FUNCS; i++) {
		if (!func_addr[i]) continue;
		for (j = 0; j < i; j++) {
			if (func_addr[j] == func_addr[i]) { func_addr[i] = 0; break; }
		}
	}

	for (i = 0; i < NR_PROBE_FUNCS; i++) {
		unsigned long size = 0;
		if (!func_addr[i]) continue;
		if (kf_kallsyms_lookup_size_offset)
			kf_kallsyms_lookup_size_offset(func_addr[i], &size, NULL);
		if (!size) size = 512 * 4;
		if (size < 16 * 4) size = 16 * 4;
		func_size[i] = size & ~3UL;
		valid_funcs++;
	}

	if (valid_funcs == 0) return -ENOENT;

	for (i = 0; i < NR_PROBE_FUNCS; i++) {
		if (!func_addr[i]) continue;
		scan_function_for_lock_offset(func_addr[i], func_size[i], i, lock_addr, lock_resolved);
	}

	ret = pick_consensus_offset(&off, valid_funcs);
	if (ret != 0) return ret;

	*offset = off;
	hmkpm_info("mmap_sem probe: dynamically resolved offset = 0x%x (%u)\n", off, off);
	return 0;
}

static inline int get_mm_mmap_lock_offset(void)
{
	if (kver >= VERSION(6, 12, 0)) return 136;
	else if (kver >= VERSION(6, 6, 0)) return 144;
	else if (kver >= VERSION(6, 1, 0)) return 96;
	else if (kver >= VERSION(5, 15, 0)) return 104;
	else if (kver >= VERSION(5, 10, 0)) return 112;
	else {
		unsigned int off = 0;
		if (find_mm_mmap_sem_offset(&off) == 0) return (int)off;
		return -1;
	}
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
        "__memset", "memset", "__pi___memset", "__pi_memset", "__asan_memset", "__hwasan_memset", "__mte_memset", "__arch_memset", NULL
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

	mmap_lock_sem_offset = get_mm_mmap_lock_offset();
	if (mmap_lock_sem_offset >= 0 && kf_down_read && kf_up_read) {
		hmkpm_info("mmap lock/sem offset = %d (0x%x)\n", mmap_lock_sem_offset, mmap_lock_sem_offset);
	} else {
		hmkpm_warn("mmap lock/sem offset not resolved; running in lockless mode\n");
		mmap_lock_sem_offset = -1;
	}

	if (init_error) {
		hmkpm_error("Symbol resolution failed, aborting...\n");
		return -ENOENT;
	}

	if (kver >= VERSION(5, 10, 0)) {
		fsnotify_addr = hmkpm_lookup_symbol("fsnotify");
		if (fsnotify_addr) {
			err = hook_wrap7((void *)fsnotify_addr, before_fsnotify, 0, 0);
			if (err) fsnotify_hooked = false;
			else fsnotify_hooked = true;
		}
	}

	// 初始化你的 Netlink 通信
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
    if (g_nl_sk && hmkpm_lookup_symbol("netlink_kernel_release")) {
        void (*release_nl)(struct sock*) = (void*)hmkpm_lookup_symbol("netlink_kernel_release");
        release_nl(g_nl_sk);
    }
	hmkpm_info("module cleaned up\n");
	return 0;
}

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
