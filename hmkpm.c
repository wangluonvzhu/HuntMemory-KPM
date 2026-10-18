// SPDX-License-Identifier: GPL-2.0
/*
 * KernelPatch Module (KPM) - Ghost Channel Edition
 * 融合 HuntMemory-KPM 的页表遍历 + android-wuwa 的 do_mem_abort 隐蔽通信
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
#include <asm/ptrace.h>
#include <asm-generic/rwonce.h>

KPM_NAME("HMKPM_GHOST");
KPM_VERSION("1.0.0");
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Fusion");
KPM_DESCRIPTION("Ghost Channel Memory R/W");

#define HMKPM_TAG "[HMKPM] "
#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

// ----------------- 幽灵通信协议定义 -----------------
#define HMKPM_GHOST_PREFIX 0xDEAD000000000000ULL
#define HMKPM_GHOST_MASK   0xFFFF000000000000ULL

#define HMKPM_MAGIC_READ   0x101
#define HMKPM_MAGIC_WRITE  0x102

struct hmkpm_req {
    int32_t pid;
    uint32_t _pad;
    uint64_t addr;
    uint64_t size;
};
// ----------------------------------------------------

static bool hook_active = true;
static int mmap_lock_sem_offset = -1;

// 需要动态解析的内核符号
void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
long kfunc_def(copy_from_kernel_nofault)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);
void kfunc_def(__rcu_read_lock)(void);
void kfunc_def(__rcu_read_unlock)(void);
void kfunc_def(down_read)(struct rw_semaphore *sem);
void kfunc_def(up_read)(struct rw_semaphore *sem);

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);

static unsigned long hmkpm_lookup_symbol(const char *name)
{
    if (!name || !kallsyms_lookup_name) return 0;
    return kallsyms_lookup_name(name);
}

// 页表遍历相关全局变量
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
static uint64_t pgt_high_memory;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }
static inline uint64_t pgt_virt_to_phys(uint64_t addr) { return addr - pgt_linear_voffset; }
static inline uint64_t pgt_untag_user_va(uint64_t va) { return va & 0x00FFFFFFFFFFFFFFULL; }

static inline int validate_virt_range(uint64_t va, uint64_t size)
{
    if (unlikely(size == 0) || va < pgt_page_offset) return -EFAULT;
    if (unlikely(va > U64_MAX - size)) return -EFAULT;
    if (unlikely((va + size - 1) >= pgt_high_memory)) return -EFAULT;
    return 0;
}

static inline int validate_phys_range(uint64_t phys, uint64_t size)
{
    if (unlikely(size == 0) || (phys >> 48) != 0) return -EFAULT;
    return validate_virt_range(pgt_phys_to_virt(phys), size);
}

static inline uint64_t pgt_desc_to_phys(uint64_t desc)
{
    uint64_t addr_mask = (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
    return desc & addr_mask;
}

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write)
{
    uint64_t table_va = pgd;
    uint64_t pxd_bits = pgt_page_shift - 3;
    uint64_t pxd_ptrs = 1ULL << pxd_bits;
    int64_t start = 4 - (int64_t)pgt_page_level;
    va = pgt_untag_user_va(va);

    if (!pgd || (pgd & pgt_pgd_align_mask) || validate_virt_range(pgd, pgt_pgd_size) || (va >> pgt_va_bits))
        return 0;

    for (int64_t lv = start; lv < 4; lv++) {
        uint64_t pxd_shift = (pgt_page_shift - 3) * (4 - lv) + 3;
        if (pxd_shift >= pgt_va_bits) return 0;
        uint64_t pxd_index = (va >> pxd_shift) & (pxd_ptrs - 1);
        
        uint64_t cur_table_size = (lv == start) ? pgt_pgd_size : pgt_page_size;
        if (validate_virt_range(table_va, cur_table_size)) return 0;

        uint64_t entry_va = table_va + pxd_index * 8;
        uint64_t desc = 0;
        if (kfunc(copy_from_kernel_nofault)(&desc, (const void *)entry_va, sizeof(desc)) != 0) return 0;

        uint64_t type = desc & 3ULL;
        if (type == 0ULL || type == 2ULL) return 0;

        if (lv == 3) {
            if (type != 3ULL) return 0;
            if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51))) return 0;
            uint64_t base = pgt_desc_to_phys(desc);
            return validate_phys_range(base, pgt_page_size) ? 0 : (base | (va & (pgt_page_size - 1)));
        }

        if (type == 1ULL) { // Block
            if (pgt_page_shift == 14 ? (lv != 2) : (lv != 1 && lv != 2)) return 0;
            if (is_write && (desc & (1ULL << 7)) && !(desc & (1ULL << 51))) return 0;
            uint64_t block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
            uint64_t block_size = 1ULL << block_bits;
            uint64_t base = pgt_desc_to_phys(desc);
            return validate_phys_range(base, block_size) ? 0 : ((base & ~(block_size - 1)) | (va & (block_size - 1)));
        }

        if (is_write && (desc & (1ULL << 62))) return 0;
        uint64_t next_pa = pgt_desc_to_phys(desc);
        if (validate_phys_range(next_pa, pgt_page_size)) return 0;
        table_va = pgt_phys_to_virt(next_pa);
    }
    return 0;
}

static int pgt_pgtable_init(void)
{
    uint64_t tcr_el1, t1sz, va1_bits, t0sz, va0_bits, tg0;
    asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    t1sz = (tcr_el1 >> 16) & 0x3F;
    va1_bits = 64 - t1sz;
    t0sz = tcr_el1 & 0x3F;
    va0_bits = 64 - t0sz;
    tg0 = (tcr_el1 >> 14) & 0x3ULL;

    if (va0_bits > 48 || va0_bits < 36) return -EINVAL;
    pgt_va_bits = va0_bits;
    pgt_user_limit = (1ULL << va0_bits) - 1;
    pgt_page_shift = (tg0 == 0) ? 12 : ((tg0 == 2) ? 14 : 0);
    if (!pgt_page_shift) return -EINVAL;
    pgt_page_level = (va0_bits - 4) / (pgt_page_shift - 3);
    if (pgt_page_level < 2 || pgt_page_level > 4) return -EINVAL;
    
    pgt_page_size = 1ULL << pgt_page_shift;
    pgt_pgd_size = pgt_page_size; // 5.10+ always page size
    pgt_pgd_align_mask = pgt_page_size - 1;
    pgt_page_offset = -(UL(1) << va1_bits);

    if (!kallsyms_lookup_name) return -EFAULT;
    kv_memstart_addr = (typeof(kv_memstart_addr))hmkpm_lookup_symbol("memstart_addr");
    if (!kv_memstart_addr) return -EFAULT;
    pgt_phys_offset = *(u64 *)kv_memstart_addr;
    pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

    kv_high_memory = (typeof(kv_high_memory))hmkpm_lookup_symbol("high_memory");
    pgt_high_memory = kv_high_memory ? *(u64 *)kv_high_memory : ~0ULL;
    return 0;
}

// ----------------- 读写核心逻辑 -----------------

static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len, void __user *local_buf, bool is_write)
{
    ssize_t total = 0;
    uint64_t pgd = 0;
    uint8_t bounce[512]; // 栈上缓冲

    if (!mm) return -ESRCH;
    if (*(u64 *)((uintptr_t)mm + mm_struct_offset.pgd_offset) == 0) { // 快速校验
        if (kfunc(copy_from_kernel_nofault)(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd)
            return -EFAULT;
    } else {
        pgd = *(u64 *)((uintptr_t)mm + mm_struct_offset.pgd_offset);
    }

    while (len > 0) {
        unsigned long page_off = remote_va & (pgt_page_size - 1);
        size_t chunk = min(len, (size_t)(pgt_page_size - page_off));
        chunk = min(chunk, (size_t)sizeof(bounce));

        if (is_write) {
            if (kfunc(__arch_copy_from_user)(bounce, local_buf, chunk) != 0) break;
        }

        if (mmap_lock_sem_offset >= 0 && kf_down_read) {
            kfunc(down_read)((struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset));
        }

        uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va, is_write);
        if (!tkpa) {
            if (mmap_lock_sem_offset >= 0 && kf_up_read) kfunc(up_read)((struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset));
            if (total > 0) break;
            return -EFAULT;
        }

        void *tkva = (void *)pgt_phys_to_virt(tkpa);
        if (is_write) {
            memcpy(tkva, bounce, chunk);
        } else {
            memcpy(bounce, tkva, chunk);
        }

        if (mmap_lock_sem_offset >= 0 && kf_up_read) kfunc(up_read)((struct rw_semaphore *)((uintptr_t)mm + mmap_lock_sem_offset));

        if (!is_write) {
            if (kfunc(__arch_copy_to_user)(local_buf, bounce, chunk) != 0) break;
        }

        total += chunk;
        local_buf = (void __user *)((uintptr_t)local_buf + chunk);
        remote_va += chunk;
        len -= chunk;
    }
    return total;
}

static long hmkpm_do_rw(void __user *req_ptr, void __user *data_ptr, uint64_t magic)
{
    struct hmkpm_req req;
    if (kfunc(__arch_copy_from_user)(&req, req_ptr, sizeof(req)) != 0) return -EFAULT;
    if (req.size == 0) return 0;

    bool is_write = (magic == HMKPM_MAGIC_WRITE);
    struct task_struct *task = NULL;
    struct mm_struct *mm = NULL;
    long ret;

    kfunc(__rcu_read_lock)();
    task = kfunc(find_task_by_vpid)(req.pid);
    if (task) mm = kfunc(get_task_mm)(task);
    kfunc(__rcu_read_unlock)();
    if (!mm) return -ESRCH;

    ret = pgt_rw_mm(mm, req.addr, req.size, data_ptr, is_write);
    kfunc(mmput)(mm);
    return (ret == (long)req.size) ? 0 : -EFAULT;
}

// ----------------- 缺页异常拦截通道 -----------------

static void before_do_mem_abort(hook_fargs3_t *args, void *udata)
{
    unsigned long far = (unsigned long)args->arg0;
    struct pt_regs *regs = (struct pt_regs *)args->arg2;

    // 快速过滤
    if (likely((far & HMKPM_GHOST_MASK) != HMKPM_GHOST_PREFIX)) return;
    if (!READ_ONCE(hook_active)) return;

    uint64_t magic = regs->regs[0];
    void __user *req_ptr = (void __user *)regs->regs[1];
    void __user *data_ptr = (void __user *)regs->regs[2];

    // 伪造成功，跳过内核原有 SIGSEGV 处理
    args->skip_origin = 1;
    args->ret = 0;
    regs->regs[0] = 0; // 默认返回值

    if (magic == HMKPM_MAGIC_READ || magic == HMKPM_MAGIC_WRITE) {
        regs->regs[0] = (uint64_t)hmkpm_do_rw(req_ptr, data_ptr, magic);
    }

    // 强制 PC 跳过触发异常的指令（ARM64 固定 4 字节指令）
    regs->pc += 4;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
    if (pgt_pgtable_init() != 0) return -ENOENT;

    kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))hmkpm_lookup_symbol("__arch_copy_to_user");
    kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))hmkpm_lookup_symbol("__arch_copy_from_user");
    kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))hmkpm_lookup_symbol("find_task_by_vpid");
    kf_get_task_mm = (typeof(kf_get_task_mm))hmkpm_lookup_symbol("get_task_mm");
    kf_mmput = (typeof(kf_mmput))hmkpm_lookup_symbol("mmput");
    kf___rcu_read_lock = (typeof(kf___rcu_read_lock))hmkpm_lookup_symbol("__rcu_read_lock");
    kf___rcu_read_unlock = (typeof(kf___rcu_read_unlock))hmkpm_lookup_symbol("__rcu_read_unlock");
    kf_down_read = (typeof(kf_down_read))hmkpm_lookup_symbol("down_read");
    kf_up_read = (typeof(kf_up_read))hmkpm_lookup_symbol("up_read");

    if (!kf___arch_copy_to_user || !kf___arch_copy_from_user || !kf_find_task_by_vpid) {
        hmkpm_error("Core symbols missing!\n");
        return -ENOENT;
    }

    // Kernel 5.10 mm->mmap_lock 偏移量固定为 112
    mmap_lock_sem_offset = 112;

    unsigned long do_mem_abort_addr = hmkpm_lookup_symbol("do_mem_abort");
    if (!do_mem_abort_addr) {
        hmkpm_error("Failed to find do_mem_abort!\n");
        return -ENOENT;
    }

    hook_err_t err = hook_wrap3((void *)do_mem_abort_addr, before_do_mem_abort, 0, 0);
    if (err) {
        hmkpm_error("hook do_mem_abort failed: %d\n", err);
        return -ENOENT;
    }

    hmkpm_info("Ghost Channel KPM Loaded.\n");
    return 0;
}

static long module_cleanup_handler(void *__user reserved)
{
    unsigned long do_mem_abort_addr = hmkpm_lookup_symbol("do_mem_abort");
    if (do_mem_abort_addr) hook_unwrap((void *)do_mem_abort_addr, before_do_mem_abort, 0);
    return 0;
}

KPM_INIT(module_init_handler);
KPM_EXIT(module_cleanup_handler);
