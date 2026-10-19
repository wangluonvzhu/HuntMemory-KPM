// SPDX-License-Identifier: GPL-2.0
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
#include <linux/string.h>
#include <asm/ptrace.h>
#include <asm-generic/rwonce.h>
#include <uapi/asm-generic/unistd.h>
#include <syscall.h>

KPM_NAME("sys_trace");
KPM_VERSION("1.0.0");
KPM_LICENSE("GPL v2");

#define GHOST_SYSCALL_NR    __NR_futex
#define GHOST_MAGIC         0x1A2B3C4D
#define CMD_GET_PID         0x11
#define CMD_GET_BASE        0x22
#define CMD_READ_MEM        0x33

struct ghost_req {
    uint32_t pid;
    uint32_t _pad1;
    uint64_t addr;
    uint64_t size;
    uint64_t user_buf;
    uint32_t cmd;
    uint8_t  _pad2[12];
};

#ifndef U64_MAX
#define U64_MAX ((u64)~0ULL)
#endif
#ifndef min
#define min(a, b) ((a) < (b) ? (a) : (b))
#endif

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);
struct task_struct *kvar_def(init_task); // 用于遍历进程

void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
long kfunc_def(copy_from_kernel_nofault)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);

// ==========================================
// 物理内存直读核心
// ==========================================
static uint64_t pgt_va_bits, pgt_phys_offset, pgt_page_offset, pgt_linear_voffset;
static uint64_t pgt_page_shift, pgt_page_size, pgt_pgd_align_mask, pgt_pgd_size;
static uint64_t pgt_page_level, pgt_user_limit, pgt_high_memory;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }
static inline uint64_t pgt_untag_user_va(uint64_t va) { return va & 0x00FFFFFFFFFFFFFFULL; }

static inline int validate_virt_range(uint64_t va, uint64_t size) {
    if (unlikely(size == 0) || va < pgt_page_offset) return -EFAULT;
    if (unlikely(va > U64_MAX - size)) return -EFAULT;
    if (unlikely((va + size - 1) >= pgt_high_memory)) return -EFAULT;
    return 0;
}
static inline int validate_phys_range(uint64_t phys, uint64_t size) {
    if (unlikely(size == 0) || (phys >> 48) != 0) return -EFAULT;
    return validate_virt_range(pgt_phys_to_virt(phys), size);
}
static inline uint64_t pgt_desc_to_phys(uint64_t desc) {
    uint64_t addr_mask = (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
    return desc & addr_mask;
}

static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write) {
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

        if (type == 1ULL) {
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

static int pgt_pgtable_init(void) {
    uint64_t tcr_el1, t1sz, va1_bits, t0sz, va0_bits, tg0;
    asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    t1sz = (tcr_el1 >> 16) & 0x3F; va1_bits = 64 - t1sz;
    t0sz = tcr_el1 & 0x3F; va0_bits = 64 - t0sz; tg0 = (tcr_el1 >> 14) & 0x3ULL;

    if (va0_bits > 48 || va0_bits < 36) return -EINVAL;
    pgt_va_bits = va0_bits; pgt_user_limit = (1ULL << va0_bits) - 1;
    pgt_page_shift = (tg0 == 0) ? 12 : ((tg0 == 2) ? 14 : 0);
    if (!pgt_page_shift) return -EINVAL;
    pgt_page_level = (va0_bits - 4) / (pgt_page_shift - 3);
    if (pgt_page_level < 2 || pgt_page_level > 4) return -EINVAL;
    
    pgt_page_size = 1ULL << pgt_page_shift;
    pgt_pgd_size = pgt_page_size; pgt_pgd_align_mask = pgt_page_size - 1;
    pgt_page_offset = -(UL(1) << va1_bits);

    kv_memstart_addr = (typeof(kv_memstart_addr))kallsyms_lookup_name("memstart_addr");
    if (!kv_memstart_addr) return -EFAULT;
    pgt_phys_offset = *(u64 *)kv_memstart_addr;
    pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

    kv_high_memory = (typeof(kv_high_memory))kallsyms_lookup_name("high_memory");
    pgt_high_memory = kv_high_memory ? *(u64 *)kv_high_memory : U64_MAX;
    return 0;
}

static void hmkpm_memcpy(void *dst, const void *src, size_t n) {
    uint8_t *d = (uint8_t *)dst;
    const uint8_t *s = (const uint8_t *)src;
    while (n >= 8) { *(uint64_t *)d = *(const uint64_t *)s; d += 8; s += 8; n -= 8; }
    while (n > 0) { *d++ = *s++; n--; }
}

static ssize_t pgt_rw_mm(struct mm_struct *mm, uint64_t remote_va, size_t len, void __user *local_buf, bool is_write)
{
    ssize_t total = 0;
    uint64_t pgd = 0;
    uint8_t bounce[512];

    if (!mm) return -ESRCH;
    if (kfunc(copy_from_kernel_nofault)(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), sizeof(pgd)) != 0 || !pgd) return -EFAULT;

    while (len > 0) {
        unsigned long page_off = remote_va & (pgt_page_size - 1);
        size_t chunk = min(len, (size_t)(pgt_page_size - page_off));
        chunk = min(chunk, (size_t)sizeof(bounce));

        uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va, is_write);
        if (!tkpa) {
            if (total > 0) break;
            return -EFAULT;
        }

        void *tkva = (void *)pgt_phys_to_virt(tkpa);
        hmkpm_memcpy(bounce, tkva, chunk);

        if (kfunc(__arch_copy_to_user)(local_buf, bounce, chunk) != 0) break;

        total += chunk; local_buf = (void __user *)((uintptr_t)local_buf + chunk);
        remote_va += chunk; len -= chunk;
    }
    return total;
}

// ==========================================
// 纯内核态：进程与模块基址解析 (5.10 GKI 偏移)
// ==========================================
static int resolve_pid_by_name(const char *pkg_name) {
    uint64_t init_task_addr = (uint64_t)kv_init_task;
    if (!init_task_addr) return -1;

    // 5.10 GKI 标准偏移
    uint64_t tasks_off = 0x458;
    uint64_t comm_off  = 0x730;
    uint64_t pid_off   = 0x620;

    uint64_t tasks_head = init_task_addr + tasks_off;
    uint64_t pos_addr = 0;
    
    if (kfunc(copy_from_kernel_nofault)(&pos_addr, (void*)tasks_head, 8)) return -1;

    size_t target_len = strlen(pkg_name);
    if (target_len > 15) target_len = 15;

    while (pos_addr != tasks_head) {
        uint64_t task_ptr = pos_addr - tasks_off;
        char comm[16] = {0};
        
        if (kfunc(copy_from_kernel_nofault)(comm, (void*)(task_ptr + comm_off), 16) == 0) {
            if (strncmp(comm, pkg_name, target_len) == 0) {
                int pid = -1;
                if (kfunc(copy_from_kernel_nofault)(&pid, (void*)(task_ptr + pid_off), 4) == 0) {
                    return pid;
                }
            }
        }
        if (kfunc(copy_from_kernel_nofault)(&pos_addr, (void*)pos_addr, 8)) break;
    }
    return -1;
}

static uint64_t resolve_base_by_name(int pid, const char *so_name) {
    struct task_struct *task = kfunc(find_task_by_vpid)(pid);
    if (!task) return 0;
    
    // task->mm (5.10 偏移 0x540)
    uint64_t mm_addr = 0;
    if (kfunc(copy_from_kernel_nofault)(&mm_addr, (void*)((uint64_t)task + 0x540), 8)) return 0;
    if (!mm_addr) return 0;
    
    // mm->mmap (5.10 偏移 0x0)
    uint64_t vma_addr = 0;
    if (kfunc(copy_from_kernel_nofault)(&vma_addr, (void*)(mm_addr + 0x0), 8)) return 0;
    
    uint64_t target_base = 0;
    while (vma_addr) {
        uint64_t vm_start = 0, vm_flags = 0, vm_file = 0, vm_next = 0;
        // vma 结构体偏移
        kfunc(copy_from_kernel_nofault)(&vm_start, (void*)(vma_addr + 0x0), 8);
        kfunc(copy_from_kernel_nofault)(&vm_flags, (void*)(vma_addr + 0x50), 8);
        kfunc(copy_from_kernel_nofault)(&vm_file,  (void*)(vma_addr + 0x98), 8);
        kfunc(copy_from_kernel_nofault)(&vm_next,  (void*)(vma_addr + 0x10), 8);
        
        if (vm_file) {
            uint64_t dentry = 0;
            // file->f_path.dentry (0x18)
            if (kfunc(copy_from_kernel_nofault)(&dentry, (void*)(vm_file + 0x18), 8) == 0 && dentry) {
                uint64_t name_ptr = 0;
                // dentry->d_name.name (0x28)
                if (kfunc(copy_from_kernel_nofault)(&name_ptr, (void*)(dentry + 0x28), 8) == 0 && name_ptr) {
                    char name[256] = {0};
                    if (kfunc(copy_from_kernel_nofault)(name, (void*)name_ptr, 255) == 0) {
                        if (strstr(name, so_name)) {
                            if (vm_flags & 0x4) { // VM_EXEC
                                if (target_base == 0 || vm_start < target_base) {
                                    target_base = vm_start;
                                }
                            }
                        }
                    }
                }
            }
        }
        vma_addr = vm_next;
    }
    return target_base;
}

// ==========================================
// 系统调用拦截
// ==========================================
static void ghost_syscall_before(hook_fargs6_t *args, void *udata) {
    long magic = (long)syscall_argn(args, 0);
    if (magic != GHOST_MAGIC) return;

    uint64_t req_ptr = (uint64_t)syscall_argn(args, 1);
    struct ghost_req req;

    if (kfunc(__arch_copy_from_user)(&req, (void __user *)req_ptr, sizeof(req))) {
        args->skip_origin = 1;
        args->ret = -14;
        return;
    }

    long ret = -1;
    struct task_struct *task;
    struct mm_struct *mm;

    if (req.cmd == CMD_GET_PID) {
        char pkg[64] = {0};
        if (kfunc(__arch_copy_from_user)(pkg, (void __user *)req.addr, sizeof(pkg)-1) == 0) {
            ret = resolve_pid_by_name(pkg);
        }
    } 
    else if (req.cmd == CMD_GET_BASE) {
        char soname[64] = {0};
        if (kfunc(__arch_copy_from_user)(soname, (void __user *)req.addr, sizeof(soname)-1) == 0) {
            ret = resolve_base_by_name(req.pid, soname);
        }
    }
    else if (req.cmd == CMD_READ_MEM) {
        task = kfunc(find_task_by_vpid)(req.pid);
        if (task && (mm = kfunc(get_task_mm)(task))) {
            long read_ret = pgt_rw_mm(mm, req.addr, req.size, (void __user *)req.user_buf, false);
            ret = (read_ret == (long)req.size) ? 0 : -EFAULT;
            kfunc(mmput)(mm);
        }
    }

    args->skip_origin = 1;
    args->ret = ret;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved) {
    kv_init_task = (typeof(kv_init_task))kallsyms_lookup_name("init_task");
    kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))kallsyms_lookup_name("__arch_copy_to_user");
    kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))kallsyms_lookup_name("__arch_copy_from_user");
    kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))kallsyms_lookup_name("copy_from_kernel_nofault");
    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_vpid");
    kf_get_task_mm = (typeof(kf_get_task_mm))kallsyms_lookup_name("get_task_mm");
    kf_mmput = (typeof(kf_mmput))kallsyms_lookup_name("mmput");

    if (pgt_pgtable_init() != 0) return -ENOENT;
    if (!kv_init_task) return -ENOENT;

    hook_err_t err = inline_hook_syscalln(GHOST_SYSCALL_NR, 6, ghost_syscall_before, 0, 0);
    if (err) return -ENOENT;

    return 0;
}

static long module_cleanup_handler(void *__user reserved) {
    inline_unhook_syscalln(GHOST_SYSCALL_NR, ghost_syscall_before, 0);
    return 0;
}

KPM_INIT(module_init_handler);
KPM_EXIT(module_cleanup_handler);
