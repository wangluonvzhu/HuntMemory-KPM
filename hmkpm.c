// 最终兼容版 ghost_read.c
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

// === 针对 5.10 内核补充的必要头文件 ===
#include <linux/mm.h>
#include <linux/fs.h>
#include <linux/sched/signal.h>
// =====================================

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

// ... (这里原封不动保留之前发你的 符号声明、pgt_ 相关函数、hmkpm_memcpy、pgt_rw_mm) ...
// 注意：因为你之前发的 hmkpm.c 里有些变量（如 kv_memstart_addr）如果没有声明，
// 请确保你的 kputils.h 或 ksyms.h 里已经有 extern 定义，或者加上：
u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);
void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
long kfunc_def(copy_from_kernel_nofault)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);

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

// [将你原版 hmkpm.c 的 pgt_pgtable_to_tkpa 和 pgt_pgtable_init 完整粘贴在这里]
// [将你原版 hmkpm.c 的 hmkpm_memcpy 和 pgt_rw_mm 完整粘贴在这里]

static int resolve_pid_by_name(const char *pkg_name) {
    struct task_struct *task;
    size_t target_len = strlen(pkg_name);
    if (target_len > 15) target_len = 15;
    for_each_process(task) {
        if (task->comm && strncmp(task->comm, pkg_name, target_len) == 0) {
            return task->pid;
        }
    }
    return -1;
}

static uint64_t resolve_base_by_name(struct mm_struct *mm, const char *so_name) {
    struct vm_area_struct *vma;
    uint64_t base = 0;
    if (!mm) return 0;

    for (vma = mm->mmap; vma; vma = vma->vm_next) {
        if (vma->vm_file) {
            const char *path = (const char *)vma->vm_file->f_path.dentry->d_name.name;
            if (path && strstr(path, so_name)) {
                if ((vma->vm_flags & VM_EXEC) && (vma->vm_start < base || base == 0)) {
                    base = vma->vm_start;
                }
            }
        }
    }
    return base;
}

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

    switch (req.cmd) {
        case CMD_GET_PID: {
            char pkg[64] = {0};
            if (kfunc(__arch_copy_from_user)(pkg, (void __user *)req.addr, sizeof(pkg)-1) == 0) {
                ret = resolve_pid_by_name(pkg);
            }
            break;
        }
        case CMD_GET_BASE:
            task = kfunc(find_task_by_vpid)(req.pid);
            if (task && (mm = kfunc(get_task_mm)(task))) {
                char soname[64] = {0};
                if (kfunc(__arch_copy_from_user)(soname, (void __user *)req.addr, sizeof(soname)-1) == 0) {
                    ret = resolve_base_by_name(mm, soname);
                }
                kfunc(mmput)(mm);
            }
            break;

        case CMD_READ_MEM:
            task = kfunc(find_task_by_vpid)(req.pid);
            if (task && (mm = kfunc(get_task_mm)(task))) {
                long read_ret = pgt_rw_mm(mm, req.addr, req.size, (void __user *)req.user_buf, false);
                ret = (read_ret == (long)req.size) ? 0 : -EFAULT;
                kfunc(mmput)(mm);
            }
            break;
    }

    args->skip_origin = 1;
    args->ret = ret;
}

static long module_init_handler(const char *args, const char *event, void *__user reserved) {
    kf___arch_copy_to_user = (typeof(kf___arch_copy_to_user))kallsyms_lookup_name("__arch_copy_to_user");
    kf___arch_copy_from_user = (typeof(kf___arch_copy_from_user))kallsyms_lookup_name("__arch_copy_from_user");
    kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))kallsyms_lookup_name("copy_from_kernel_nofault");
    kf_find_task_by_vpid = (typeof(kf_find_task_by_vpid))kallsyms_lookup_name("find_task_by_vpid");
    kf_get_task_mm = (typeof(kf_get_task_mm))kallsyms_lookup_name("get_task_mm");
    kf_mmput = (typeof(kf_mmput))kallsyms_lookup_name("mmput");

    if (pgt_pgtable_init() != 0) return -ENOENT;

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
