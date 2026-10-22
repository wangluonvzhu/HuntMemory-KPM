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
#include <uapi/asm-generic/unistd.h>
#include <asm-generic/rwonce.h>

#define HMKPM_VERSION_STR "3.0.0-silent"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("KernelPatch Module (KPM) HMKPM - Silent Read Channel");

#define HMKPM_TAG "[HMKPM] "
#define hmkpm_info(fmt, ...) logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...) logke(HMKPM_TAG fmt, ##__VA_ARGS__)

/* 适配 Android GKI 5.10 结构体偏移 */
#define MM_MMAP_OFFSET       0x00
#define VMA_VM_START_OFFSET  0x00
#define VMA_VM_FILE_OFFSET   0x80
#define VMA_VM_NEXT_OFFSET   0xA0
#define FILE_F_PATH_DENTRY_OFFSET 0x18
#define DENTRY_D_NAME_NAME_OFFSET 0x38

/* 通信协议结构 (与用户态严格一致) */
struct hmkpm_cmd {
    uint32_t cmd;      // 1=GET_PID, 2=GET_BASE, 3=READ
    int32_t pid;       // 目标 PID
    uint64_t addr;     // 读地址
    uint64_t size;     // 读大小
    uint64_t user_buf; // 本地接收 Buffer
    char name[64];     // 包名或模块名
};

/* KPM 内部函数声明 */
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

/* KPM 内部变量声明 */
u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);

/* 内部字符串匹配函数 (必须放在使用前) */
static int hmkpm_strstr_inline(const char *haystack, const char *needle) {
    if (!*needle) return 1;
    for (; *haystack; ++haystack) {
        const char *h = haystack; const char *n = needle;
        while (*h && *n && *h == *n) { h++; n++; }
        if (!*n) return 1;
    }
    return 0;
}

/* 符号查找宏 */
static unsigned long hmkpm_lookup_symbol(const char *name) {
    if (!name || !kallsyms_lookup_name) return 0;
    return kallsyms_lookup_name(name);
}

#define hkfunc_match(func) \
do { \
    kf_##func = (typeof(kf_##func))hmkpm_lookup_symbol(#func); \
    if (!kf_##func) { hmkpm_error("Missing kfunc %s\n", #func); return -ENOENT; } \
} while (0)

#define hkvar_match(var) \
do { \
    kv_##var = (typeof(kv_##var))hmkpm_lookup_symbol(#var); \
    if (!kv_##var) { hmkpm_error("Missing kvar %s\n", #var); init_error = true; } \
} while (0)

static bool init_error = false;

/* 内存拷贝封装 */
static inline long hmkpm_copy_from_kernel_nofault(void *dst, const void *src, size_t size) {
    if (!src || !dst) return -EINVAL;
    if (kf_copy_from_kernel_nofault) return kfunc(copy_from_kernel_nofault)(dst, src, size);
    if (kf_probe_kernel_read) return kfunc(probe_kernel_read)(dst, src, size);
    return -ENOSYS;
}

static inline unsigned long hmkpm_copy_from_user(void *to, const void __user *from, unsigned long n) {
    return kfunc(__arch_copy_from_user)(to, from, n);
}

static inline unsigned long hmkpm_copy_to_user(void __user *to, const void *from, unsigned long n) {
    return kfunc(__arch_copy_to_user)(to, from, n);
}

/* 页表配置 */
static uint64_t pgt_va_bits, pgt_phys_offset, pgt_page_offset, pgt_linear_voffset;
static uint64_t pgt_page_shift, pgt_page_size, pgt_pgd_align_mask, pgt_pgd_size;
static uint64_t pgt_page_level, pgt_user_limit, pgt_high_memory;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }

static int pgt_init(void) {
    uint64_t tcr_el1, t1sz, va1_bits, t0sz, va0_bits, tg0, pxd_bits;
    asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    t1sz = (tcr_el1 >> 16) & 0x3F; va1_bits = 64 - t1sz;
    t0sz = tcr_el1 & 0x3F; va0_bits = 64 - t0sz;
    tg0 = (tcr_el1 >> 14) & 0x3ULL;

    if (va0_bits > 48 || va0_bits < 36) return -EINVAL;
    pgt_va_bits = va0_bits; pgt_user_limit = (1ULL << va0_bits) - 1;
    pgt_page_shift = (tg0 == 0) ? 12 : 14;
    pgt_page_size = 1ULL << pgt_page_shift;
    
    pxd_bits = pgt_page_shift - 3;
    pgt_page_level = (va0_bits - 4) / pxd_bits;
    pgt_pgd_size = pgt_page_size; 
    pgt_pgd_align_mask = pgt_page_size - 1;

    if (kver >= VERSION(4, 6, 0)) pgt_page_offset = -(1ULL << (va1_bits - 1));
    else pgt_page_offset = -(1ULL << va1_bits);

    hkvar_match(memstart_addr);
    if (!kv_memstart_addr) return -EFAULT;
    pgt_phys_offset = kvar_val(memstart_addr);
    pgt_linear_voffset = pgt_page_offset - pgt_phys_offset;

    hkvar_match(high_memory);
    if (kv_high_memory) {
        pgt_high_memory = (uint64_t)kvar_val(high_memory);
    } else {
        pgt_high_memory = ~0ULL;
    }

    return 0;
}

static inline uint64_t pgt_untag(uint64_t va) { return va & 0x00FFFFFFFFFFFFFFULL; }
static inline uint64_t pgt_desc_to_phys(uint64_t desc) {
    return desc & (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
}

/* 绝对防崩溃的页表遍历 */
static uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va) {
    uint64_t table_va, pxd_bits, pxd_ptrs, desc, type, base;
    int64_t start, lv;

    if (!pgd || (pgd & pgt_pgd_align_mask)) return 0;
    va = pgt_untag(va);
    if (va >> pgt_va_bits) return 0;

    table_va = pgd; pxd_bits = pgt_page_shift - 3; pxd_ptrs = 1ULL << pxd_bits;
    start = 4 - (int64_t)pgt_page_level;

    for (lv = start; lv < 4; lv++) {
        uint64_t pxd_shift = (pgt_page_shift - 3) * (4 - lv) + 3;
        if (pxd_shift >= pgt_va_bits) return 0;
        uint64_t pxd_index = (va >> pxd_shift) & (pxd_ptrs - 1);
        uint64_t entry_va = table_va + pxd_index * 8;

        if (hmkpm_copy_from_kernel_nofault(&desc, (const void *)entry_va, 8) != 0) return 0;
        type = desc & 3ULL;
        if (type == 0 || type == 2) return 0;

        if (lv == 3) {
            if (type != 3) return 0;
            base = pgt_desc_to_phys(desc);
            return base | (va & (pgt_page_size - 1));
        }
        if (type == 1) {
            uint64_t block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
            if (block_bits >= 64) return 0;
            uint64_t block_mask = (1ULL << block_bits) - 1;
            base = pgt_desc_to_phys(desc);
            return (base & ~block_mask) | (va & block_mask);
        }
        uint64_t next_pa = pgt_desc_to_phys(desc);
        table_va = pgt_phys_to_virt(next_pa);
    }
    return 0;
}

/* 读进程内存 */
static ssize_t safe_read_memory(pid_t pid, uint64_t remote_va, void *local_buf, size_t len) {
    struct task_struct *task = NULL; 
    struct mm_struct *mm = NULL; 
    uint64_t pgd = 0;
    ssize_t total = 0;

    kfunc(__rcu_read_lock)();
    task = kfunc(find_task_by_vpid)(pid);
    if (task) mm = kfunc(get_task_mm)(task);
    kfunc(__rcu_read_unlock)();
    
    if (!mm) return -ESRCH;

    if (hmkpm_copy_from_kernel_nofault(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), 8) != 0 || !pgd) {
        kfunc(mmput)(mm); return -EFAULT;
    }

    while (len > 0) {
        uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, remote_va);
        if (!tkpa) {
            if (total > 0) break;
            kfunc(mmput)(mm); return -EFAULT;
        }

        size_t chunk = pgt_page_size - (remote_va & (pgt_page_size - 1));
        if (chunk > len) chunk = len;

        void *tkva = (void *)pgt_phys_to_virt(tkpa);
        if (hmkpm_copy_from_kernel_nofault((uint8_t*)local_buf + total, tkva, chunk) != 0) {
            if (total > 0) break;
            kfunc(mmput)(mm); return -EFAULT;
        }
        
        total += chunk; remote_va += chunk; len -= chunk;
    }
    kfunc(mmput)(mm);
    return total;
}

/* 遍历找 PID */
static int kernel_find_pid(const char *pkg_name) {
    for (int i = 1; i < 32768; i++) {
        struct task_struct *task;
        kfunc(__rcu_read_lock)();
        task = kfunc(find_task_by_vpid)(i);
        if (task) {
            char comm[17] = {0};
            // 5.10 GKI task->comm 偏移 0x8C0
            hmkpm_copy_from_kernel_nofault(comm, (const void *)((uintptr_t)task + 0x8C0), 16);
            if (comm[0] && hmkpm_strstr_inline(comm, pkg_name)) {
                kfunc(__rcu_read_unlock)();
                return i;
            }
        }
        kfunc(__rcu_read_unlock)();
    }
    return -1;
}

/* 遍历 VMA 找基址 */
static uint64_t kernel_get_base(int pid, const char *mod_name) {
    struct task_struct *task = NULL; 
    struct mm_struct *mm = NULL;
    uint64_t result = 0;

    kfunc(__rcu_read_lock)();
    task = kfunc(find_task_by_vpid)(pid);
    if (task) mm = kfunc(get_task_mm)(task);
    kfunc(__rcu_read_unlock)();
    if (!mm) return 0;

    uintptr_t vma = 0;
    hmkpm_copy_from_kernel_nofault(&vma, (const void *)((uintptr_t)mm + MM_MMAP_OFFSET), 8);
    while (vma) {
        uintptr_t file = 0;
        hmkpm_copy_from_kernel_nofault(&file, (const void *)(vma + VMA_VM_FILE_OFFSET), 8);
        if (file) {
            uintptr_t dentry = 0;
            hmkpm_copy_from_kernel_nofault(&dentry, (const void *)(file + FILE_F_PATH_DENTRY_OFFSET), 8);
            if (dentry) {
                char *name_ptr = NULL;
                hmkpm_copy_from_kernel_nofault(&name_ptr, (const void *)(dentry + DENTRY_D_NAME_NAME_OFFSET), 8);
                if (name_ptr) {
                    char iname[64] = {0};
                    if (hmkpm_copy_from_kernel_nofault(iname, name_ptr, 63) == 0) {
                        if (hmkpm_strstr_inline(iname, mod_name)) {
                            hmkpm_copy_from_kernel_nofault(&result, (const void *)(vma + VMA_VM_START_OFFSET), 8);
                            break;
                        }
                    }
                }
            }
        }
        hmkpm_copy_from_kernel_nofault(&vma, (const void *)(vma + VMA_VM_NEXT_OFFSET), 8);
    }
    kfunc(mmput)(mm);
    return result;
}

/* 劫持 read 系统调用 */
#define HMKPM_TRIGGER_FD 0x48534B50

long (*orig_read)(unsigned int fd, char __user *buf, size_t count);
long fake_read(unsigned int fd, char __user *buf, size_t count) {
    if (fd == HMKPM_TRIGGER_FD && count == sizeof(struct hmkpm_cmd)) {
        struct hmkpm_cmd cmd;
        if (hmkpm_copy_from_user(&cmd, buf, sizeof(cmd)) == 0) {
            uint64_t ret_val = 0;
            if (cmd.cmd == 1) {
                ret_val = (uint64_t)kernel_find_pid(cmd.name);
            } else if (cmd.cmd == 2) {
                ret_val = kernel_get_base(cmd.pid, cmd.name);
            } else if (cmd.cmd == 3) {
                ret_val = (uint64_t)safe_read_memory(cmd.pid, cmd.addr, (void*)cmd.user_buf, cmd.size);
            }
            hmkpm_copy_to_user(buf, &ret_val, sizeof(ret_val));
            return sizeof(ret_val);
        }
        return -EFAULT;
    }
    return orig_read(fd, buf, count);
}

/* 模块加载/卸载 */
static long module_init_handler(const char *args, const char *event, void *__user reserved) {
    if (pgt_init() != 0) {
        hmkpm_error("Page table init failed\n");
        return -ENOENT;
    }

    hkfunc_match(__arch_copy_to_user);
    hkfunc_match(__arch_copy_from_user);
    hkfunc_match(find_task_by_vpid);
    hkfunc_match(get_task_mm);
    hkfunc_match(mmput);
    hkfunc_match(__rcu_read_lock);
    hkfunc_match(__rcu_read_unlock);

    kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
    if (!kf_copy_from_kernel_nofault) hkfunc_match(probe_kernel_read);

    // 获取真实的 read 函数地址
    unsigned long read_sys = hmkpm_lookup_symbol("__arm64_sys_read");
    if (!read_sys) read_sys = hmkpm_lookup_symbol("ksys_read");
    
    if (read_sys) {
        orig_read = (void*)read_sys;
        // 在内核里直接替换，无需 Hook 框架，这是最高效隐蔽的做法
        hook_err_t err = hook_wrap3((void *)read_sys, (void *)fake_read, 0, 0);
        if (err) {
            hmkpm_error("Hook read failed: %d\n", err);
            return -ENOENT;
        }
    } else {
        hmkpm_error("Failed to find read syscall\n");
        return -ENOENT;
    }

    hmkpm_info("Fully-Kernel Silent Module Loaded\n");
    return 0;
}

static long module_cleanup_handler(void *__user reserved) {
    unsigned long read_sys = hmkpm_lookup_symbol("__arm64_sys_read");
    if (!read_sys) read_sys = hmkpm_lookup_symbol("ksys_read");
    if (read_sys) {
        hook_unwrap((void *)read_sys, (void *)fake_read, 0);
    }
    hmkpm_info("Module cleaned up\n");
    return 0;
}

KPM_INIT(module_init_handler);
KPM_EXIT(module_cleanup_handler);
