// SPDX-License-Identifier: GPL-2.0
#include <kpmodule.h>
#include <kputils.h>
#include <hook.h>
#include <syscall.h>
#include <linux/sched.h>
#include <linux/mm.h>
#include <linux/uaccess.h>
#include <linux/fs.h>
#include <linux/file.h>
#include <linux/fdtable.h>
#include <linux/dcache.h>
#include <linux/version.h>

// 【修复】移除 anon_inodes.h，手动声明内核符号
extern struct file_operations anon_inode_fops;
extern struct file *anon_inode_getfile(const char *name, const struct file_operations *fops, void *priv, int flags);
extern int get_unused_fd_flags(unsigned flags);
extern void put_unused_fd(unsigned int fd);
extern void fd_install(unsigned int fd, struct file *file);

KPM_NAME("com.sys.core"); // 伪装成系统核心组件
KPM_VERSION("1.0.0");
KPM_LICENSE("GPL v2");

#define AF_DECNET_VAL 12
#define CMD_GET_PID   0x1001
#define CMD_GET_BASE  0x1002
#define CMD_READ_MEM  0x1003

struct k_req {
    uint32_t cmd;
    uint32_t pid;
    uint64_t addr;
    uint64_t buf;
    uint64_t size;
    char name[64];
};

// ==================== 依赖符号解析 ====================
#define KF_FIND_TASK ((struct task_struct* (*)(pid_t))kallsyms_lookup_name("find_task_by_vpid"))
#define KF_GET_MM ((struct mm_struct* (*)(struct task_struct*))kallsyms_lookup_name("get_task_mm"))
#define KF_MMPUT ((void (*)(struct mm_struct*))kallsyms_lookup_name("mmput"))
#define KF_GET_CMDLINE ((int (*)(struct task_struct*, char*, int))kallsyms_lookup_name("get_cmdline"))
#define KF_PROBE_READ ((int (*)(void*, const void*, size_t))kallsyms_lookup_name("probe_kernel_read"))
#define KF_COPY_TO_USER ((unsigned long (*)(void __user*, const void*, unsigned long))kallsyms_lookup_name("__arch_copy_to_user"))
#define KF_COPY_FROM_USER ((unsigned long (*)(void*, const void __user*, unsigned long))kallsyms_lookup_name("__arch_copy_from_user"))

// 引入 hmkpm 原版的页表遍历函数 (确保你原工程里有这两个函数)
extern int pgt_pgtable_init(void);
extern uint64_t pgt_pgtable_to_tkpa(uint64_t pgd, uint64_t va, bool is_write);
extern uint64_t pgt_phys_to_virt(uint64_t phys);

// ==================== 核心 1：包名找 PID ====================
static pid_t do_find_pid(const char *name) {
    struct task_struct *p;
    char cmdline[256];
    size_t name_len = strlen(name);
    pid_t found_pid = -1;
    
    kfunc(__rcu_read_lock)();
    for_each_process(p) {
        if (p->mm == NULL) continue;
        cmdline[0] = '\0';
        if (KF_GET_CMDLINE && KF_GET_CMDLINE(p, cmdline, sizeof(cmdline)) > 0) {
            char *prog = cmdline;
            char *space = strrchr(cmdline, ' ');
            if (space) prog = space + 1;
            
            if (strncmp(prog, name, name_len) == 0 && strlen(prog) == name_len) {
                found_pid = p->pid;
                break;
            }
        }
    }
    kfunc(__rcu_read_unlock)();
    return found_pid;
}

// ==================== 核心 2：获取模块基址 ====================
static unsigned long do_get_base(pid_t pid, const char *name) {
    struct task_struct *task = KF_FIND_TASK(pid);
    if (!task) return 0;
    
    struct mm_struct *mm = KF_GET_MM(task);
    if (!mm) return 0;
    
    struct vm_area_struct *vma;
    unsigned long base = 0;
    size_t name_len = strlen(name);
    
    // 针对 6.1+ 和旧内核的 VMA 安全遍历
#if LINUX_VERSION_CODE >= KERNEL_VERSION(6, 1, 0)
    VMA_ITERATOR(vmi, mm, 0);
    for_each_vma(vmi, vma) {
#else
    for (vma = mm->mmap; vma; vma = vma->vm_next) {
#endif
        if (vma->vm_file) {
            const char *dname = vma->vm_file->f_path.dentry->d_name.name;
            if (dname && strncmp(dname, name, name_len) == 0) {
                base = vma->vm_start;
                break;
            }
        }
    }
    KF_MMPUT(mm);
    return base;
}

// ==================== 核心 3：物理内存直读 ====================
static bool do_read_physical(int pid, uint64_t va, void *buf, uint64_t size) {
    struct task_struct *task = KF_FIND_TASK(pid);
    if (!task) return false;
    
    struct mm_struct *mm = KF_GET_MM(task);
    if (!mm) return false;
    
    uint64_t pgd;
    // 注意：这里的 64 是 mm->pgd 的偏移（你的 hmkpm 里有动态解析 mm_struct_offset.pgd_offset，如有请替换）
    if (KF_PROBE_READ(&pgd, (void*)((uintptr_t)mm + 64), 8) != 0 || !pgd) {
        KF_MMPUT(mm);
        return false;
    }
    
    // 将虚拟地址翻译成物理地址
    uint64_t tkpa = pgt_pgtable_to_tkpa(pgd, va, false);
    if (!tkpa) {
        KF_MMPUT(mm);
        return false;
    }
    
    // 通过内核线性映射区读取物理内存数据
    void *kva = (void*)pgt_phys_to_virt(tkpa);
    KF_COPY_TO_USER(buf, kva, size);
    
    KF_MMPUT(mm);
    return true;
}

// ==================== 通信层：完美复刻 wuwa ====================

// 1. Hook socket：拦截 AF_DECnet
static void before_socket(hook_fargs3_t *args, void *udata) {
    int family = (int)syscall_argn(args, 0);
    int type = (int)syscall_argn(args, 1);

    if (family == AF_DECNET_VAL && type == SOCK_RAW) {
        args->skip_origin = 1;
        int fd = get_unused_fd_flags(O_CLOEXEC);
        if (fd >= 0) {
            struct file *filp = anon_inode_getfile("[net]", &anon_inode_fops, NULL, O_RDWR);
            if (!IS_ERR(filp)) {
                fd_install(fd, filp);
                args->ret = fd;
            } else {
                put_unused_fd(fd);
                args->ret = -EMFILE;
            }
        } else {
            args->ret = -EMFILE;
        }
    }
}

// 2. Hook ioctl：拦截通信指令
static void before_ioctl(hook_fargs3_t *args, void *udata) {
    unsigned int cmd = (unsigned int)syscall_argn(args, 1);
    void __user *arg = (void __user *)syscall_argn(args, 2);

    if (cmd < CMD_GET_PID || cmd > CMD_READ_MEM) return;

    args->skip_origin = 1;

    struct k_req req;
    if (KF_COPY_FROM_USER(&req, arg, sizeof(req)) != 0) {
        args->ret = -EFAULT;
        return;
    }

    if (cmd == CMD_GET_PID) {
        req.pid = do_find_pid(req.name);
        args->ret = (req.pid > 0) ? 0 : -ENOENT;
    } 
    else if (cmd == CMD_GET_BASE) {
        req.addr = do_get_base(req.pid, req.name);
        args->ret = (req.addr > 0) ? 0 : -ENOENT;
    } 
    else if (cmd == CMD_READ_MEM) {
        bool ok = do_read_physical(req.pid, req.addr, (void*)req.buf, req.size);
        args->ret = ok ? 0 : -EFAULT;
    }
    else {
        args->ret = -EINVAL;
    }

    // 将 pid 和 base 写回用户态
    if (args->ret == 0 && cmd != CMD_READ_MEM) {
        KF_COPY_TO_USER(arg, &req, sizeof(req));
    }
}

// ==================== KPM 生命周期 ====================
static long mod_init(const char *args, const char *event, void *__user reserved) {
    if (pgt_pgtable_init() != 0) return -1;

    hook_err_t err = hook_syscalln(__NR_socket, 3, before_socket, 0, 0);
    if (err) return err;

    err = hook_syscalln(__NR_ioctl, 3, before_ioctl, 0, 0);
    if (err) {
        unhook_syscalln(__NR_socket, before_socket, 0);
        return err;
    }
    return 0;
}

static long mod_exit(void *__user reserved) {
    unhook_syscalln(__NR_socket, before_socket, 0);
    unhook_syscalln(__NR_ioctl, before_ioctl, 0);
    return 0;
}

KPM_INIT(mod_init);
KPM_EXIT(mod_exit);
