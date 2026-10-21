// SPDX-License-Identifier: GPL-2.0
/*
 * Copyright (c) 2026 Yervant7
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
#define HMKPM_VERSION_STR	"2.8.0-netlink-pure"

KPM_NAME("HMKPM");
KPM_VERSION(HMKPM_VERSION_STR);
KPM_LICENSE("GPL v2");
KPM_AUTHOR("Yervant7");
KPM_DESCRIPTION("HMKPM Netlink Pure Build");

static bool hook_active = true;
static bool init_error = false;
static int mmap_lock_sem_offset = -1;

#define U64_MAX				((u64)~0ULL)
#define HMKPM_TAG			"[HMKPM] "

#define hmkpm_info(fmt, ...)        logki(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_warn(fmt, ...)        logkw(HMKPM_TAG fmt, ##__VA_ARGS__)
#define hmkpm_error(fmt, ...)       logke(HMKPM_TAG fmt, ##__VA_ARGS__)

// 手写字符串函数
static int hmkpm_strlen(const char *s) {
    int len = 0; while (s[len]) len++; return len;
}
static int hmkpm_strstr(const char *haystack, const char *needle) {
    if (!*needle) return 1;
    for (; *haystack; ++haystack) {
        const char *h = haystack; const char *n = needle;
        while (*h && *n && *h == *n) { h++; n++; }
        if (!*n) return 1;
    }
    return 0;
}

static inline void make_cfi_name(char *dst, size_t dst_size, const char *name) {
	const char *suffix = ".cfi_jt";
	size_t i = 0;
	while (name && *name && i + 1 < dst_size) dst[i++] = *name++;
	while (*suffix && i + 1 < dst_size) dst[i++] = *suffix++;
	dst[i] = '\0';
}

static unsigned long hmkpm_lookup_symbol(const char *name) {
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

#define hkfunc_match(func) do { \
	kf_##func = (typeof(kf_##func))hmkpm_lookup_symbol(#func); \
	if (!kf_##func) { hmkpm_error("Failed to find kfunc %s\n", #func); init_error = true; } \
} while (0)

#define hkvar_match(var) do { \
	kv_##var = (typeof(kv_##var))hmkpm_lookup_symbol(#var); \
	if (!kv_##var) { hmkpm_error("Failed to find kvar %s\n", #var); init_error = true; } \
} while (0)

void *kfunc_def(memset)(void *s, int c, size_t count);
unsigned long kfunc_def(__arch_copy_to_user)(void __user *to, const void *from, unsigned long n);
unsigned long kfunc_def(__arch_copy_from_user)(void *to, const void __user *from, unsigned long n);
long kfunc_def(probe_kernel_read)(void *dst, const void *src, size_t size);
struct task_struct *kfunc_def(find_task_by_vpid)(pid_t pid);
struct mm_struct *kfunc_def(get_task_mm)(struct task_struct *task);
void kfunc_def(mmput)(struct mm_struct *mm);
void kfunc_def(__rcu_read_lock)(void);
void kfunc_def(__rcu_read_unlock)(void);

u64 kvar_def(memstart_addr);
void *kvar_def(high_memory);

// ============================================================
// 页表遍历核心
// ============================================================
static uint64_t pgt_va_bits, pgt_page_offset, pgt_linear_voffset;
static uint64_t pgt_page_shift, pgt_page_size, pgt_pgd_align_mask, pgt_pgd_size;
static uint64_t pgt_page_level, pgt_high_memory;

static inline uint64_t pgt_phys_to_virt(uint64_t phys) { return phys + pgt_linear_voffset; }

static inline uint64_t pgt_desc_to_phys(uint64_t desc) {
    return desc & (((1ULL << (48 - pgt_page_shift)) - 1) << pgt_page_shift);
}

static uint64_t pgt_walk(uint64_t pgd, uint64_t va) {
    uint64_t table_va = pgd, pxd_bits = pgt_page_shift - 3, pxd_ptrs = 1ULL << pxd_bits;
    int64_t start = 4 - (int64_t)pgt_page_level;

    if (!pgd || (pgd & pgt_pgd_align_mask)) return 0;
    va &= 0x00FFFFFFFFFFFFFFULL;

    for (int64_t lv = start; lv < 4; lv++) {
        if (table_va < pgt_page_offset || table_va >= pgt_high_memory) return 0;
        uint64_t pxd_shift = pxd_bits * (4 - lv) + 3;
        uint64_t pxd_index = (va >> pxd_shift) & (pxd_ptrs - 1);
        uint64_t desc = 0;
        if (kfunc(probe_kernel_read)(&desc, (void *)(table_va + pxd_index * 8), 8) != 0) return 0;
        
        uint64_t type = desc & 3ULL;
        if (type == 0 || type == 2) return 0;

        if (lv == 3) {
            if (type != 3) return 0;
            uint64_t base = pgt_desc_to_phys(desc);
            return base ? (base | (va & (pgt_page_size - 1))) : 0;
        }

        if (type == 1) {
            uint64_t block_bits = (uint64_t)(3 - lv) * pxd_bits + pgt_page_shift;
            uint64_t block_size = 1ULL << block_bits;
            uint64_t base = pgt_desc_to_phys(desc);
            return base ? ((base & ~(block_size - 1)) | (va & (block_size - 1))) : 0;
        }
        table_va = pgt_phys_to_virt(pgt_desc_to_phys(desc));
    }
    return 0;
}

static int pgt_init(void) {
    uint64_t tcr_el1;
    asm volatile("mrs %0, tcr_el1" : "=r"(tcr_el1));
    pgt_va_bits = 64 - (tcr_el1 & 0x3F);
    uint64_t tg0 = (tcr_el1 >> 14) & 3;
    pgt_page_shift = (tg0 == 0) ? 12 : 14;
    
    uint64_t pxd_bits = pgt_page_shift - 3;
    pgt_page_level = (pgt_va_bits - 4) / pxd_bits;
    pgt_page_size = 1ULL << pgt_page_shift;
    pgt_pgd_size = pgt_page_size;
    pgt_pgd_align_mask = pgt_page_size - 1;

    uint64_t va1_bits = 64 - ((tcr_el1 >> 16) & 0x3F);
    pgt_page_offset = -(UL(1) << va1_bits);

    unsigned long ms_addr = hmkpm_lookup_symbol("memstart_addr");
    unsigned long hm_addr = hmkpm_lookup_symbol("high_memory");
    if (!ms_addr || !hm_addr) {
        hmkpm_error("memstart_addr or high_memory not found\n");
        return -1;
    }
    
    uint64_t ms = 0, hm = 0;
    kfunc(probe_kernel_read)(&ms, (void*)ms_addr, 8);
    kfunc(probe_kernel_read)(&hm, (void*)hm_addr, 8);

    pgt_linear_voffset = pgt_page_offset - ms;
    pgt_high_memory = hm;
    return 0;
}

static ssize_t pgt_rw(pid_t pid, uint64_t remote_va, size_t len, void __user *local_buf, bool is_write) {
    struct task_struct *task = NULL; struct mm_struct *mm = NULL;
    ssize_t total = 0; uint64_t pgd = 0;
    uint8_t bounce[256];
    if (pid <= 0) return -EINVAL;

    kfunc(__rcu_read_lock)(); 
    task = kfunc(find_task_by_vpid)(pid);
    if (!task) { kfunc(__rcu_read_unlock)(); return -ESRCH; }
    mm = kfunc(get_task_mm)(task); 
    kfunc(__rcu_read_unlock)();
    if (!mm) return -ESRCH;

    if (kfunc(probe_kernel_read)(&pgd, (const void *)((uintptr_t)mm + mm_struct_offset.pgd_offset), 8) != 0 || !pgd) {
        kfunc(mmput)(mm);
        return -EFAULT;
    }

    while (len > 0) {
        unsigned long page_off = remote_va & (pgt_page_size - 1);
        size_t page_left = (size_t)(pgt_page_size - page_off);
        size_t chunk = len < page_left ? len : page_left;
        chunk = chunk < 256 ? chunk : 256;

        uint64_t tkpa = pgt_walk(pgd, remote_va);
        if (!tkpa) { if (total > 0) break; kfunc(mmput)(mm); return -EFAULT; }
        void *tkva = (void *)pgt_phys_to_virt(tkpa);
        
        unsigned long not_copied = kfunc(__arch_copy_to_user)(local_buf, tkva, chunk);
        if (not_copied) { total += (chunk - not_copied); break; }

        total += chunk; local_buf = (void __user *)((uintptr_t)local_buf + chunk); remote_va += chunk; len -= chunk;
    }
    kfunc(mmput)(mm);
    return total;
}

// ============================================================
// Netlink 通信层
// ============================================================
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

static void netlink_recv(struct sk_buff *skb) {
    if (!skb) return;
    char *skb_data = NULL;
    if (kfunc(probe_kernel_read)(&skb_data, (char*)skb + 0xD8, 8) != 0 || !skb_data) return;

    struct nlmsghdr *nlh = (struct nlmsghdr *)skb_data;
    if (nlh->nlmsg_len < sizeof(struct hmkpm_nl_req)) return;

    struct hmkpm_nl_req *req = (struct hmkpm_nl_req *)NLMSG_DATA(nlh);
    uint32_t user_pid = nlh->nlmsg_pid;
    uint64_t result = 0;

    if (nlh->nlmsg_type == HMKPM_NL_CMD_READ) {
        if (req->pid > 0) {
            uintptr_t clean_buf = (uintptr_t)req->user_buf & 0x00FFFFFFFFFFFFFFULL;
            long r = pgt_rw((pid_t)req->pid, req->addr, req->size, (void __user *)clean_buf, false);
            result = (r == req->size) ? 0 : (uint64_t)-1;
        }
    } 
    else if (nlh->nlmsg_type == HMKPM_NL_CMD_GET_PID) {
        // 遍历所有进程找 PID
        for (int i = 1; i < 32768; i++) {
            struct task_struct *task = NULL;
            struct mm_struct *mm = NULL;
            kfunc(__rcu_read_lock)(); 
            task = kfunc(find_task_by_vpid)(i);
            if (task) mm = kfunc(get_task_mm)(task);
            kfunc(__rcu_read_unlock)();

            if (mm) {
                // ★ 绝对无偏移依赖：直接读 mm->arg_start (5.10 内核固定偏移 0x2B0)
                uint64_t arg_start = 0;
                kfunc(probe_kernel_read)(&arg_start, (const void *)((uintptr_t)mm + 0x2B0), 8);
                if (arg_start) {
                    char kbuf[128] = {0};
                    // 用我们强大的物理直读，去读进程的用户态栈参数！
                    if (pgt_rw(i, arg_start, 127, (void __user *)kbuf, false) > 0) {
                        // 看完整命令行里有没有我们要找的包名
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
            // 遍历 VMA 链表
            uintptr_t vma = 0;
            kfunc(probe_kernel_read)(&vma, (const void *)((uintptr_t)mm + 0x000), 8);
            while (vma) {
                uintptr_t file = 0;
                kfunc(probe_kernel_read)(&file, (const void *)(vma + 0x0A0), 8); // vm_file 偏移
                if (file) {
                    uintptr_t dentry = 0;
                    kfunc(probe_kernel_read)(&dentry, (const void *)(file + 0x018 + 8), 8); // d_path -> dentry
                    if (dentry) {
                        char iname[32] = {0};
                        kfunc(probe_kernel_read)(iname, (const void *)(dentry + 0x038), 31); // d_iname
                        if (hmkpm_strstr(iname, req->mod_name)) { 
                            kfunc(probe_kernel_read)(&result, (const void *)(vma + 0x000), 8); // vm_start
                            break; 
                        }
                    }
                }
                uintptr_t next_vma = 0;
                kfunc(probe_kernel_read)(&next_vma, (const void *)(vma + 0x008), 8); // vm_next
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

static long module_init_handler(const char *args, const char *event, void *__user reserved) {
    hmkpm_info("Module init started\n");

    kf_memset = (void*)hmkpm_lookup_symbol("memset");
    kf___arch_copy_to_user = (void*)hmkpm_lookup_symbol("__arch_copy_to_user");
    kf___arch_copy_from_user = (void*)hmkpm_lookup_symbol("__arch_copy_from_user");
    kf_probe_kernel_read = (void*)hmkpm_lookup_symbol("probe_kernel_read");
    kf_find_task_by_vpid = (void*)hmkpm_lookup_symbol("find_task_by_vpid");
    kf_get_task_mm = (void*)hmkpm_lookup_symbol("get_task_mm");
    kf_mmput = (void*)hmkpm_lookup_symbol("mmput");
    kf___rcu_read_lock = (void*)hmkpm_lookup_symbol("__rcu_read_lock");
    kf___rcu_read_unlock = (void*)hmkpm_lookup_symbol("__rcu_read_unlock");

    if (pgt_init() != 0) return -ENOENT;
    if (netlink_init() != 0) return -ENOENT;

    hmkpm_info("Module loaded successfully!\n");
    return 0;
}

static long module_exit_handler(void *__user reserved) {
    hmkpm_info("Module exiting\n");
    return 0;
}

KPM_INIT(module_init_handler);
KPM_EXIT(module_exit_handler);
