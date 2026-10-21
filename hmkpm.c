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
#define HMKPM_VERSION_CODE	(((uint32_t)HMKPM_VERSION_MAJOR << 16) | \
				 ((uint32_t)HMKPM_VERSION_MINOR << 8) | \
				 ((uint32_t)HMKPM_VERSION_PATCH))
#define HMKPM_VERSION_STR	"2.8.0-netlink"

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
    if (!i) return false;
    sb = (const struct super_block_min *)READ_ONCE(i->i_sb);
    if (!sb) return false;
    return (READ_ONCE(sb->s_magic) == PROC_SUPER_MAGIC);
}

static void before_fsnotify(hook_fargs7_t *args, void *udata)
{
    struct inode *dir;
    struct inode *inode;
    struct inode *target;
    if (!READ_ONCE(hook_active) || !args) return;
    dir   = (struct inode *)args->arg3;
    inode = (struct inode *)args->arg5;
    target = inode ? inode : dir;
    if (!target) return;
    if (is_proc_inode(target)) {
        args->skip_origin = 1;
        args->ret = 0;
    }
}

// --- 以下为原版逻辑保留 ---
#define HMKPM_MAGIC			0x484D4B504DULL /* "HMKPM" */
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
#define HMKPM_ALL_FEATURES		(HMKPM_FEATURE_READ | HMKPM_FEATURE_WRITE | \
					 HMKPM_FEATURE_READ_BATCH | HMKPM_FEATURE_WRITE_BATCH | \
					 HMKPM_FEATURE_V2P_BATCH | HMKPM_FEATURE_SCAN_KERNEL)

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
	HMKPM_SCAN_TYPE_I8	= 1, HMKPM_SCAN_TYPE_U8	= 2, HMKPM_SCAN_TYPE_I16	= 3,
	HMKPM_SCAN_TYPE_U16	= 4, HMKPM_SCAN_TYPE_I32	= 5, HMKPM_SCAN_TYPE_U32	= 6,
	HMKPM_SCAN_TYPE_I64	= 7, HMKPM_SCAN_TYPE_U64	= 8, HMKPM_SCAN_TYPE_F32	= 9,
	HMKPM_SCAN_TYPE_F64	= 10, HMKPM_SCAN_TYPE_BYTES	= 11,
};

enum hmkpm_scan_op {
	HMKPM_SCAN_OP_EXACT	= 1, HMKPM_SCAN_OP_RANGE	= 2, HMKPM_SCAN_OP_MASK	= 3,
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

// 保留原版的页表遍历结构体与函数，这里省略未贴出的部分，请把原来 2.8.0 版本的 pgt_pgtable_to_tkpa、pgt_pgtable_init、pgt_rw_mm、pgt_rw 等所有函数原封不动保留！！

// ========== Netlink 通信层插入 ==========
struct sock;
struct sk_buff;
struct nlmsghdr {
    uint32_t nlmsg_len;
    uint16_t nlmsg_type;
    uint16_t nlmsg_flags;
    uint32_t nlmsg_seq;
    uint32_t nlmsg_pid;
};
#define NLMSG_HDRLEN ((int)((sizeof(struct nlmsghdr)+3)&~3))
#define NLMSG_LENGTH(len) ((len) + NLMSG_HDRLEN)
#define NLMSG_SPACE(len) (((NLMSG_LENGTH(len))+3)&~3)
#define NLMSG_DATA(nlh) ((void*)(((char*)nlh) + NLMSG_LENGTH(0)))

struct netlink_kernel_cfg {
    unsigned int groups;
    void (*input)(struct sk_buff *skb);
    void *cb_mutex;
    void *bind;
    void *unbind;
};

static struct sock *(*kf_netlink_create)(void *net, int unit, void *module, struct netlink_kernel_cfg *cfg);
static int (*kf_netlink_unicast)(struct sock *ssk, struct sk_buff *skb, uint32_t portid, int nonblock);
static void *(*kf_alloc_skb)(unsigned int size, int gfp_mask);
static void *(*kf_skb_put)(struct sk_buff *skb, unsigned int len);
static void *kv_init_net = NULL;
static struct sock *g_nl_sk = NULL;

struct hmkpm_nl_req {
    int32_t pid;
    uint32_t _pad;
    uint64_t addr;
    uint64_t size;
    uint64_t user_buf;
};

static void netlink_recv(struct sk_buff *skb) {
    if (!skb) return;
    char *skb_data = NULL;
    if (kfunc(probe_kernel_read)(&skb_data, (char*)skb + 0xD8, 8) != 0 || !skb_data) return;

    struct nlmsghdr *nlh = (struct nlmsghdr *)skb_data;
    if (nlh->nlmsg_len < sizeof(struct hmkpm_nl_req)) return;

    struct hmkpm_nl_req *req = (struct hmkpm_nl_req *)NLMSG_DATA(nlh);
    uint32_t user_pid = nlh->nlmsg_pid;

    long ret = -1;
    if (req->pid > 0) {
        // 直接调用你原版里就有的 pgt_rw 函数
        ssize_t r = pgt_rw((pid_t)req->pid, req->addr, req->size, (void __user *)(uintptr_t)req->user_buf, false);
        if (r == req->size) ret = 0;
    }

    if (kf_alloc_skb && kf_netlink_unicast && kf_skb_put) {
        struct sk_buff *skb_out = kf_alloc_skb(32, 0); 
        if (skb_out) {
            struct nlmsghdr *nlh_out = (struct nlmsghdr *)kf_skb_put(skb_out, NLMSG_SPACE(4));
            nlh_out->nlmsg_len = NLMSG_SPACE(4);
            nlh_out->nlmsg_type = 0;
            nlh_out->nlmsg_pid = 0;
            *(int*)NLMSG_DATA(nlh_out) = (int)ret;
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
        hmkpm_error("Netlink symbols missing\n");
        return -1;
    }

    struct netlink_kernel_cfg cfg;
    memset(&cfg, 0, sizeof(cfg));
    cfg.input = netlink_recv;

    g_nl_sk = kf_netlink_create(kv_init_net, 31, NULL, &cfg);
    if (!g_nl_sk) {
        hmkpm_error("Netlink create failed on proto 31\n");
        return -1;
    }
    hmkpm_info("Netlink registered on 31\n");
    return 0;
}
// ========== Netlink 层结束 ==========

// ... 省略了原版的大量 handle 函数 (hmkpm_handle_single, hmkpm_handle_batch, hmkpm_handle 等) ...

static long module_init_handler(const char *args, const char *event, void *__user reserved)
{
	hook_err_t err;

	if (kver < VERSION(4, 0, 0) || kver >= VERSION(6, 13, 0)) return -EINVAL;
	if (pgt_pgtable_init() != 0) return -ENOENT;
	hmkpm_sw_pan_init();

	static const char *const arm64_memset_aliases[] = { "__memset", "memset", "__pi___memset", "__pi_memset", "__asan_memset", "__hwasan_memset", "__mte_memset", "__arch_memset", NULL };
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

	hkfunc_match(find_task_by_vpid);
	hkfunc_match(get_task_mm);
	hkfunc_match(mmput);
	hkfunc_match(__rcu_read_lock);
	hkfunc_match(__rcu_read_unlock);

	kf_copy_from_kernel_nofault = (typeof(kf_copy_from_kernel_nofault))hmkpm_lookup_symbol("copy_from_kernel_nofault");
	if (!kf_copy_from_kernel_nofault) hkfunc_match(probe_kernel_read);

	kf_copy_to_kernel_nofault = (typeof(kf_copy_to_kernel_nofault))hmkpm_lookup_symbol("copy_to_kernel_nofault");
	if (!kf_copy_to_kernel_nofault) hkfunc_match(probe_kernel_write);

	mmap_lock_sem_offset = get_mm_mmap_lock_offset();
	if (init_error) return -ENOENT;

    // ★ 第一步：先执行原版的 hook，这是让 KPM 加载器认可模块的“投名状”
	if (kver >= VERSION(5, 10, 0)) {
		fsnotify_addr = hmkpm_lookup_symbol("fsnotify");
		if (fsnotify_addr) {
			err = hook_wrap7((void *)fsnotify_addr, before_fsnotify, 0, 0);
			if (!err) fsnotify_hooked = true;
		}
	}

	err = hook_syscalln(__NR_getresuid, 3, (void *)hmkpm_handle, 0, 0);
	if (err) return -ENOENT;

    // ★ 第二步：偷偷注册 Netlink（即使这里失败，也不影响 KPM 成功加载）
    if (netlink_init() != 0) {
        hmkpm_warn("Netlink init failed, but KPM loaded via Syscall hook.\n");
    }

	hmkpm_info("module loaded successfully\n");
	return 0;
}

// ... 保留原版的 module_control_handler 和 module_cleanup_handler ...

KPM_INIT(module_init_handler);
KPM_CTL0(module_control_handler);
KPM_EXIT(module_cleanup_handler);
