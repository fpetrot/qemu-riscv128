/*
 * Copyright (C) 2021, Mahmoud Mandour <ma.mandourr@gmail.com>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */

#include <inttypes.h>
#include <stdio.h>
#include <glib.h>

#include <qemu-plugin.h>

/*
 * We use rdtime zero and rdcycle zero as start and stop markers
 * for plugin execution.
 * This allows to extract statistics for a well define subset of
 * instructions.
 * Note that launching in parallel programs that contains these
 * markers is probably the best way to obtain random numbers, ...
 */
#define MAGIC_OPCODE_START 0xc0102073
#define MAGIC_OPCODE_STOP 0xc0002073

#define STRTOLL(x) g_ascii_strtoll(x, NULL, 10)

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

static GHashTable *miss_ht;

static GMutex hashtable_lock;
static GRand *rng;

static int limit;
static bool sys;

enum EvictionPolicy {
    LRU,
    FIFO,
    RAND,
};

enum EvictionPolicy policy;

/*
 * A CacheSet is a set of cache blocks. A memory block that maps to a set can be
 * put in any of the blocks inside the set. The number of block per set is
 * called the associativity (assoc).
 *
 * Each block contains the stored tag and a valid bit. Since this is not
 * a functional simulator, the data itself is not stored. We only identify
 * whether a block is in the cache or not by searching for its tag.
 *
 * In order to search for memory data in the cache, the set identifier and tag
 * are extracted from the address and the set is probed to see whether a tag
 * match occur.
 *
 * An address is logically divided into three portions: The block offset,
 * the set number, and the tag.
 *
 * The set number is used to identify the set in which the block may exist.
 * The tag is compared against all the tags of a set to search for a match. If a
 * match is found, then the access is a hit.
 *
 * The CacheSet also contains bookkeaping information about eviction details.
 */

/*
 * All sets must share the same tagh, so, when adding or replacing a block,
 * check that its tagh matches the set tagh, otherwise invalidate all ways.
 */
typedef struct {
    uint64_t tagl;
    bool valid;
} CacheBlock;

typedef struct {
    uint64_t tagh;
    CacheBlock *blocks;
    uint64_t *lru_priorities;
    uint64_t lru_gen_counter;
    GQueue *fifo_queue;
} CacheSet;

typedef struct {
    CacheSet *sets;
    int num_sets;
    int cachesize;
    int assoc;
    int blksize_shift;
    uint64_t set_mask;
    uint64_t tagh_mask;
    uint64_t tagl_mask;
    uint64_t accesses;
    uint64_t misses;
    uint64_t invals;
} Cache;

typedef struct {
    char *disas_str;
    const char *symbol;
    uint64_t addr;
    uint64_t l1_dmisses;
    uint64_t l1_imisses;
    uint64_t l1_dinvals;
    uint64_t l1_iinvals;
    uint64_t l2_misses;
    uint64_t l2_invals;
} InsnData;

void (*update_hit)(Cache *cache, int set, int blk);
void (*update_miss)(Cache *cache, int set, int blk);

void (*metadata_init)(Cache *cache);
void (*metadata_destroy)(Cache *cache);

static int cores;
static Cache **l1_dcaches, **l1_icaches;

static bool use_l2;
static Cache **l2_ucaches;

static GMutex *l1_dcache_locks;
static GMutex *l1_icache_locks;
static GMutex *l2_ucache_locks;

static uint64_t l1_dmem_accesses;
static uint64_t l1_imem_accesses;
static uint64_t l1_imisses;
static uint64_t l1_dmisses;
static uint64_t l1_iinvals;
static uint64_t l1_dinvals;
static uint64_t l2_invals;

static uint64_t l2_mem_accesses;
static uint64_t l2_misses;

static bool use_magic_op;
static bool magic_op_found;
static void log_stats(bool reset);

static int pow_of_two(int num)
{
    g_assert((num & (num - 1)) == 0);
    int ret = 0;
    while (num /= 2) {
        ret++;
    }
    return ret;
}

/*
 * LRU evection policy: For each set, a generation counter is maintained
 * alongside a priority array.
 *
 * On each set access, the generation counter is incremented.
 *
 * On a cache hit: The hit-block is assigned the current generation counter,
 * indicating that it is the most recently used block.
 *
 * On a cache miss: The block with the least priority is searched and replaced
 * with the newly-cached block, of which the priority is set to the current
 * generation number.
 */

static void lru_priorities_init(Cache *cache)
{
    int i;

    for (i = 0; i < cache->num_sets; i++) {
        cache->sets[i].lru_priorities = g_new0(uint64_t, cache->assoc);
        cache->sets[i].lru_gen_counter = 0;
    }
}

static void lru_update_blk(Cache *cache, int set_idx, int blk_idx)
{
    CacheSet *set = &cache->sets[set_idx];
    set->lru_priorities[blk_idx] = cache->sets[set_idx].lru_gen_counter;
    set->lru_gen_counter++;
}

static int lru_get_lru_block(Cache *cache, int set_idx)
{
    int i, min_idx, min_priority;

    min_priority = cache->sets[set_idx].lru_priorities[0];
    min_idx = 0;

    for (i = 1; i < cache->assoc; i++) {
        if (cache->sets[set_idx].lru_priorities[i] < min_priority) {
            min_priority = cache->sets[set_idx].lru_priorities[i];
            min_idx = i;
        }
    }
    return min_idx;
}

static void lru_priorities_destroy(Cache *cache)
{
    int i;

    for (i = 0; i < cache->num_sets; i++) {
        g_free(cache->sets[i].lru_priorities);
    }
}

/*
 * FIFO eviction policy: a FIFO queue is maintained for each CacheSet that
 * stores accesses to the cache.
 *
 * On a compulsory miss: The block index is enqueued to the fifo_queue to
 * indicate that it's the latest cached block.
 *
 * On a conflict miss: The first-in block is removed from the cache and the new
 * block is put in its place and enqueued to the FIFO queue.
 */

static void fifo_init(Cache *cache)
{
    int i;

    for (i = 0; i < cache->num_sets; i++) {
        cache->sets[i].fifo_queue = g_queue_new();
    }
}

static int fifo_get_first_block(Cache *cache, int set)
{
    GQueue *q = cache->sets[set].fifo_queue;
    return GPOINTER_TO_INT(g_queue_pop_tail(q));
}

static void fifo_update_on_miss(Cache *cache, int set, int blk_idx)
{
    GQueue *q = cache->sets[set].fifo_queue;
    g_queue_push_head(q, GINT_TO_POINTER(blk_idx));
}

static void fifo_destroy(Cache *cache)
{
    int i;

    for (i = 0; i < cache->num_sets; i++) {
        g_queue_free(cache->sets[i].fifo_queue);
    }
}

static inline uint64_t extract_tagh(Cache *cache, uint64_t addr)
{
    return addr & cache->tagh_mask;
}

static inline uint64_t extract_tagl(Cache *cache, uint64_t addr)
{
    return addr & cache->tagl_mask;
}

static inline uint64_t extract_set(Cache *cache, uint64_t addr)
{
    return (addr & cache->set_mask) >> cache->blksize_shift;
}

static const char *cache_config_error(int blksize, int assoc, int cachesize)
{
    if (cachesize % blksize != 0) {
        return "cache size must be divisible by block size";
    } else if (cachesize % (blksize * assoc) != 0) {
        return "cache size must be divisible by set size (assoc * block size)";
    } else {
        return NULL;
    }
}

static bool bad_cache_params(int blksize, int assoc, int cachesize)
{
    return (cachesize % blksize) != 0 || (cachesize % (blksize * assoc) != 0);
}

static Cache *cache_init(int blksize, int assoc, int cachesize, int taglsize)
{
    Cache *cache;
    int i;
    uint64_t blk_mask;
    uint64_t tag_mask;
    uint64_t set_shift;

    /*
     * This function shall not be called directly, and hence expects suitable
     * parameters.
     */
    g_assert(!bad_cache_params(blksize, assoc, cachesize));

    cache = g_new(Cache, 1);
    cache->assoc = assoc;
    cache->cachesize = cachesize;
    cache->num_sets = cachesize / (blksize * assoc);
    cache->sets = g_new(CacheSet, cache->num_sets);
    set_shift = pow_of_two(cache->num_sets);
    cache->blksize_shift = pow_of_two(blksize);
    cache->accesses = 0;
    cache->misses = 0;
    cache->invals = 0;

    cache->set_mask = ((cache->num_sets - 1) << cache->blksize_shift);
    blk_mask = blksize - 1;
    tag_mask = ~(cache->set_mask | blk_mask);

    /* This is where the magic takes place */
    cache->tagh_mask = tag_mask & ~((1L << taglsize) - 1) << (set_shift + cache->blksize_shift);
    cache->tagl_mask = tag_mask & ((1L << taglsize) - 1) << (set_shift + cache->blksize_shift);

    for (i = 0; i < cache->num_sets; i++) {
        cache->sets[i].blocks = g_new0(CacheBlock, assoc);
    }

    if (metadata_init) {
        metadata_init(cache);
    }

    return cache;
}

static Cache **caches_init(int blksize, int assoc, int cachesize, int taglsize)
{
    Cache **caches;
    int i;

    if (bad_cache_params(blksize, assoc, cachesize)) {
        return NULL;
    }

    caches = g_new(Cache *, cores);

    for (i = 0; i < cores; i++) {
        caches[i] = cache_init(blksize, assoc, cachesize, taglsize);
    }

    return caches;
}

static int get_invalid_block(Cache *cache, uint64_t set)
{
    int i;

    for (i = 0; i < cache->assoc; i++) {
        if (!cache->sets[set].blocks[i].valid) {
            return i;
        }
    }

    return -1;
}

static int get_replaced_block(Cache *cache, int set)
{
    switch (policy) {
    case RAND:
        return g_rand_int_range(rng, 0, cache->assoc);
    case LRU:
        return lru_get_lru_block(cache, set);
    case FIFO:
        return fifo_get_first_block(cache, set);
    default:
        g_assert_not_reached();
    }
}

static int in_cache(Cache *cache, uint64_t addr)
{
    int i;
    uint64_t tagh, tagl, set;

    tagh = extract_tagh(cache, addr);
    tagl = extract_tagl(cache, addr);
    set = extract_set(cache, addr);

    if (cache->sets[set].tagh != tagh) {
        return -1;
    }

    for (i = 0; i < cache->assoc; i++) {
        if (cache->sets[set].blocks[i].tagl == tagl
            && cache->sets[set].blocks[i].valid) {
            return i;
        }
    }

    return -1;
}

/**
 * access_cache(): Simulate a cache access
 * @cache: The cache under simulation
 * @addr: The address of the requested memory location
 *
 * Returns 0 if the requested data is in the cache (hit) and 0b01 (miss with
 * simple replacement) or 0b11 (miss with invalidation and replacement) when not.
 * The cache is updated on miss for the next access.
 */
static int access_cache(Cache *cache, uint64_t addr)
{
    int hit_blk, replaced_blk, inval = 0;
    uint64_t tagh, tagl, set;

    tagh = extract_tagh(cache, addr);
    tagl = extract_tagl(cache, addr);
    set = extract_set(cache, addr);

    hit_blk = in_cache(cache, addr);
    if (hit_blk != -1) {
        if (update_hit) {
            update_hit(cache, set, hit_blk);
        }
        return 0;
    }

    /*
     * The sets must all share the same tagh by definition, so we have to
     * make sure it is still the case, otherwise we invalidate all ways
     */

    if (cache->sets[set].tagh != tagh) {
        for (int i = 0; i < cache->assoc; i++) {
            cache->sets[set].blocks[i].valid = false;
        }
        inval = 0b10;
        /* Update tagh as we know the data will be inserted there */
        cache->sets[set].tagh = tagh;
    }
    replaced_blk = get_invalid_block(cache, set);

    if (replaced_blk == -1) {
        replaced_blk = get_replaced_block(cache, set);
    }

    if (update_miss) {
        update_miss(cache, set, replaced_blk);
    }

    cache->sets[set].blocks[replaced_blk].tagl = tagl;
    cache->sets[set].blocks[replaced_blk].valid = true;

    return inval | 1;
}

static void vcpu_mem_access(unsigned int vcpu_index, qemu_plugin_meminfo_t info,
                            uint64_t vaddr, void *userdata)
{
    uint64_t effective_addr;
    struct qemu_plugin_hwaddr *hwaddr;
    int cache_idx;
    InsnData *insn;
    int miss;

    /* Needed if the tb has been translated beforehand */
    if (use_magic_op && !magic_op_found) {
        return;
    }

    hwaddr = qemu_plugin_get_hwaddr(info, vaddr);
    if (hwaddr && qemu_plugin_hwaddr_is_io(hwaddr)) {
        return;
    }

    effective_addr = hwaddr ? qemu_plugin_hwaddr_phys_addr(hwaddr) : vaddr;
    cache_idx = vcpu_index % cores;

    g_mutex_lock(&l1_dcache_locks[cache_idx]);
    miss = access_cache(l1_dcaches[cache_idx], effective_addr);
    if (miss) {
        insn = userdata;
        __atomic_fetch_add(&insn->l1_dmisses, 1, __ATOMIC_SEQ_CST);
        l1_dcaches[cache_idx]->misses++;
        if (miss & 0b10) {
            __atomic_fetch_add(&insn->l1_dinvals, 1, __ATOMIC_SEQ_CST);
            l1_dcaches[cache_idx]->invals++;
        }
    }
    l1_dcaches[cache_idx]->accesses++;
    g_mutex_unlock(&l1_dcache_locks[cache_idx]);

    if (!miss || !use_l2) {
        /* No need to access L2 */
        return;
    }

    g_mutex_lock(&l2_ucache_locks[cache_idx]);
    miss = access_cache(l2_ucaches[cache_idx], effective_addr);
    if (miss) {
        insn = userdata;
        __atomic_fetch_add(&insn->l2_misses, 1, __ATOMIC_SEQ_CST);
        l2_ucaches[cache_idx]->misses++;
        if (miss & 0b10) {
            __atomic_fetch_add(&insn->l2_invals, 1, __ATOMIC_SEQ_CST);
            l2_ucaches[cache_idx]->invals++;
        }
    }
    l2_ucaches[cache_idx]->accesses++;
    g_mutex_unlock(&l2_ucache_locks[cache_idx]);
}

static void vcpu_insn_exec(unsigned int vcpu_index, void *userdata)
{
    uint64_t insn_addr;
    InsnData *insn;
    int cache_idx;
    int miss;

    if (use_magic_op && !magic_op_found) {
        return;
    }

    insn_addr = ((InsnData *) userdata)->addr;

    cache_idx = vcpu_index % cores;
    g_mutex_lock(&l1_icache_locks[cache_idx]);
    miss = access_cache(l1_icaches[cache_idx], insn_addr);
    if (miss) {
        insn = userdata;
        __atomic_fetch_add(&insn->l1_imisses, 1, __ATOMIC_SEQ_CST);
        l1_icaches[cache_idx]->misses++;
        if (miss & 0b10) {
            __atomic_fetch_add(&insn->l1_iinvals, 1, __ATOMIC_SEQ_CST);
            l1_icaches[cache_idx]->invals++;
        }
    }
    l1_icaches[cache_idx]->accesses++;
    g_mutex_unlock(&l1_icache_locks[cache_idx]);

    if (!miss || !use_l2) {
        /* No need to access L2 */
        return;
    }

    g_mutex_lock(&l2_ucache_locks[cache_idx]);
    miss = access_cache(l2_ucaches[cache_idx], insn_addr);
    if (miss) {
        insn = userdata;
        __atomic_fetch_add(&insn->l2_misses, 1, __ATOMIC_SEQ_CST);
        l2_ucaches[cache_idx]->misses++;
        if (miss & 0b10) {
            __atomic_fetch_add(&insn->l2_invals, 1, __ATOMIC_SEQ_CST);
            l2_ucaches[cache_idx]->invals++;
        }
    }
    l2_ucaches[cache_idx]->accesses++;
    g_mutex_unlock(&l2_ucache_locks[cache_idx]);
}

static void vcpu_start_instrumentation(unsigned int vcpu_index, void *userdata)
{
    magic_op_found = true;
}

static void vcpu_stop_instrumentation(unsigned int vcpu_index, void *userdata)
{
    magic_op_found = false;
    log_stats(true);
}

static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
    size_t n_insns;
    size_t i;
    InsnData *data;

    n_insns = qemu_plugin_tb_n_insns(tb);
    for (i = 0; i < n_insns; i++) {
        struct qemu_plugin_insn *insn = qemu_plugin_tb_get_insn(tb, i);
        uint64_t effective_addr, opcode;
        if (use_magic_op) {
            qemu_plugin_insn_data(insn, &opcode, sizeof(opcode));
            switch (opcode) {
            case MAGIC_OPCODE_START:
                qemu_plugin_register_vcpu_insn_exec_cb(insn,
                                                       vcpu_start_instrumentation,
                                                       QEMU_PLUGIN_CB_NO_REGS,
                                                       NULL);
                magic_op_found = true;
                continue;
            case MAGIC_OPCODE_STOP:
                qemu_plugin_register_vcpu_insn_exec_cb(insn,
                                                       vcpu_stop_instrumentation,
                                                       QEMU_PLUGIN_CB_NO_REGS,
                                                       NULL);
                magic_op_found = false;
                return;
            default:
                break;
            }
        }

        if (use_magic_op && !magic_op_found) {
            return;
        }

        /* Assume vipt cache in full system emulation */
        if (sys) {
            effective_addr = (uint64_t) qemu_plugin_insn_haddr(insn);
        } else {
            effective_addr = (uint64_t) qemu_plugin_insn_vaddr(insn);
        }

        /*
         * Instructions might get translated multiple times, we do not create
         * new entries for those instructions. Instead, we fetch the same
         * entry from the hash table and register it for the callback again.
         */
        g_mutex_lock(&hashtable_lock);
        data = g_hash_table_lookup(miss_ht, GUINT_TO_POINTER(effective_addr));
        if (data == NULL) {
            data = g_new0(InsnData, 1);
            data->disas_str = qemu_plugin_insn_disas(insn);
            data->symbol = qemu_plugin_insn_symbol(insn);
            data->addr = effective_addr;
            g_hash_table_insert(miss_ht, GUINT_TO_POINTER(effective_addr),
                               (gpointer) data);
        }
        g_mutex_unlock(&hashtable_lock);

        qemu_plugin_register_vcpu_mem_cb(insn, vcpu_mem_access,
                                         QEMU_PLUGIN_CB_NO_REGS,
                                         QEMU_PLUGIN_MEM_RW, data);

        /* We should probably use a conditional plugin to accelerate stuff */
        qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec,
                                               QEMU_PLUGIN_CB_NO_REGS, data);
    }
}

static void insn_free(gpointer data)
{
    InsnData *insn = (InsnData *) data;
    g_free(insn->disas_str);
    g_free(insn);
}

static void cache_free(Cache *cache)
{
    for (int i = 0; i < cache->num_sets; i++) {
        g_free(cache->sets[i].blocks);
    }

    if (metadata_destroy) {
        metadata_destroy(cache);
    }

    g_free(cache->sets);
    g_free(cache);
}

static void caches_free(Cache **caches)
{
    int i;

    for (i = 0; i < cores; i++) {
        cache_free(caches[i]);
    }
}

static void append_stats_line(GString *line,
                              uint64_t l1_daccess, uint64_t l1_dmisses,  uint64_t l1_dinvals,
                              uint64_t l1_iaccess, uint64_t l1_imisses,  uint64_t l1_iinvals,
                              uint64_t l2_access, uint64_t l2_misses, uint64_t l2_invals)
{
    double l1_dmiss_rate = ((double) l1_dmisses) / (l1_daccess) * 100.0;
    double l1_imiss_rate = ((double) l1_imisses) / (l1_iaccess) * 100.0;

    g_string_append_printf(line,
                           "%-14" PRIu64 " %-12" PRIu64 " %9.4lf%%  %-14" PRIu64 "  "
                           "%-14" PRIu64 " %-12" PRIu64 " %9.4lf%%  %-14" PRIu64 "  ",
                           l1_daccess,
                           l1_dmisses,
                           l1_daccess ? l1_dmiss_rate : 0.0,
                           l1_dinvals,
                           l1_iaccess,
                           l1_imisses,
                           l1_iaccess ? l1_imiss_rate : 0.0,
                           l1_iinvals);

    if (l2_access && l2_misses) {
        double l2_miss_rate =  ((double) l2_misses) / (l2_access) * 100.0;
        g_string_append_printf(line,
                               "  %-12" PRIu64 " %-11" PRIu64 " %10.4lf%%  %-14" PRIu64,
                               l2_access,
                               l2_misses,
                               l2_miss_rate,
                               l2_invals);
    }

    g_string_append(line, "\n");
}

static void sum_stats(void)
{
    int i;

    g_assert(cores > 1);
    for (i = 0; i < cores; i++) {
        l1_imisses += l1_icaches[i]->misses;
        l1_iinvals += l1_icaches[i]->misses;
        l1_dmisses += l1_dcaches[i]->misses;
        l1_dinvals += l1_dcaches[i]->invals;
        l1_imem_accesses += l1_icaches[i]->accesses;
        l1_dmem_accesses += l1_dcaches[i]->accesses;

        if (use_l2) {
            l2_misses += l2_ucaches[i]->misses;
            l2_mem_accesses += l2_ucaches[i]->accesses;
            l2_invals += l2_ucaches[i]->invals;
        }
    }
}

static int dcmp(gconstpointer a, gconstpointer b)
{
    InsnData *insn_a = (InsnData *) a;
    InsnData *insn_b = (InsnData *) b;

    return insn_a->l1_dmisses < insn_b->l1_dmisses ? 1 : -1;
}

static int icmp(gconstpointer a, gconstpointer b)
{
    InsnData *insn_a = (InsnData *) a;
    InsnData *insn_b = (InsnData *) b;

    return insn_a->l1_imisses < insn_b->l1_imisses ? 1 : -1;
}

static int l2_cmp(gconstpointer a, gconstpointer b)
{
    InsnData *insn_a = (InsnData *) a;
    InsnData *insn_b = (InsnData *) b;

    return insn_a->l2_misses < insn_b->l2_misses ? 1 : -1;
}

static void log_stats(bool reset)
{
    int i;
    Cache *icache, *dcache, *l2_cache;

    g_autoptr(GString) rep = g_string_new("core #, data accesses, data misses,"
                                          " dmiss rate, dcache inval, insn accesses,"
                                          " insn misses, imiss rate, icache inval");

    if (use_l2) {
        g_string_append(rep, ", l2 accesses, l2 misses, l2 miss rate");
    }

    g_string_append(rep, "\n");

    for (i = 0; i < cores; i++) {
        g_string_append_printf(rep, "%-8d", i);
        dcache = l1_dcaches[i];
        icache = l1_icaches[i];
        l2_cache = use_l2 ? l2_ucaches[i] : NULL;
        append_stats_line(rep, dcache->accesses, dcache->misses, dcache->invals,
                icache->accesses, icache->misses, icache->invals,
                l2_cache ? l2_cache->accesses : 0,
                l2_cache ? l2_cache->misses : 0,
                l2_cache ? l2_cache->invals : 0);
        /*
         * Reinitialize stuff so that we can call this function several times
         * for our set of programs of the benchmark.
         */
        if (reset) {
            dcache->accesses = 0;
            dcache->misses = 0;
            dcache->invals = 0;
            icache->accesses = 0;
            icache->misses = 0;
            icache->invals = 0;
            if (l2_cache) {
                l2_cache->accesses = 0;
                l2_cache->misses = 0;
                l2_cache->invals = 0;
            }
        }
    }

    if (cores > 1) {
        sum_stats();
        g_string_append_printf(rep, "%-8s", "sum");
        append_stats_line(rep, l1_dmem_accesses, l1_dmisses, l1_dinvals,
                l1_imem_accesses, l1_imisses, l1_iinvals,
                l2_cache ? l2_mem_accesses : 0,
                l2_cache ? l2_misses : 0,
                l2_cache ? l2_invals : 0);
        /* Same as above */
        if (reset) {
            l1_dmem_accesses = 0;
            l1_dmisses = 0;
            l1_dinvals = 0;
            l1_imem_accesses = 0;
            l1_imisses = 0;
            l1_iinvals = 0;
            l2_mem_accesses = 0;
            l2_misses = 0;
            l2_invals = 0;
        }
    }

    g_string_append(rep, "\n");
    qemu_plugin_outs(rep->str);
}

static void log_top_insns(void)
{
    int i;
    GList *curr, *miss_insns;
    InsnData *insn;

    miss_insns = g_hash_table_get_values(miss_ht);
    miss_insns = g_list_sort(miss_insns, dcmp);
    g_autoptr(GString) rep = g_string_new("");
    g_string_append_printf(rep, "%s", "address, data misses, instruction\n");

    for (curr = miss_insns, i = 0; curr && i < limit; i++, curr = curr->next) {
        insn = (InsnData *) curr->data;
        g_string_append_printf(rep, "0x%" PRIx64, insn->addr);
        if (insn->symbol) {
            g_string_append_printf(rep, " (%s)", insn->symbol);
        }
        g_string_append_printf(rep, ", %" PRId64 ", %s\n",
                               insn->l1_dmisses, insn->disas_str);
    }

    miss_insns = g_list_sort(miss_insns, icmp);
    g_string_append_printf(rep, "%s", "\naddress, fetch misses, instruction\n");

    for (curr = miss_insns, i = 0; curr && i < limit; i++, curr = curr->next) {
        insn = (InsnData *) curr->data;
        g_string_append_printf(rep, "0x%" PRIx64, insn->addr);
        if (insn->symbol) {
            g_string_append_printf(rep, " (%s)", insn->symbol);
        }
        g_string_append_printf(rep, ", %" PRId64 ", %s\n",
                               insn->l1_imisses, insn->disas_str);
    }

    if (!use_l2) {
        goto finish;
    }

    miss_insns = g_list_sort(miss_insns, l2_cmp);
    g_string_append_printf(rep, "%s", "\naddress, L2 misses, instruction\n");

    for (curr = miss_insns, i = 0; curr && i < limit; i++, curr = curr->next) {
        insn = (InsnData *) curr->data;
        g_string_append_printf(rep, "0x%" PRIx64, insn->addr);
        if (insn->symbol) {
            g_string_append_printf(rep, " (%s)", insn->symbol);
        }
        g_string_append_printf(rep, ", %" PRId64 ", %s\n",
                               insn->l2_misses, insn->disas_str);
    }

finish:
#if 0
    qemu_plugin_outs(rep->str);
#endif
    g_list_free(miss_insns);
}

static void plugin_exit(qemu_plugin_id_t id, void *p)
{
    log_stats(false);
    log_top_insns();

    caches_free(l1_dcaches);
    caches_free(l1_icaches);

    g_free(l1_dcache_locks);
    g_free(l1_icache_locks);

    if (use_l2) {
        caches_free(l2_ucaches);
        g_free(l2_ucache_locks);
    }

    g_hash_table_destroy(miss_ht);
}

static void policy_init(void)
{
    switch (policy) {
    case LRU:
        update_hit = lru_update_blk;
        update_miss = lru_update_blk;
        metadata_init = lru_priorities_init;
        metadata_destroy = lru_priorities_destroy;
        break;
    case FIFO:
        update_miss = fifo_update_on_miss;
        metadata_init = fifo_init;
        metadata_destroy = fifo_destroy;
        break;
    case RAND:
        rng = g_rand_new();
        break;
    default:
        g_assert_not_reached();
    }
}

QEMU_PLUGIN_EXPORT
int qemu_plugin_install(qemu_plugin_id_t id, const qemu_info_t *info,
                        int argc, char **argv)
{
    int i;
    int l1_iassoc, l1_iblksize, l1_icachesize, l1_itaglsize;
    int l1_dassoc, l1_dblksize, l1_dcachesize, l1_dtaglsize;
    int l2_assoc, l2_blksize, l2_cachesize, l2_taglsize;

    limit = 32;
    sys = info->system_emulation;

    l1_dassoc = 8;
    l1_dblksize = 64;
    l1_dcachesize = l1_dblksize * l1_dassoc * 32;
    l1_dtaglsize = 53; /* Assuming a 64-bit address */

    l1_iassoc = 8;
    l1_iblksize = 64;
    l1_icachesize = l1_iblksize * l1_iassoc * 32;
    l1_itaglsize = 53;

    l2_assoc = 16;
    l2_blksize = 64;
    l2_cachesize = l2_assoc * l2_blksize * 2048;
    l2_taglsize = 45;

    policy = LRU;

    cores = sys ? info->system.smp_vcpus : 1;

    for (i = 0; i < argc; i++) {
        char *opt = argv[i];
        g_auto(GStrv) tokens = g_strsplit(opt, "=", 2);

        if (g_strcmp0(tokens[0], "iblksize") == 0) {
            l1_iblksize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "iassoc") == 0) {
            l1_iassoc = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "icachesize") == 0) {
            l1_icachesize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "itaglsize") == 0) {
            l1_itaglsize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "dblksize") == 0) {
            l1_dblksize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "dassoc") == 0) {
            l1_dassoc = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "dcachesize") == 0) {
            l1_dcachesize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "dtaglsize") == 0) {
            l1_dtaglsize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "limit") == 0) {
            limit = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "cores") == 0) {
            cores = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "l2cachesize") == 0) {
            use_l2 = true;
            l2_cachesize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "l2blksize") == 0) {
            use_l2 = true;
            l2_blksize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "l2assoc") == 0) {
            use_l2 = true;
            l2_assoc = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "l2taglsize") == 0) {
            use_l2 = true;
            l2_taglsize = STRTOLL(tokens[1]);
        } else if (g_strcmp0(tokens[0], "l2") == 0) {
            if (!qemu_plugin_bool_parse(tokens[0], tokens[1], &use_l2)) {
                fprintf(stderr, "boolean argument parsing failed: %s\n", opt);
                return -1;
            }
        } else if (g_strcmp0(tokens[0], "replace") == 0) {
            if (g_strcmp0(tokens[1], "rand") == 0) {
                policy = RAND;
            } else if (g_strcmp0(tokens[1], "lru") == 0) {
                policy = LRU;
            } else if (g_strcmp0(tokens[1], "fifo") == 0) {
                policy = FIFO;
            } else {
                fprintf(stderr, "invalid replacement policy: %s\n", opt);
                return -1;
            }
        } else if (g_strcmp0(tokens[0], "magic") == 0) {
            if (!qemu_plugin_bool_parse(tokens[0], tokens[1], &use_magic_op)) {
                fprintf(stderr, "boolean argument parsing failed: %s\n", opt);
                return -1;
            }
        } else {
            fprintf(stderr, "option parsing failed: %s\n", opt);
            return -1;
        }
    }

    policy_init();

    l1_dcaches = caches_init(l1_dblksize, l1_dassoc, l1_dcachesize, l1_dtaglsize);
    if (!l1_dcaches) {
        const char *err = cache_config_error(l1_dblksize, l1_dassoc, l1_dcachesize);
        fprintf(stderr, "dcache cannot be constructed from given parameters\n");
        fprintf(stderr, "%s\n", err);
        return -1;
    }

    l1_icaches = caches_init(l1_iblksize, l1_iassoc, l1_icachesize, l1_itaglsize);
    if (!l1_icaches) {
        const char *err = cache_config_error(l1_iblksize, l1_iassoc, l1_icachesize);
        fprintf(stderr, "icache cannot be constructed from given parameters\n");
        fprintf(stderr, "%s\n", err);
        return -1;
    }

    l2_ucaches = use_l2 ? caches_init(l2_blksize, l2_assoc, l2_cachesize, l2_taglsize) : NULL;
    if (!l2_ucaches && use_l2) {
        const char *err = cache_config_error(l2_blksize, l2_assoc, l2_cachesize);
        fprintf(stderr, "L2 cache cannot be constructed from given parameters\n");
        fprintf(stderr, "%s\n", err);
        return -1;
    }

    l1_dcache_locks = g_new0(GMutex, cores);
    l1_icache_locks = g_new0(GMutex, cores);
    l2_ucache_locks = use_l2 ? g_new0(GMutex, cores) : NULL;

    qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

    miss_ht = g_hash_table_new_full(NULL, g_direct_equal, NULL, insn_free);

    return 0;
}
