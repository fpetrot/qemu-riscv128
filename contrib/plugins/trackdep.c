/*
 * Very much inspired by the execlog plugin
 * Copyright (C) 2021, Alexandre Iooss <erdnaxe@crans.org>
 *
 * (not so) quick and dirty hack to track address registers dependencies
 * Copyright (C) 2022, Frederic Pétrot <frederic.petrot@univ-grenoble-alpes.fr>
 *
 * License: GNU GPL, version 2 or later.
 *   See the COPYING file in the top-level directory.
 */
#include <glib.h>
#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <assert.h>

#include <qemu-plugin.h>

QEMU_PLUGIN_EXPORT int qemu_plugin_version = QEMU_PLUGIN_VERSION;

/* Arrays of insns having the same way to handle registers:
 * Not so bright, but ok for a simple experiment. */
const char *rv_fmt_rd_rs1_rs2[] = {
    "add", "sub", "sll", "slt", "sltu", "xor", "srl", "sra", "or", "and",
    "addw", "subw", "sllw", "srlw", "sraw", "addd", "subd", "slld", "srld",
    "srad", "mul", "mulh", "mulhsu", "mulhu", "div", "divu", "rem", "remu",
    "mulw", "divw", "divuw", "remw", "remuw", "muld", "divd", "divud", "remd",
    "remud", NULL
};

const char *rv_fmt_rd_imm[] = {
    "lui", "auipc", "jal", NULL
};

const char *rv_fmt_rd_rs1_imm[] = {
    "jalr", "addi", "slti", "sltiu", "xori", "ori", "andi", "slli", "srli",
    "srai", "addiw", "slliw", "srliw", "sraiw", "addid", "sllid", "srlid",
    "sraid", NULL
};

const char *rv_fmt_rs1_rs2_offset[] = {
    "beq", "bne", "blt", "bge", "bltu", "bgeu", NULL
};

const char *rv_fmt_rd_offset_rs1[] = {
    "lb", "lh", "lw", "lbu", "lhu", "lwu", "ld", "ldu", "lq", NULL
};

const char *rv_fmt_rs2_offset_rs1[] = {
    "sb", "sh", "sw", "sd", "sq", NULL
};

const char *rv_fmt_aqrl_rd_rs1[] = {
    "lr", NULL
};

const char *rv_fmt_aqrl_rd_rs2_rs1[] = {
    "sc", "amoswap", "amoadd", "amoxor", "amoor", "amoand", "amomin", "amomax",
    "amominu", "amomaxu", NULL
};

const char *rv_fmt_rs1_rs2[] = {
    "sfence", NULL
};

const char *rv_fmt_rd_csr_rs1[] = {
    "csrrw", "csrrs", "csrrc", NULL
};

const char *rv_fmt_rd_csr_zimm[] = {
    "csrrwi", "csrrsi", "csrrci", NULL
};

const char *rv_fmt_frd_offset_rs1[] = {
    "flw", "fld", "flq", NULL
};

const char *rv_fmt_frs2_offset_rs1[] = {
    "fsw", "fsd", "fsq", NULL
};

const char *rv_fmt_fp[] = {
    "fmadd", "fmsub", "fnmsub", "fnmadd", "fadd", "fsub", "fmul",
    "fdiv", "fsgnj", "fsgnjn", "fsgnjx", "fmin", "fmax", "fsqrt",

    /*
     * The following instructions make use of integer registers, but in such
     * a way that it should *never* be used to contain an address.
     * So for now just consider them as skippable.
     */
    "fle", "flt", "feq", "fcvt", "fmv", "fclass", NULL
};


const char *rv_fmt_none[] = {
    "illegal", "fence", "fence", "ecall", "ebreak",
    "uret", "sret", "hret", "mret", "dret", "wfi", NULL
};

/*
 * Indicates that we know for sure that a reg contains an address
 * because it is one of these instructions:
 * - ld/st/lr/sc/amos/sfence : rs1 contains the address
 *   We have to traverse back the dependency tree to a 
 *   lui/auipc/jal/jalr that sets rd through dependencies
 */
typedef enum {
    none = 0,
    rd   = 1,
    rs1  = 2,
    rs2  = 4
} rop;

typedef struct insnregs {
    rop      addr:4; /* Which registers contain an address, if any */
    int8_t   rd;
    int8_t   rs1;
    int8_t   rs2;
    char     *insn;
    uint64_t vaddr;                                                        
} insnregs;

static const char rv_ireg_name[32][5] = {
    "zero", "ra",   "sp",   "gp",   "tp",   "t0",   "t1",   "t2",
    "s0",   "s1",   "a0",   "a1",   "a2",   "a3",   "a4",   "a5",
    "a6",   "a7",   "s2",   "s3",   "s4",   "s5",   "s6",   "s7",
    "s8",   "s9",   "s10",  "s11",  "t3",   "t4",   "t5",   "t6",
};


static int regno(const char *s)
{
    for (size_t i = 0; i < 32; i++) {
        if (!strcmp(rv_ireg_name[i], s)) {
            return i;
        }
    }
    return -1;
}

/*
 * Build dependency graph during execution.
 * Assume for now a uniprocessor execution
 */
GSList *regl;

static void dump_dependencies(GSList *l, int8_t rn)
{
    uint64_t vaddr = ((insnregs *)l->data)->vaddr;
    for (GSList *s = l->next; s != NULL; s = s->next) {
        insnregs *r = s->data;
        if (r->rd == rn) { /* Found the dependent from insn */
            if (r->vaddr != vaddr) {
                /*
                 * Just avoids repeating the same insn over and over
                 * within short loops
                 */
                fprintf(stderr, "0x%08lx %s\n", r->vaddr, r->insn);
            }
            if ((r->addr & rd) == rd) { /* We stop recursion here */
                break;
            }
            if (r->rs1 != -1) {
                dump_dependencies(s, r->rs1);
            }
            /* Needed when propagating through an add or so */
            if (r->rs2 != -1) {
                dump_dependencies(s, r->rs2);
            }
            break;
        }
    }
}

static void vcpu_insn_exec(unsigned int cpu_index, void *udata)
{
    insnregs *regs = udata;
    regl = g_slist_prepend(regl, regs);

    if (regs->addr == rs1) {
        /* Dump register dependency list */
        fprintf(stderr, "0x%08lx %s\n", regs->vaddr, regs->insn);
        dump_dependencies(regl, regs->rs1);
        fprintf(stderr, "@@@@@@@@@@@@@@@@@\n");
    }
}

/*
 * QEMU convert code by translation block (TB). By hooking here we can then hook
 * a callback on each instruction and memory access.
 */
static void vcpu_tb_trans(qemu_plugin_id_t id, struct qemu_plugin_tb *tb)
{
    struct qemu_plugin_insn *insn;
    uint64_t insn_vaddr;
    char *insn_disas;
    size_t n = qemu_plugin_tb_n_insns(tb);

    for (size_t i = 0; i < n; i++) {
        insnregs *regs = malloc(sizeof(*regs));
        /*
         * `insn` is shared between translations in QEMU, copy needed data here.
         * `output` is never freed as it might be used multiple times during
         * the emulation lifetime.
         * We only consider the first 32 bits of the instruction, this may be
         * a limitation for CISC architectures.
         */
        insn = qemu_plugin_tb_get_insn(tb, i);
        insn_vaddr = qemu_plugin_insn_vaddr(insn);
        insn_disas = qemu_plugin_insn_disas(insn);
        /* For debugging purposes */
        regs->insn = strdup(insn_disas);
        regs->vaddr = insn_vaddr;
        gchar **tk = g_str_tokenize_and_fold(insn_disas, NULL, NULL);
        free(insn_disas);
        /*
         * Skip first element that is insn binary representation,
         * and roughly parse the instruction to fetch the registers.
         * Warning: This is done harshly, and all that stuff is very
         * ad-hoc.
         */
        /* Register/register ops, typically  */
        for (size_t j = 0; rv_fmt_rd_rs1_rs2[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_rs1_rs2[j])) {
                regs->addr = none;
                regs->rd   = regno(tk[2]);
                regs->rs1  = regno(tk[3]);
                regs->rs2  = regno(tk[4]);
                goto next_insn;
            }
        }

        /* These set rd from imm (plus some function of pc for 2 of them) */
        for (size_t j = 0; rv_fmt_rd_imm[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_imm[j])) {
                regs->addr = rd;
                regs->rd   = regno(tk[2]);
                regs->rs1  = -1;
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These setting rd with some function of rs1 and imm */
        for (size_t j = 0; rv_fmt_rd_rs1_imm[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_rs1_imm[j])) {
                if (tk[1][0] == 'j') { /* Handle jalr case */
                    regs->addr = rs1;
                } else {
                    regs->addr = none;
                }
                regs->rd   = regno(tk[2]);
                regs->rs1  = regno(tk[3]);
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These are branches and do not alter rd */
        for (size_t j = 0; rv_fmt_rs1_rs2_offset[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rs1_rs2_offset[j])) {
                /*
                 * If rs1 or rs2 appears to be an address, then the
                 * other register is one too.
                 */
                regs->addr = none;
                regs->rd   = -1;
                regs->rs1  = regno(tk[2]);
                regs->rs2  = regno(tk[3]);
                goto next_insn;
            }
        }

        /* These are loads! How rs1 is computed is what we are seeking */
        for (size_t j = 0; rv_fmt_rd_offset_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_offset_rs1[j])) {
                regs->addr = rs1;
                regs->rd   = regno(tk[2]);
                regs->rs1  = regno(tk[4]);
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These are stores! How rs1 is computed is what we are seeking too */
        for (size_t j = 0; rv_fmt_rs2_offset_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rs2_offset_rs1[j])) {
                regs->addr = rs1;
                regs->rd   = -1;
                regs->rs1  = regno(tk[4]);
                regs->rs2  = regno(tk[2]);
                goto next_insn;
            }
        }

        /* These are load linked */
        for (size_t j = 0; rv_fmt_aqrl_rd_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_aqrl_rd_rs1[j])) {
                size_t k = 2;
                /* Skip the size, aq and rl if it exists */
                while (regno(tk[k]) == -1) {
                    k++;
                }
                    
                regs->addr = rs1;
                regs->rd   = -1;
                regs->rs1  = regno(tk[k + 1]);
                regs->rs2  = regno(tk[k + 0]);
                goto next_insn;
            }
        }

        /* These are store conditional and amos */
        for (size_t j = 0; rv_fmt_aqrl_rd_rs2_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_aqrl_rd_rs2_rs1[j])) {
                size_t k = 2;
                /* Skip the size, aq and rl if it exists */
                while (regno(tk[k]) == -1) {
                    k++;
                }
                    
                regs->addr = rs1;
                regs->rd   = regno(tk[k + 0]);
                regs->rs1  = regno(tk[k + 2]);
                regs->rs2  = regno(tk[k + 1]);
                goto next_insn;
            }
        }

        /* This is sfence.vma */
        for (size_t j = 0; rv_fmt_rs1_rs2[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rs1_rs2[j])) {
                regs->addr = rs1;
                regs->rd   = -1;
                regs->rs1  = regno(tk[3]);
                regs->rs2  = regno(tk[4]);
                goto next_insn;
            }
        }

        /* We are in the csrs, some of them might be addresses, we shall
         * check the csr number to set the insn type.
         * Let us use none for now. */
        for (size_t j = 0; rv_fmt_rd_csr_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_csr_rs1[j])) {
                regs->addr = none;
                regs->rd   = regno(tk[2]);
                regs->rs1  = regno(tk[4]);
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        for (size_t j = 0; rv_fmt_rd_csr_zimm[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_rd_csr_zimm[j])) {
                regs->addr = none;
                regs->rd   = regno(tk[3]);
                regs->rs1  = -1;
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These are float loads */
        for (size_t j = 0; rv_fmt_frd_offset_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_frd_offset_rs1[j])) {
                regs->addr = rs1;
                regs->rd   = -1;
                regs->rs1  = regno(tk[4]);
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These are float stores */
        for (size_t j = 0; rv_fmt_frs2_offset_rs1[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_frs2_offset_rs1[j])) {
                regs->addr = rs1;
                regs->rd   = -1;
                regs->rs1  = regno(tk[3]);
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* These are either floats or for sure cannot contain addresses */
        for (size_t j = 0; rv_fmt_fp[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_fp[j])) {
                regs->addr = none;
                regs->rd   = -1;
                regs->rs1  = -1;
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        for (size_t j = 0; rv_fmt_none[j] != NULL; j++) {
            if (!strcmp(tk[1], rv_fmt_none[j])) {
                regs->addr = none;
                regs->rd   = -1;
                regs->rs1  = -1;
                regs->rs2  = -1;
                goto next_insn;
            }
        }

        /* If no insn matches, we have a problem */
        assert(true);

next_insn:
        /* Well, not King Size speed work here */
        for (size_t j = 0; tk[j] != NULL; j++) {
            free(tk[j]);
        }
#if 0
static const char rv_areg_name[4][5] = {
    "none", "rd",   "rs1",   "rs2",
};
        /* Useful for checking whether the insns have been properly decoded */
        fprintf(stderr, "%s\n", insn_disas);
        fprintf(stderr, "%4s/%4s/%4s/%4s\n",
                rv_areg_name[regs->addr], rv_ireg_name[regs->rd],
                rv_ireg_name[regs->rs1], rv_ireg_name[regs->rs2]);
#endif

#if 1
        /* Register callback on instruction */
        qemu_plugin_register_vcpu_insn_exec_cb(insn, vcpu_insn_exec,
                                               QEMU_PLUGIN_CB_NO_REGS, regs);
#endif
    }
}

/*
 * On plugin exit, release resources
 */
static void plugin_exit(qemu_plugin_id_t id, void *p)
{
    for (GSList *s = regl; s != NULL; s = s->next) {
        insnregs *r = s->data;
        /* Got some double-free here, don't understand why */
#if 0
        free(r->insn);
#endif
        free(r);
    }
    g_slist_free(regl);
}

/*
 * Install the plugin
 */
QEMU_PLUGIN_EXPORT int qemu_plugin_install(qemu_plugin_id_t id,
                                           const qemu_info_t *info, int argc,
                                           char **argv)
{
    /* Register translation block and exit callbacks */
    qemu_plugin_register_vcpu_tb_trans_cb(id, vcpu_tb_trans);
    qemu_plugin_register_atexit_cb(id, plugin_exit, NULL);

    return 0;
}
