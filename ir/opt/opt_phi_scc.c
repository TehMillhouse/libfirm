/*
 * This file is part of libFirm.
 * Copyright (C) 2016 Karlsruhe Institute of Technology
 */

/**
 * @file
 * @brief   Unnecessary Phi SCC removal.
 * @date    13.03.2016
 * @author  Max Wagner
 * @brief
 *  Removal of Phi SCCs which have at most one true predecessor.
 *  See "Simple and Efficient Construction of Static Single Assignment Form" by Braun et al.
 */

#include "irdump.h"
#include "adt/pdeq.h"
#include "adt/list.h"
#include "array.h"
#include "debug.h"
#include "panic.h"
#include "hashptr.h"
#include "ircons.h"
#include "irdom.h"
#include "iredges_t.h"
#include "irflag_t.h"
#include "irgmod.h"
#include "irgwalk.h"
#include "irhooks.h"
#include "irnodeset.h"
#include "irloop_t.h"
#include "irop_t.h"
#include "iroptimize.h"
#include "irouts.h"
#include "irtools.h"
#include "obst.h"
#include "set.h"
#include "tv.h"
#include "util.h"

/** The debug handle. */
DEBUG_ONLY(static firm_dbg_module_t *dbg;)

/** We use (yet another implementation of) Tarjan's algorithm to find SCCs, which implicitly gives them
 * to us in reverse topological order, which is incidentally exactly the ordering we need.
 */


/** scratchpad:
 *
 * We compute all SCCs in a set of nodes. (until this is done, we have no way of knowing the SCCs predecessors)
 *   Note that the graph induced by these may not be connected
 *
 * We iterate over all SCCs in reverse topoorder, for each:
 *   sort phis into innerPhis and borderPhis
 *   if len(borderPhis) == 1, short circuit it
 *   else, recurse on innerPhis
 *
 *
 * this means we need to save arbitrarily many SCCs, and we need a quick way to exclude nodes from the searched
 * node set.
 * SCCs need to be iterable, so I'll need some sort of dynamic list in there
 */

/** SCCs are represented as linked lists of nodes and stored in a linked list themselves. */

typedef struct scc_node {
    list_head    link;
    ir_nodeset_t irns;
} scc_node_t;

typedef struct scc_env {
    struct obstack   obst;
    ir_node        **stack;
    size_t           stack_top;
    unsigned         next_index;
    list_head        sccs;        /**< doubly-linked list of sccs */
} scc_env_t;

typedef struct scc_irn_info {
    bool     in_stack;          /**< Marks whether node is on the stack. */
    int      dfn;               /**< Depth first search number. */
    int      uplink;            /**< dfn number of ancestor. */
    bool     blacklisted;       /**< Marks whether the node is necessary in every induced scc */
} scc_irn_info_t;


static scc_irn_info_t *get_irn_info(ir_node *node, scc_env_t *env)
{
    scc_irn_info_t *e = get_irn_link(node);
    if (e == NULL) {
        e = OALLOCZ(&env->obst, scc_irn_info_t);
        node->link = e;
    }
    return e;
}

/**
 * push a node onto the stack, potentially growing it
 *
 * @param env   the algorithm environment
 * @param node  the node to push
 */
static void push(scc_env_t *env, ir_node *node)
{
    if (env->stack_top == ARR_LEN(env->stack)) {
        size_t nlen = ARR_LEN(env->stack) * 2;
        ARR_RESIZE(ir_node*, env->stack, nlen);
    }
    env->stack[env->stack_top++] = node;
    scc_irn_info_t *e = get_irn_info(node, env);
    e->in_stack = true;

}

/**
 * pop a node from the stack
 *
 * @param env   the algorithm environment
 * @return  The topmost node
 */
static ir_node *pop(scc_env_t *env)
{
    ir_node      *n = env->stack[--env->stack_top];
    scc_irn_info_t *e = get_irn_info(n, env);
    e->in_stack = false;
    return n;
}


/** returns false if n must be ignored (either because it's not a Phi node or because it's been blacklisted */
static bool find_scc_at(ir_node *n, scc_env_t *env)
{
    scc_irn_info_t *info = get_irn_info(n, env);

    if (info->blacklisted)
        printf("blacklisted node: %d\n", get_irn_idx(n));

    if (!is_Phi(n) || info->blacklisted) {
        return false;
    } else {
        printf("PHI: %d", get_irn_idx(n));
    }
    if (info->dfn != 0) {
        // node has already been visited
        printf(" (x)\n");
        return true;
    }
    printf("\n");
    info->dfn = ++env->next_index;
    info->uplink = info->dfn;
    push(env, n);
    info->in_stack = true;
    foreach_irn_in(n, i, pred) {
        scc_irn_info_t *pred_info = get_irn_info(pred, env);
        if (pred_info->dfn == 0 && find_scc_at(pred, env)) {
            info->uplink = MIN(pred_info->uplink,info->uplink);
        } else if (pred_info->in_stack) {
            info->uplink = MIN(pred_info->dfn, info->uplink);
        }
    }
    if (info->dfn == info->uplink) {
        // found an scc
        struct scc_node *scc = OALLOC(&env->obst, struct scc_node);
        ir_nodeset_init(&scc->irns);

        ir_node *n2;
        int i = 0;
        do {
            n2 = pop(env);
            scc_irn_info_t *n2_info = get_irn_info(n2, env);
            n2_info->in_stack = false;
            ir_nodeset_insert(&scc->irns, n2);
            i++;
        } while (n2 != n);
        list_add_tail(&scc->link, &env->sccs);
    }
    return true;
}

static bool is_redundant(scc_node_t *scc, scc_env_t *env)
{
    ir_node *unique_pred = NULL;
    bool redundant = true;
    foreach_ir_nodeset(&scc->irns, irn, iter) {
        foreach_irn_in(irn, idx, pred) {
            if (!ir_nodeset_contains(&scc->irns, pred)) {
                if (unique_pred) redundant = false;
                // we don't break out of the loop because we still want to mark all necessary nodes
                unique_pred = pred;
                get_irn_info(irn, env)->blacklisted = true;
            }
        }
    }
    return redundant;
}

static void print_sccs(scc_env_t *env)
{
    if (!list_empty(&env->sccs)) {
        list_for_each_entry(scc_node_t, scc, &env->sccs, link) {
            printf("[ ");
            foreach_ir_nodeset(&scc->irns, irn, iter) {
                printf("%d, ", get_irn_idx(irn));
            }
            printf("]");
            printf(is_redundant(scc, env) ? " (redundant)\n" : "\n");
        }
    } else {
        printf("No SCCs found :(\n");
    }
}

void opt_remove_unnecessary_phi_sccs(ir_graph *irg)
{
    ir_add_dump_flags(ir_dump_flag_idx_label);
    dump_ir_graph(irg, "rofl");

    struct scc_env env;
    memset(&env, 0, sizeof(env));
    struct obstack temp;
    obstack_init(&temp);
    env.obst = temp;
    env.stack = NEW_ARR_F(ir_node*, 128);
    INIT_LIST_HEAD(&env.sccs);

    ir_reserve_resources(irg, IR_RESOURCE_IRN_LINK);
    irg_walk_graph(irg, NULL, firm_clear_link, NULL);

    printf("Starting phi SCC removal\n");

    irg_walk_graph(irg, (void (*)(ir_node *,void *)) find_scc_at, NULL, &env);
    print_sccs(&env);

    printf("======================================\n Second round\n======================================\n");
    list_for_each_entry(scc_node_t, scc, &env.sccs, link) {
        foreach_ir_nodeset(&scc->irns, irn, iter) {
            find_scc_at(irn, &env);
        }
        printf("-------- NEXT SCC\n");
    }
    print_sccs(&env);

    printf("Done.\n");


    DEL_ARR_F(env.stack);
    obstack_free(&env.obst, NULL);
    ir_free_resources(irg, IR_RESOURCE_IRN_LINK);
}
