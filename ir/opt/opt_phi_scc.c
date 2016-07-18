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

#include <irdump_t.h>
#include <bits/time.h>
#include <time.h>
#include "debug.h"
#include "ircons.h"
#include "irgmod.h"
#include "irgwalk.h"
#include "irnodehashmap.h"
#include "irnodeset.h"
#include "irtools.h"
#include "util.h"


/** We use (yet another implementation of) Tarjan's algorithm to find SCCs, which implicitly obtains them
 * in reverse topological order. (which forgoes the need for a fixpoint iteration)
 * These SCCs are then checked for whether they are, as a whole, redundant. If they are, we mark the mapping
 * from nodes in the SCC to their unique non-SCC predecessor for edge rerouting later.
 *
 * If an SCC is not redundant, we still have to check all SCCs in the subgraph induced by the SCC without any nodes that
 * connect to its outside. In order to do this, we note the "allowed iteration depth" of each node and only increase
 * this number for the nodes we may recurse on. (since the "inner" part of different SCCs are disconnected, this works
 * out on the whole)
 *
 * SCCs are stored in a doubly-linked list, with each SCC consisting of an ir_nodeset of nodes.
 */

typedef struct scc {
    list_head    link;
    ir_nodeset_t nodes;
} scc_t;

typedef struct scc_env {
    struct obstack   obst;
    ir_node        **stack;
    size_t           stack_top;
    unsigned         next_index;
    list_head        sccs;
    ir_nodehashmap_t replacement_map;  /**< map from node to their replacement */
} scc_env_t;

typedef struct scc_irn_info {
    bool     in_stack;          /**< Marks whether node is on the stack. */
    int      dfn;               /**< Depth first search number. */
    int      uplink;            /**< dfn number of ancestor. */
    int      depth;             /**< iteration depth of scc search */
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
    ir_node        *n = env->stack[--env->stack_top];
    scc_irn_info_t *e = get_irn_info(n, env);
    e->in_stack = false;
    return n;
}

/** returns whether another iteration is needed */
static bool prepare_next_iteration(scc_env_t *env) {
    // check if any scc is redundant
    // for redundant sccs: add their nodes to the replacement_map
    // for nonredundant sccs: build a new working set, dispose of the old ones

    list_for_each_entry_safe(scc_t, scc, tmp, &env->sccs, link) {

        ir_node *unique_pred = NULL;
        bool redundant = true;
        foreach_ir_nodeset(&scc->nodes, irn, iter) {
            // only nodes which are not on the "rim" of the scc are eligible for the next iteration
            bool eligible_for_next_iteration = true;
            foreach_irn_in(irn, idx, original_pred) {
                // previous iterations might have "deleted" the node already.
                ir_node *pred = ir_nodehashmap_get(ir_node, &env->replacement_map, original_pred);
                if (pred == NULL) pred = original_pred;

                if (!ir_nodeset_contains(&scc->nodes, pred)) {
                    if (unique_pred && unique_pred != pred) redundant = false;
                    // we don't break out of the loop because we still want to mark all necessary nodes
                    unique_pred = pred;
                    eligible_for_next_iteration = false;
                }
            }
            if (eligible_for_next_iteration) {
                scc_irn_info_t *info = get_irn_info(irn, env);
                info->depth++;
                info->dfn = 0;
            }
        }

        if (redundant) {
            DEBUG_ONLY(assert(unique_pred != NULL && "completely isolated phi cycles aren't supposed to exist!"));
            foreach_ir_nodeset(&scc->nodes, irn, iter) {
                ir_nodehashmap_insert(&env->replacement_map, irn, unique_pred);
            }
        }
        // Now that we've marked all nodes in the SCC, we can remove those we've deemed not eligible for the next iteration.
        // (i.e. those who haven't had their dfn reset to zero.) We couldn't do this earlier because edges to the nodes in this
        // class would have been counted as pointing outside the SCC.
        foreach_ir_nodeset(&scc->nodes, irn, iter) {
            if (get_irn_info(irn, env)->dfn != 0)
                ir_nodeset_remove_iterator(&scc->nodes, &iter);
        }


        if (ir_nodeset_size(&scc->nodes) <= 1) {
            // we have no need for this scc anymore (trivial phis are excluded by construction)
            ir_nodeset_destroy(&scc->nodes);
            list_del_init(&scc->link);
        }
    }
    return !list_empty(&env->sccs);

}

static inline bool is_removable(ir_node *irn, scc_env_t *env, int depth) {
    scc_irn_info_t *info = get_irn_info(irn, env);
    return is_Phi(irn) && !get_Phi_loop(irn) && info->depth >= depth;
}

/** returns false if n must be ignored
 *  (either because it's not a Phi node or because it's been excluded in a previous run) */
static bool find_scc_at(ir_node *n, scc_env_t *env, int depth)
{
    if (!is_removable(n, env, depth)) return false;

    scc_irn_info_t *info = get_irn_info(n, env);
    if (info->dfn != 0) {
        // node has already been visited
        return true;
    }
    info->dfn = ++env->next_index;
    info->uplink = info->dfn;
    push(env, n);
    info->in_stack = true;
    foreach_irn_in(n, i, pred) {
        // the node might have been identified as part of a redundant scc already, so we need to check
        ir_node *canonical_pred = ir_nodehashmap_get(ir_node, &env->replacement_map, pred);
        if (!canonical_pred) canonical_pred = pred;

        scc_irn_info_t *pred_info = get_irn_info(canonical_pred, env);
        if (pred_info->dfn == 0 && find_scc_at(canonical_pred, env, depth)) {
            info->uplink = MIN(pred_info->uplink,info->uplink);
        } else if (pred_info->in_stack) {
            info->uplink = MIN(pred_info->dfn, info->uplink);
        }
    }
    if (info->dfn == info->uplink) {
        // found an scc
        struct scc *scc = OALLOC(&env->obst, struct scc);
        ir_nodeset_init(&scc->nodes);

        ir_node *n2;
        int i = 0;
        do {
            n2 = pop(env);
            scc_irn_info_t *n2_info = get_irn_info(n2, env);
            n2_info->in_stack = false;
            ir_nodeset_insert(&scc->nodes, n2);
            i++;
        } while (n2 != n);
        list_add_tail(&scc->link, &env->sccs);
    }
    return true;
}

#ifdef DEBUG_libfirm
static void print_sccs(scc_env_t *env)
{
    if (!list_empty(&env->sccs)) {
        list_for_each_entry(scc_t, scc, &env->sccs, link) {
            printf("[ ");
            foreach_ir_nodeset(&scc->nodes, irn, iter) {
                printf("%d, ", get_irn_idx(irn));
            }
            printf("]\n");
        }
    } else {
        printf("No SCCs found :(\n");
    }
}

static int phiCount = 0;
static void _count_phis(ir_node *irn, void *env) {
    if (is_Phi(irn) && get_irn_mode(irn) != mode_M) phiCount++;
}
#endif

static void _start_walk(ir_node *irn, void *env) {
    find_scc_at(irn, (scc_env_t *) env, 0);
}

FIRM_API void opt_remove_unnecessary_phi_sccs(ir_graph *irg)
{

#ifdef DEBUG_libfirm
    ir_add_dump_flags(ir_dump_flag_idx_label);

    clock_t begin, end;
    double time_spent;
    begin = clock();
    phiCount = 0;
#endif

    struct scc_env env;
    memset(&env, 0, sizeof(env));
    struct obstack temp;
    obstack_init(&temp);
    env.obst = temp;
    env.stack = NEW_ARR_F(ir_node*, 128);
    ir_nodehashmap_init(&env.replacement_map);
    INIT_LIST_HEAD(&env.sccs);

    ir_reserve_resources(irg, IR_RESOURCE_IRN_LINK);
    irg_walk_graph(irg, NULL, firm_clear_link, NULL);

    irg_walk_graph(irg, _start_walk, NULL, &env);

    while (prepare_next_iteration(&env)) {
        // we swap out the list in the environment, keeping the previous list as a working set for the next iteration
        list_head *tmp = (&env.sccs)->next;
        list_del_init(&env.sccs);
        list_head working_set;
        INIT_LIST_HEAD(&working_set);
        list_add_tail(&working_set, tmp);

        list_for_each_entry_safe(scc_t, scc, tmp, &working_set, link) {
            foreach_ir_nodeset(&scc->nodes, irn, iter) {
                find_scc_at(irn, &env, 1);
            }
        }
        // dispose of the old working set
        list_for_each_entry(scc_t, scc, &working_set, link) {
            ir_nodeset_destroy(&scc->nodes);
        }
    }

    ir_nodehashmap_entry_t entry;
    ir_nodehashmap_iterator_t iter;

    DEBUG_ONLY (if (ir_nodehashmap_size(&env.replacement_map)) dump_ir_graph(irg, "PRE"););

    foreach_ir_nodehashmap(&env.replacement_map, entry, iter) {
        exchange(entry.node, (ir_node *) entry.data);
    }

#ifdef DEBUG_libfirm
    end = clock();
    time_spent = (double)(end - begin) / CLOCKS_PER_SEC;

    irg_walk_graph(irg, _count_phis, NULL, &env);
    FILE *f = fopen("./PHIS", "a");

    fprintf(f, "Phis removed in %s: %d (took %f seconds, %d phis remaining)\n",
            get_irg_dump_name(irg),
            (int) ir_nodehashmap_size(&env.replacement_map),
            (float) time_spent,
            phiCount);
    fclose(f);

    if (ir_nodehashmap_size(&env.replacement_map)) dump_ir_graph(irg, "POST");
#endif

    ir_nodehashmap_destroy((ir_nodehashmap_t *) &env.replacement_map);
    DEL_ARR_F(env.stack);
    obstack_free(&env.obst, NULL);
    ir_free_resources(irg, IR_RESOURCE_IRN_LINK);
}
