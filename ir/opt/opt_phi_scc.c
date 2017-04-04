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
 * If an SCC is not redundant, we still have to check all SCCs in the subgraph induced by the SCC (removing any nodes that
 * connect to its outside from the working set). In order to do this, we note the "scc id" of each node
 * and only increase this number for the nodes we may recurse on. (since the "inner" part of different SCCs are
 * disconnected, this works out on the whole)
 *
 * SCCs are stored in a doubly-linked list, with each SCC consisting of an ir_nodeset of nodes.
 */

typedef struct scc {
    list_head    link;
    ir_nodeset_t nodes;
    unsigned depth;
} scc_t;

typedef struct scc_env {
    struct obstack   obst;
    ir_node        **stack;
    size_t           stack_top;
    unsigned         next_index;
    list_head        working_set_sccs; /**< the sccs we *just* found, and haven't yet evaluated */
    list_head        scc_work_stack;   /**< the sets of nodes we still need to evaluate in future iterations */
    ir_nodehashmap_t replacement_map;  /**< map from node to their replacement */
} scc_env_t;

typedef struct scc_irn_info {
    bool     in_stack;          /**< Marks whether node is on the stack. */
    unsigned dfn;               /**< Depth first search number. */
    unsigned uplink;            /**< dfn number of ancestor. */
    unsigned depth;            /**< iteration depth of scc search */
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


/** return the unique predecessor of a redundant scc, or NULL if the scc is not redundant.
 *  (Also marks nodes elidible for next iteration by clearing their dfn and setting their depth)
 */
static ir_node *get_unique_pred(scc_t *scc, scc_env_t *env) {
    ir_node *unique_pred = NULL;
    bool redundant = true;
    foreach_ir_nodeset(&scc->nodes, irn, iter) {
        // only nodes which are not on the "rim" of the scc are eligible for the next iteration
        bool eligible_for_next_iteration = true;
        foreach_irn_in(irn, idx, original_pred) {
            // we can safely ignore self-loops in this regard
            if (original_pred != irn) {

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
        }
        if (eligible_for_next_iteration) {
            scc_irn_info_t *info = get_irn_info(irn, env);
            info->depth++;
            scc->depth = info->depth; // TODO factor out
            info->dfn = 0;
        }
    }
    return redundant ? unique_pred : NULL;
}


/** Append the working set to the work queue and prime the first eligible SCC in the work queue for the next iteration
 *  (redundant or outer-node-only SCCs are evaluated and discarded)
 */
static void prepare_next_iteration(scc_env_t *env) {

    list_splice_init(&env->working_set_sccs, &env->scc_work_stack);

    list_for_each_entry_safe(scc_t, scc, tmp, &env->scc_work_stack, link) {
        ir_node *unique_pred = get_unique_pred(scc, env);
        if (unique_pred) {
            // SCC is redundant, reroute and discard
            foreach_ir_nodeset(&scc->nodes, irn, iter) {
                ir_nodehashmap_insert(&env->replacement_map, irn, unique_pred);
            }
            ir_nodeset_destroy(&scc->nodes);
            list_del_init(&scc->link);
        } else {
            foreach_ir_nodeset(&scc->nodes, irn, iter) {
                // get_unique_pred has marked all "inner" nodes by resetting their dfn, the rest must be removed.
                if (get_irn_info(irn, env)->dfn != 0)
                    ir_nodeset_remove_iterator(&scc->nodes, &iter);
            }

            if (ir_nodeset_size(&scc->nodes) > 1) break;
            else {
                // we have no need for this scc anymore
                ir_nodeset_destroy(&scc->nodes);
                list_del_init(&scc->link);
            }
        }
    }
}

static inline bool is_removable(ir_node *irn, scc_env_t *env, unsigned depth) {
    scc_irn_info_t *info = get_irn_info(irn, env);
    return is_Phi(irn) && !get_Phi_loop(irn) && info->depth >= depth;
}


/// DEBUG
ir_graph *create_blank_graph(void) {
    ir_type *t = new_type_method(0, 1, false, 0, mtp_no_property);
    set_method_res_type(t, 0, new_type_primitive(get_modeIs()));
    ir_entity *ent = new_entity(get_glob_type(), new_id_from_str("test_"), t);
    ir_graph *g = new_ir_graph(ent, 100);
    return g;
}

ir_graph *create_ladder_graph(int steps) {
    ir_graph *g = create_blank_graph();
    set_current_ir_graph(g);

    ir_node *startbl = get_irg_start_block(g);
    set_cur_block(startbl);

    ir_node *n0 = new_Const_long(mode_Is, 0);
    ir_node *n1 = new_Const_long(mode_Is, 1);

    ir_node *ins1[] = {n0};
    ir_node *ret = new_r_Return(startbl, get_irg_initial_mem(g), 1, ins1);
    add_immBlock_pred(get_irg_end_block(g), ret);

    printf("creating phis\n");
    ir_node *ins[] = {n0, n1};
    ir_node *final0 = new_r_Phi(startbl, 2, ins, mode_Is);
    ir_node *final1 = new_r_Phi(startbl, 2, ins, mode_Is);

    ins[0] = final0;
    ins[1] = final1;

    ir_node *final = new_r_Phi(startbl, 2, ins, mode_Is);

    ir_node *phi0, *phi1;
    ir_node *oldphi0 = n0, *oldphi1 = n1;
    // Loop creating n steps
    for (int n = 0; n < steps-1; n++) {
        ins[0] = oldphi0;
        ins[1] = final0;
        phi0 = new_r_Phi(startbl, 2, ins, mode_Is);
        ins[0] = oldphi1;
        ins[1] = final1;
        phi1 = new_r_Phi(startbl, 2, ins, mode_Is);

        oldphi0 = phi0;
        oldphi1 = phi1;
    }

    ir_node *fixup[] = {phi0, final1};
    set_irn_in(final0, 2, fixup);
    fixup[0] = phi1;
    fixup[1] = final0;
    set_irn_in(final1, 2, fixup);

    set_irn_n(ret, 1, final);
    clear_irg_constraints(g, IR_GRAPH_CONSTRAINT_CONSTRUCTION);
    return g;
}


/** Perform's Tarjan's algorithm, starting at a given node
 *
 *  returns false if n must be ignored
 *  (either because it's not a Phi node or because it's been excluded in a previous run) */
static bool find_scc_at(ir_node *n, scc_env_t *env, unsigned depth)
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
        do {
            n2 = pop(env);
            scc_irn_info_t *n2_info = get_irn_info(n2, env);
            n2_info->in_stack = false;
            ir_nodeset_insert(&scc->nodes, n2);
            scc->depth = n2_info->depth;
        } while (n2 != n);
        list_add_tail(&scc->link, &env->working_set_sccs);
    }
    return true;
}

#ifdef DEBUG_libfirm
static void print_sccs(scc_env_t *env)
{
    if (!list_empty(&env->scc_work_stack)) {
        list_for_each_entry(scc_t, scc, &env->scc_work_stack, link) {
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
#endif

// One recursive "find_scc_at" handles a complete phi web, but there may be many, so we need to walk the graph
static void _start_walk(ir_node *irn, void *env) {
    find_scc_at(irn, (scc_env_t *) env, 0 /* this is only used for the initial SCC search, so depth 0 is fine*/);
}

FIRM_API void opt_remove_unnecessary_phi_sccs(ir_graph *irg)
{

    struct scc_env env;
    memset(&env, 0, sizeof(env));
    struct obstack temp;
    obstack_init(&temp);
    env.obst = temp;
    env.stack = NEW_ARR_F(ir_node*, 128);
    ir_nodehashmap_init(&env.replacement_map);
    INIT_LIST_HEAD(&env.working_set_sccs);
    INIT_LIST_HEAD(&env.scc_work_stack);

    ir_reserve_resources(irg, IR_RESOURCE_IRN_LINK);
    irg_walk_graph(irg, NULL, firm_clear_link, NULL);

    // populate work queue with an initial round of SCCs
    irg_walk_graph(irg, _start_walk, NULL, &env);
    prepare_next_iteration(&env);

    while (!list_empty(&env.scc_work_stack)) {
        // pop an SCC from the front of the queue and evaluate it
        scc_t *current_set = list_entry(env.scc_work_stack.next, scc_t, link);
        list_del(env.scc_work_stack.next);
        foreach_ir_nodeset(&current_set->nodes, irn, iter) {
            find_scc_at(irn, &env, current_set->depth);
        }
        // clean up the scc we just popped off
        ir_nodeset_destroy(&current_set->nodes);
        prepare_next_iteration(&env);

    }

    ir_nodehashmap_entry_t entry;
    ir_nodehashmap_iterator_t iter;

    foreach_ir_nodehashmap(&env.replacement_map, entry, iter) {
        exchange(entry.node, (ir_node *) entry.data);
    }

    ir_nodehashmap_destroy((ir_nodehashmap_t *) &env.replacement_map);
    DEL_ARR_F(env.stack);
    obstack_free(&env.obst, NULL);
    ir_free_resources(irg, IR_RESOURCE_IRN_LINK);

    printf("SCC removal DONE\n");
}
