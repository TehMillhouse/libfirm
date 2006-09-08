/**
 * Author:      Daniel Grund
 * Date:		20.09.2005
 * Copyright:   (c) Universitaet Karlsruhe
 * Licence:     This file protected by GPL -  GNU GENERAL PUBLIC LICENSE.
 *
 */
#ifdef HAVE_CONFIG_H
#include "config.h"
#endif

#ifdef HAVE_ALLOCA_H
#include <alloca.h>
#endif

#ifdef HAVE_MALLOC_H
#include <malloc.h>
#endif

#include "obst.h"
#include "set.h"
#include "pset.h"
#include "irprintf_t.h"
#include "irgraph.h"
#include "irnode.h"
#include "irmode.h"
#include "irgwalk.h"
#include "iredges_t.h"
#include "ircons_t.h"
#include "irprintf.h"

#include "beutil.h"
#include "bearch.h"
#include "bespillbelady.h"
#include "beuses_t.h"
#include "besched_t.h"
#include "beirgmod.h"
#include "belive_t.h"
#include "benode_t.h"
#include "bechordal_t.h"

#define DBG_SPILL   1
#define DBG_WSETS   2
#define DBG_FIX     4
#define DBG_DECIDE  8
#define DBG_START  16
#define DBG_SLOTS  32
#define DBG_TRACE  64
#define DBG_WORKSET 128
#define DEBUG_LVL 0 //(DBG_START | DBG_DECIDE | DBG_WSETS | DBG_FIX | DBG_SPILL)
DEBUG_ONLY(static firm_dbg_module_t *dbg = NULL;)

/**
 * An association between a node and a point in time.
 */
typedef struct _loc_t {
  ir_node *irn;        /**< A node. */
  unsigned time;       /**< A use time (see beuses.h). */
} loc_t;

typedef struct _workset_t {
	int len;			/**< current length */
	loc_t vals[0];		/**< inlined array of the values/distances in this working set */
} workset_t;

typedef struct _belady_env_t {
	struct obstack ob;
	const be_chordal_env_t *cenv;
	const arch_env_t *arch;
	const arch_register_class_t *cls;
	int n_regs;			/** number of regs in this reg-class */

	workset_t *ws;		/**< the main workset used while processing a block. ob-allocated */
	be_uses_t *uses;	/**< env for the next-use magic */
	ir_node *instr;		/**< current instruction */
	unsigned instr_nr;	/**< current instruction number (relative to block start) */
	pset *used;

	spill_env_t *senv;	/**< see bespill.h */
} belady_env_t;

static int loc_compare(const void *a, const void *b)
{
	const loc_t *p = a;
	const loc_t *q = b;
	return p->time - q->time;
}

void workset_print(const workset_t *w)
{
	int i;

	for(i = 0; i < w->len; ++i) {
		ir_fprintf(stderr, "%+F %d\n", w->vals[i].irn, w->vals[i].time);
	}
}

/**
 * Alloc a new workset on obstack @p ob with maximum size @p max
 */
static INLINE workset_t *new_workset(belady_env_t *env, struct obstack *ob) {
	workset_t *res;
	size_t size = sizeof(*res) + (env->n_regs)*sizeof(res->vals[0]);
	res = obstack_alloc(ob, size);
	memset(res, 0, size);
	return res;
}

/**
 * Alloc a new instance on obstack and make it equal to @param ws
 */
static INLINE workset_t *workset_clone(belady_env_t *env, struct obstack *ob, workset_t *ws) {
	workset_t *res;
	size_t size = sizeof(*res) + (env->n_regs)*sizeof(res->vals[0]);
	res = obstack_alloc(ob, size);
	memcpy(res, ws, size);
	return res;
}

/**
 * Do NOT alloc anything. Make @param tgt equal to @param src.
 * returns @param tgt for convenience
 */
static INLINE workset_t *workset_copy(belady_env_t *env, workset_t *tgt, workset_t *src) {
	size_t size = sizeof(*src) + (env->n_regs)*sizeof(src->vals[0]);
	memcpy(tgt, src, size);
	return tgt;
}

/**
 * Overwrites the current content array of @param ws with the
 * @param count locations given at memory @param locs.
 * Set the length of @param ws to count.
 */
static INLINE void workset_bulk_fill(workset_t *workset, int count, const loc_t *locs) {
	workset->len = count;
	memcpy(&(workset->vals[0]), locs, count * sizeof(locs[0]));
}

/**
 * Inserts the value @p val into the workset, iff it is not
 * already contained. The workset must not be full.
 */
static INLINE void workset_insert(belady_env_t *env, workset_t *ws, ir_node *val) {
	int i;
	/* check for current regclass */
	if (!arch_irn_consider_in_reg_alloc(env->arch, env->cls, val)) {
		DBG((dbg, DBG_WORKSET, "Dropped %+F\n", val));
		return;
	}

	/* check if val is already contained */
	for(i=0; i<ws->len; ++i)
		if (ws->vals[i].irn == val)
			return;

	/* insert val */
	assert(ws->len < env->n_regs && "Workset already full!");
	ws->vals[ws->len++].irn = val;
}

/**
 * Removes all entries from this workset
 */
static INLINE void workset_clear(workset_t *ws) {
	ws->len = 0;
}

/**
 * Removes the value @p val from the workset if present.
 */
static INLINE void workset_remove(workset_t *ws, ir_node *val) {
	int i;
	for(i=0; i<ws->len; ++i) {
		if (ws->vals[i].irn == val) {
			ws->vals[i] = ws->vals[--ws->len];
			return;
		}
	}
}

static INLINE int workset_contains(const workset_t *ws, const ir_node *val) {
	int i;
	for(i=0; i<ws->len; ++i) {
		if (ws->vals[i].irn == val)
			return 1;
	}

	return 0;
}

/**
 * Iterates over all values in the working set.
 * @p ws The workset to iterate
 * @p v  A variable to put the current value in
 * @p i  An integer for internal use
 */
#define workset_foreach(ws, v, i)	for(i=0; \
										v=(i < ws->len) ? ws->vals[i].irn : NULL, i < ws->len; \
										++i)

#define workset_set_time(ws, i, t) (ws)->vals[i].time=t
#define workset_get_time(ws, i) (ws)->vals[i].time
#define workset_set_length(ws, length) (ws)->len = length
#define workset_get_length(ws) ((ws)->len)
#define workset_get_val(ws, i) ((ws)->vals[i].irn)
#define workset_sort(ws) qsort((ws)->vals, (ws)->len, sizeof((ws)->vals[0]), loc_compare);

typedef struct _block_info_t {
	workset_t *ws_start, *ws_end;
	int processed;
} block_info_t;


static INLINE void *new_block_info(struct obstack *ob) {
	block_info_t *res = obstack_alloc(ob, sizeof(*res));
	res->ws_start = NULL;
	res->ws_end = NULL;
	res->processed = 0;

	return res;
}

#define get_block_info(blk)			((block_info_t *)get_irn_link(blk))
#define set_block_info(blk, info)	set_irn_link(blk, info)

/**
 * @return The distance to the next use or 0 if irn has dont_spill flag set
 */
static INLINE unsigned get_distance(belady_env_t *env, const ir_node *from, unsigned from_step, const ir_node *def, int skip_from_uses)
{
	int flags = arch_irn_get_flags(env->arch, def);
	unsigned dist;

	assert(! (flags & arch_irn_flags_ignore));

	/* We have to keep nonspillable nodes in the workingset */
	if(flags & arch_irn_flags_dont_spill)
		return 0;

	dist = be_get_next_use(env->uses, from, from_step, def, skip_from_uses);

	if(USES_IS_INFINITE(dist))
		dist = USES_INFINITY;

	return dist;
}

/**
 * Fix to remove dead nodes (especially don't spill nodes) from workset.
 */
static void fix_dead_values(workset_t *ws, ir_node *irn) {
	int idx;
	ir_node *node;
	ir_node *block = get_nodes_block(irn);

	DBG((dbg, DBG_DECIDE, "fixing dead values at %+F:\n", irn));

	workset_foreach(ws, node, idx) {
		const ir_edge_t *edge;
		int             fixme = 1;

		/* skip already fixed nodes */
		if (workset_get_time(ws, idx) == INT_MAX)
			continue;

		/* check all users */
		foreach_out_edge(node, edge) {
			ir_node *user = get_edge_src_irn(edge);

			if ((get_nodes_block(user) != block)                           ||  /* user is in a different block */
				(sched_is_scheduled(user) && sched_comes_after(irn, user)) ||  /* user is scheduled after irn */
				user == irn)                                                   /* irn is the user */
			{                                                                  /* => don't fix distance */
				fixme = 0;
				break;
			}
		}

		/* all users scheduled prior to current irn in in same block as irn -> fix */
		if (fixme) {
			workset_set_time(ws, idx, INT_MAX);
			DBG((dbg, DBG_DECIDE, "\tfixing time for %+F to INT_MAX\n", node));
		}
	}

}

/**
 * Performs the actions necessary to grant the request that:
 * - new_vals can be held in registers
 * - as few as possible other values are disposed
 * - the worst values get disposed
 *
 * @p is_usage indicates that the values in new_vals are used (not defined)
 * In this case reloads must be performed
 */
static void displace(belady_env_t *env, workset_t *new_vals, int is_usage) {
	ir_node *val;
	int     i, len, max_allowed, demand, iter;

	workset_t *ws         = env->ws;
	ir_node   **to_insert = alloca(env->n_regs * sizeof(*to_insert));

	/*
		1. Identify the number of needed slots and the values to reload
	*/
	demand = 0;
	workset_foreach(new_vals, val, iter) {
		/* mark value as used */
		if (is_usage)
			pset_insert_ptr(env->used, val);

		if (! workset_contains(ws, val)) {
			DBG((dbg, DBG_DECIDE, "    insert %+F\n", val));
			to_insert[demand++] = val;
			if (is_usage)
				be_add_reload(env->senv, val, env->instr);
		}
		else {
			assert(is_usage || "Defined value already in workset?!?");
			DBG((dbg, DBG_DECIDE, "    skip %+F\n", val));
		}
	}
	DBG((dbg, DBG_DECIDE, "    demand = %d\n", demand));

	/*
		2. Make room for at least 'demand' slots
	*/
	len         = workset_get_length(ws);
	max_allowed = env->n_regs - demand;

	DBG((dbg, DBG_DECIDE, "    disposing %d values\n", ws->len - max_allowed));

	/* Only make more free room if we do not have enough */
	if (len > max_allowed) {
		/* get current next-use distance */
		for (i = 0; i < ws->len; ++i) {
			unsigned dist = get_distance(env, env->instr, env->instr_nr, workset_get_val(ws, i), !is_usage);
			workset_set_time(ws, i, dist);
		}

		/*
			FIX for don't spill nodes:
			Problem is that get_distance always returns 0 for those nodes even if they are not
			needed anymore (all their usages have already been visited).
			Even if we change this behavior, get_distance doesn't distinguish between not
			used anymore (dead) and live out of block.
			Solution: Set distances of all nodes having all their usages in schedule prior to
			current instruction to MAX_INT.
		*/
		fix_dead_values(ws, env->instr);

		/* sort entries by increasing nextuse-distance*/
		workset_sort(ws);

		/*
			Logic for not needed live-ins: If a value is disposed
			before its first usage, remove it from start workset
			We don't do this for phis though
		*/
		for (i = max_allowed; i < ws->len; ++i) {
			ir_node *irn = ws->vals[i].irn;

            if (is_Phi(irn))
                continue;

			if (! pset_find_ptr(env->used, irn)) {
				ir_node   *curr_bb  = get_nodes_block(env->instr);
				workset_t *ws_start = get_block_info(curr_bb)->ws_start;
				workset_remove(ws_start, irn);

				DBG((dbg, DBG_DECIDE, "    dispose %+F dumb\n", irn));
			}
			else {
				DBG((dbg, DBG_DECIDE, "    dispose %+F\n", irn));
			}
		}

		/* kill the last 'demand' entries in the array */
		workset_set_length(ws, max_allowed);
	}

	/*
		3. Insert the new values into the workset
	*/
	for (i = 0; i < demand; ++i)
		workset_insert(env, env->ws, to_insert[i]);
}

static void belady(ir_node *blk, void *env);

/*
 * Computes set of live-ins for each block with multiple predecessors
 * and notifies spill algorithm which phis need to be spilled
 */
static void spill_phi_walker(ir_node *block, void *data) {
	belady_env_t *env = data;
	block_info_t *block_info;
	ir_node *first, *irn;
	loc_t loc, *starters;
	int i, len, ws_count;

	if(get_Block_n_cfgpreds(block) == 1 && get_irg_start_block(get_irn_irg(block)) != block)
		return;

	block_info = new_block_info(&env->ob);
	set_block_info(block, block_info);

	/* Collect all values living at start of block */
	starters = NEW_ARR_F(loc_t, 0);

	/* rebuild schedule time information, because it seems to be broken */
	sched_renumber(block);

	DBG((dbg, DBG_START, "Living at start of %+F:\n", block));
	first = sched_first(block);
	sched_foreach(block, irn) {
		if(!is_Phi(irn))
			break;
		if(!arch_irn_consider_in_reg_alloc(env->arch, env->cls, irn))
			continue;

		loc.irn = irn;
		loc.time = get_distance(env, first, 0, irn, 0);
		ARR_APP1(loc_t, starters, loc);
		DBG((dbg, DBG_START, "    %+F:\n", irn));
	}

	be_lv_foreach(env->cenv->lv, block, be_lv_state_in, i) {
		ir_node *irn = be_lv_get_irn(env->cenv->lv, block, i);
		if (!arch_irn_consider_in_reg_alloc(env->arch, env->cls, irn))
			continue;

		loc.irn = irn;
		loc.time = get_distance(env, first, 0, irn, 0);
		ARR_APP1(loc_t, starters, loc);
		DBG((dbg, DBG_START, "    %+F:\n", irn));
	}

	// Sort start values by first use
	qsort(starters, ARR_LEN(starters), sizeof(starters[0]), loc_compare);

	/* Copy the best ones from starters to start workset */
	ws_count = MIN(ARR_LEN(starters), env->n_regs);
	block_info->ws_start = new_workset(env, &env->ob);
	workset_bulk_fill(block_info->ws_start, ws_count, starters);

	/* The phis of this block which are not in the start set have to be spilled later. */
	for (i = ws_count, len = ARR_LEN(starters); i < len; ++i) {
		irn = starters[i].irn;
		if (!is_Phi(irn) || get_nodes_block(irn) != block)
			continue;

		be_spill_phi(env->senv, irn);
	}

	DEL_ARR_F(starters);
}

/**
 * Collects all values live-in at block @p blk and all phi results in this block.
 * Then it adds the best values (at most n_regs) to the blocks start_workset.
 * The phis among the remaining values get spilled: Introduce psudo-copies of
 *  their args to break interference and make it possible to spill them to the
 *  same spill slot.
 */
static block_info_t *compute_block_start_info(belady_env_t *env, ir_node *block) {
	ir_node *pred_block;
	block_info_t *res, *pred_info;

	/* Have we seen this block before? */
	res = get_block_info(block);
	if (res)
		return res;

	/* Create the block info for this block. */
	res = new_block_info(&env->ob);
	set_block_info(block, res);

	/* Use endset of predecessor block as startset */
	assert(get_Block_n_cfgpreds(block) == 1 && block != get_irg_start_block(get_irn_irg(block)));
	pred_block = get_Block_cfgpred_block(block, 0);
	pred_info = get_block_info(pred_block);

	/* if pred block has not been processed yet, do it now */
	if (pred_info == NULL || pred_info->processed == 0) {
		belady(pred_block, env);
		pred_info = get_block_info(pred_block);
	}

	/* now we have an end_set of pred */
	assert(pred_info->ws_end && "The recursive call (above) is supposed to compute an end_set");
	res->ws_start = workset_clone(env, &env->ob, pred_info->ws_end);

	return res;
}


/**
 * For the given block @p blk, decide for each values
 * whether it is used from a register or is reloaded
 * before the use.
 */
static void belady(ir_node *block, void *data) {
	belady_env_t *env = data;
	workset_t *new_vals;
	ir_node *irn;
	int iter;
	block_info_t *block_info;

	/* make sure we have blockinfo (with startset) */
	block_info = get_block_info(block);
	if (block_info == NULL)
		block_info = compute_block_start_info(env, block);

	/* Don't do a block twice */
	if(block_info->processed)
		return;

	/* get the starting workset for this block */
	DBG((dbg, DBG_DECIDE, "\n"));
	DBG((dbg, DBG_DECIDE, "Decide for %+F\n", block));

	workset_copy(env, env->ws, block_info->ws_start);
	DBG((dbg, DBG_WSETS, "Start workset for %+F:\n", block));
	workset_foreach(env->ws, irn, iter)
		DBG((dbg, DBG_WSETS, "  %+F\n", irn));

	/* process the block from start to end */
	DBG((dbg, DBG_WSETS, "Processing...\n"));
	env->used = pset_new_ptr_default();
	env->instr_nr = 0;
	new_vals = new_workset(env, &env->ob);
	sched_foreach(block, irn) {
		int i, arity;
		assert(workset_get_length(env->ws) <= env->n_regs && "Too much values in workset!");

		/* projs are handled with the tuple value.
		 * Phis are no real instr (see insert_starters())
		 * instr_nr does not increase */
		if (is_Proj(irn) || is_Phi(irn)) {
			DBG((dbg, DBG_DECIDE, "  ...%+F skipped\n", irn));
			continue;
		}
		DBG((dbg, DBG_DECIDE, "  ...%+F\n", irn));

		/* set instruction in the workset */
		env->instr = irn;

		/* allocate all values _used_ by this instruction */
		workset_clear(new_vals);
		for(i = 0, arity = get_irn_arity(irn); i < arity; ++i) {
			workset_insert(env, new_vals, get_irn_n(irn, i));
		}
		displace(env, new_vals, 1);

		/* allocate all values _defined_ by this instruction */
		workset_clear(new_vals);
		if (get_irn_mode(irn) == mode_T) { /* special handling for tuples and projs */
			ir_node *proj;
			for(proj=sched_next(irn); is_Proj(proj); proj=sched_next(proj))
				workset_insert(env, new_vals, proj);
		} else {
			workset_insert(env, new_vals, irn);
		}
		displace(env, new_vals, 0);

		env->instr_nr++;
	}
	del_pset(env->used);

	/* Remember end-workset for this block */
	block_info->ws_end = workset_clone(env, &env->ob, env->ws);
	block_info->processed = 1;
	DBG((dbg, DBG_WSETS, "End workset for %+F:\n", block));
	workset_foreach(block_info->ws_end, irn, iter)
		DBG((dbg, DBG_WSETS, "  %+F\n", irn));
}

/**
 * 'decide' is block-local and makes assumptions
 * about the set of live-ins. Thus we must adapt the
 * live-outs to the live-ins at each block-border.
 */
static void fix_block_borders(ir_node *blk, void *data) {
	belady_env_t *env = data;
	workset_t *wsb;
	int i, max, iter, iter2;

	DBG((dbg, DBG_FIX, "\n"));
	DBG((dbg, DBG_FIX, "Fixing %+F\n", blk));

	wsb = get_block_info(blk)->ws_start;

	/* process all pred blocks */
	for (i=0, max=get_irn_arity(blk); i<max; ++i) {
		ir_node *irnb, *irnp, *pred = get_Block_cfgpred_block(blk, i);
		workset_t *wsp = get_block_info(pred)->ws_end;

		DBG((dbg, DBG_FIX, "  Pred %+F\n", pred));

		workset_foreach(wsb, irnb, iter) {
			/* if irnb is a phi of the current block we reload
			 * the corresponding argument, else irnb itself */
			if(is_Phi(irnb) && blk == get_nodes_block(irnb)) {
				irnb = get_irn_n(irnb, i);

				// we might have unknowns as argument for the phi
				if(!arch_irn_consider_in_reg_alloc(env->arch, env->cls, irnb))
					continue;
			}

			/* Unknowns are available everywhere */
			if(get_irn_opcode(irnb) == iro_Unknown)
				continue;

			/* check if irnb is in a register at end of pred */
			workset_foreach(wsp, irnp, iter2) {
				if (irnb == irnp)
					goto next_value;
			}

			/* irnb is not in memory at the end of pred, so we have to reload it */
			DBG((dbg, DBG_FIX, "    reload %+F\n", irnb));
			be_add_reload_on_edge(env->senv, irnb, blk, i);

next_value:
			/*epsilon statement :)*/;
		}
	}
}

void be_spill_belady(const be_chordal_env_t *chordal_env) {
	be_spill_belady_spill_env(chordal_env, NULL);
}

void be_spill_belady_spill_env(const be_chordal_env_t *chordal_env, spill_env_t *spill_env) {
	belady_env_t env;

	FIRM_DBG_REGISTER(dbg, "firm.be.spill.belady");
	//firm_dbg_set_mask(dbg, DBG_START);

	/* init belady env */
	obstack_init(&env.ob);
	env.cenv      = chordal_env;
	env.arch      = chordal_env->birg->main_env->arch_env;
	env.cls       = chordal_env->cls;
	env.n_regs    = env.cls->n_regs - be_put_ignore_regs(chordal_env->birg, chordal_env->cls, NULL);
	env.ws        = new_workset(&env, &env.ob);
	env.uses      = be_begin_uses(chordal_env->irg, chordal_env->exec_freq, chordal_env->lv);
	if(spill_env == NULL) {
		env.senv = be_new_spill_env(chordal_env);
	} else {
		env.senv = spill_env;
	}
	DEBUG_ONLY(be_set_spill_env_dbg_module(env.senv, dbg);)

	DBG((dbg, LEVEL_1, "running on register class: %s\n", env.cls->name));

	be_clear_links(chordal_env->irg);
	/* Decide which phi nodes will be spilled and place copies for them into the graph */
	irg_block_walk_graph(chordal_env->irg, spill_phi_walker, NULL, &env);
	/* Fix high register pressure with belady algorithm */
	irg_block_walk_graph(chordal_env->irg, NULL, belady, &env);
	/* belady was block-local, fix the global flow by adding reloads on the edges */
	irg_block_walk_graph(chordal_env->irg, fix_block_borders, NULL, &env);
	/* Insert spill/reload nodes into the graph and fix usages */
	be_insert_spills_reloads(env.senv);

	/* clean up */
	if(spill_env == NULL)
		be_delete_spill_env(env.senv);
	be_end_uses(env.uses);
	obstack_free(&env.ob, NULL);
}
