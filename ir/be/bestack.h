/*
 * This file is part of libFirm.
 * Copyright (C) 2012 University of Karlsruhe.
 */

/**
 * @file
 * @brief       Helper functions for handling offsets into stack frames/
 *              activation records.
 * @author      Matthias Braun
 */
#ifndef FIRM_BE_BESTACK_H
#define FIRM_BE_BESTACK_H

#include <limits.h>
#include <stdbool.h>

#include "be_types.h"
#include "firm_types.h"

/**
 * Rewire all stack modifying nodes and their users to assure SSA property.
 * @param sp    The stack pointer register
 */
void be_fix_stack_nodes(ir_graph *irg, arch_register_t const *sp);

typedef int (*sp_sim_func)(ir_node *node, int offset);

/**
 * From function begin simulate relative stack pointer offset along the
 * function.
 * Note that the code already contains a special case for IncSP and MemPerm
 * nodes which need no handling in the callback.
 */
void be_sim_stack_pointer(ir_graph *irg, unsigned misalign, unsigned p2align,
                          sp_sim_func func);

/**
 * Layout entities in frame type. This will not touch entities which already
 * have offsets assigned.
 */
void be_layout_frame_type(ir_type *frame, int begin, unsigned misalign);

void be_sort_frame_entities(ir_type *const frame, bool spillslots_first);

#endif
