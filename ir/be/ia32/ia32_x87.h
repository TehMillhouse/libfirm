/*
 * Copyright (C) 1995-2008 University of Karlsruhe.  All right reserved.
 *
 * This file is part of libFirm.
 *
 * This file may be distributed and/or modified under the terms of the
 * GNU General Public License version 2 as published by the Free Software
 * Foundation and appearing in the file LICENSE.GPL included in the
 * packaging of this file.
 *
 * Licensees holding valid libFirm Professional Edition licenses may use
 * this file in accordance with the libFirm Commercial License.
 * Agreement provided with the Software.
 *
 * This file is provided AS IS with NO WARRANTY OF ANY KIND, INCLUDING THE
 * WARRANTY OF DESIGN, MERCHANTABILITY AND FITNESS FOR A PARTICULAR
 * PURPOSE.
 */

/**
 * @file
 * @brief       This file implements the x87 support and virtual to stack
 *              register translation for the ia32 backend.
 * @author      Michael Beck
 */
#ifndef FIRM_BE_IA32_IA32_X87_H
#define FIRM_BE_IA32_IA32_X87_H

#include "bearch.h"
#include "beirg.h"

/**
 * Run a simulation and fix all virtual instructions for a graph.
 * Replaces all virtual floating point instructions and registers
 * by real ones.
 *
 * @param irg      the graph to simulate and patch
 *
 * Registers must be allocated.
 */
void ia32_x87_simulate_graph(ir_graph *irg);

/**
 * Initializes the x87 simulator.
 */
void ia32_init_x87(void);

#endif