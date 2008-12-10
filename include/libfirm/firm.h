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
 * @brief     Central firm header.
 * @author    Martin Trapp, Christian Schaefer, Goetz Lindenmaier
 * @version   $Id$
 * @summary
 *  Central FIRM header.
 *
 *  FIRM is a full graph based intermediate representation in SSA Form
 *  with a novel concept to model side effects.  It allows fast, aggressive
 *  optimizations.
 *
 *  This header is the central header of the library implementation of this
 *  IR.
 *
 *  The internal representation of a program in firm is separated into five
 *  different modules:
 *   - Firm Graphs representing the code of a program. (Subdirectory ir.)
 *     Firm Graphs are assembled out of several data structures:
 *     irprog: represents a program.  Allows access to all types and all
 *       FIRM graphs for procedures and other global things.
 *     irgraph: represents a procedure.  Allows access to the code of the
 *       procedure, the actual FIRM graph.
 *     irnode: A node of a FIRM graph.  Nodes are typed with an opcode and a mode
 *   and represent instructions in a program.
 *     irop: The opcode of FIRM nodes.
 *     irmode: The mode of FIRM nodes.  Most modes correspond to machine known
 *       data types (int, float, pointer).
 *   - Entities representing program known objects. (Subdirectory tr.)
 *     All variables and procedures are entities.
 *   - Types describing the type system for the program. (Subdirectory tr.)
 *   - Target Values representing program known constants. (Subdirectory tv.)
 *   - Identifiers representing any Strings used in the program. (Subdirectory ident.)
 *
 *   Further this library supplies functionality to build and optimize FIRM graphs
 *   and further functionality needed in a compiler.  Finally there is more
 *   generic functionality to support implementations using firm.  (Code generation,
 *   further optimizations).
 */
#ifndef FIRM_COMMON_FIRM_H
#define FIRM_COMMON_FIRM_H

#ifdef __cplusplus
extern "C" {
#endif

/* The representations */
#include "firm_common.h"   /* common type tags. */
#include "irprog.h"        /* control flow and data of a program */
#include "irgraph.h"       /* graphs */
#include "typerep.h"       /* type representation */
#include "tv.h"            /* target values */
#include "irnode.h"
#include "irop.h"
#include "ident.h"         /* source code identificators */

/* Functionality */
#include "ircons.h"        /* construct ir */
#include "ircgcons.h"      /* construct interprocedural graph */

/* Optimizations */
#include "irflag.h"         /* optimization flags */
#include "irgopt.h"         /* optimize ir */
#include "iroptimize.h"     /* optimize ir by reassociation */
#include "ircgopt.h"        /* Optimizations based on interprocedural graph */
#include "iropt.h"

/* Lowering */
#include "lowering.h"         /* lowering of different calls parameters, intrinsic calls, double word types, high-level constructs */

/* Analyses */
#include "irouts.h"           /* Graph reversal / out edges. */
#include "trouts.h"           /* Graph reversal / out edges for types. */
#include "irdom.h"            /* Dominator analysis */
#include "cgana.h"            /* Analysis to construct interprocedural graph */
                              /* including some optimizations */
#include "irloop.h"           /* loop and backedge analysis */
#include "callgraph.h"        /* Callgraph construction */
#include "irconsconfirm.h"    /* Confirm nodes */
#include "analyze_irg_args.h" /* Simple pointer parameter analysis */
#include "irtypeinfo.h"       /* type information for nodes */
#include "irmemory.h"         /* memory disambiguation */
#include "interval_analysis.h"
#include "field_temperature.h"
#include "execution_frequency.h"

/* Support */
#include "irgmod.h"         /* Support to modify ir */
#include "irgwalk.h"        /* Support to walk ir */

#include "irarch.h"        /* architecture dependent optimizations */

#include "firmstat.h"      /* statistics */

#include "dbginfo.h"       /* debug support */
#include "seqnumbers.h"    /* debug support */
#include "firm_ycomp.h"    /* ycomp debugging support */

#include "irdump.h"
#include "irprintf.h"
#include "irvrfy.h"

#include "irarch.h"

#include "iredges.h"

#include "be.h"

#ifdef __cplusplus
}
#endif

#endif
