/*
 * This file is part of libFirm.
 * Copyright (C) 2012 University of Karlsruhe.
 */

/**
 * @file
 * @brief       Processor architecture specification.
 * @author      Sebastian Hack
 */
#ifndef FIRM_BE_BEARCH_H
#define FIRM_BE_BEARCH_H

#include <stdbool.h>

#include "firm_types.h"
#include "raw_bitset.h"

#include "be_types.h"
#include "beinfo.h"
#include "be.h"

/**
 * this constant is returned by the get_sp_bias functions if the stack
 * is reset (usually because the frame pointer is copied to the stack
 * pointer
 */
#define SP_BIAS_RESET      INT_MIN

typedef enum arch_register_class_flags_t {
	arch_register_class_flag_none      = 0,
	/** don't do automatic register allocation for this class */
	arch_register_class_flag_manual_ra = 1U << 0,
} arch_register_class_flags_t;
ENUM_BITSET(arch_register_class_flags_t)

typedef enum arch_register_type_t {
	arch_register_type_none    = 0,
	/** This is just a virtual register. Virtual registers fulfill any register
	 * constraints as long as the register class matches. It is a allowed to
	 * have multiple definitions for the same virtual register at a point */
	arch_register_type_virtual = 1U << 0,
} arch_register_type_t;
ENUM_BITSET(arch_register_type_t)

/**
 * Different types of register allocation requirements.
 */
typedef enum arch_register_req_type_t {
	/** No register requirement. */
	arch_register_req_type_none              = 0,
	/** All registers in the class are allowed. */
	arch_register_req_type_normal            = 1U << 0,
	/** Only a real subset of the class is allowed. */
	arch_register_req_type_limited           = 1U << 1,
	/** The register should be equal to another one at the node. */
	arch_register_req_type_should_be_same    = 1U << 2,
	/** The register must be unequal from some other at the node. */
	arch_register_req_type_must_be_different = 1U << 3,
	/** The registernumber should be aligned (in case of multiregister values)*/
	arch_register_req_type_aligned           = 1U << 4,
	/** ignore while allocating registers */
	arch_register_req_type_ignore            = 1U << 5,
	/** the output produces a new value for the stack pointer
	 * (this is not really a constraint but a marker to guide the stackpointer
	 * rewiring logic) */
	arch_register_req_type_produces_sp       = 1U << 6,
} arch_register_req_type_t;
ENUM_BITSET(arch_register_req_type_t)

extern arch_register_req_t const arch_no_requirement;
#define arch_no_register_req (&arch_no_requirement)

void arch_set_frame_offset(ir_node *irn, int bias);

ir_entity *arch_get_frame_entity(const ir_node *irn);

int arch_get_sp_bias(ir_node *irn);

int arch_get_op_estimated_cost(const ir_node *irn);

void arch_perform_memory_operand(ir_node *irn, unsigned i);

/**
 * Get the register allocated for a value.
 */
const arch_register_t *arch_get_irn_register(const ir_node *irn);

/**
 * Assign register to a value
 */
void arch_set_irn_register(ir_node *irn, const arch_register_t *reg);

/**
 * Set the register for a certain output operand.
 */
void arch_set_irn_register_out(ir_node *irn, unsigned pos, const arch_register_t *r);

const arch_register_t *arch_get_irn_register_out(const ir_node *irn, unsigned pos);
const arch_register_t *arch_get_irn_register_in(const ir_node *irn, int pos);

/**
 * Get register constraints for an operand at position @p
 */
static inline const arch_register_req_t *arch_get_irn_register_req_in(
		const ir_node *node, int pos)
{
	const backend_info_t *info = be_get_info(node);
	return info->in_reqs[pos];
}

/**
 * Get register constraint for a produced result (the @p pos result)
 */
static inline const arch_register_req_t *arch_get_irn_register_req_out(
		const ir_node *node, unsigned pos)
{
	const backend_info_t *info = be_get_info(node);
	return info->out_infos[pos].req;
}

static inline void arch_set_irn_register_req_out(ir_node *node, unsigned pos,
		const arch_register_req_t *req)
{
	backend_info_t *info = be_get_info(node);
	assert(pos < (unsigned)ARR_LEN(info->out_infos));
	info->out_infos[pos].req = req;
}

static inline void arch_set_irn_register_reqs_in(ir_node *node,
		const arch_register_req_t **reqs)
{
	backend_info_t *info = be_get_info(node);
	info->in_reqs = reqs;
}

static inline const arch_register_req_t **arch_get_irn_register_reqs_in(
		const ir_node *node)
{
	backend_info_t *info = be_get_info(node);
	return info->in_reqs;
}

static inline reg_out_info_t *get_out_info(const ir_node *node)
{
	assert(get_irn_mode(node) != mode_T);
	size_t pos = 0;
	if (is_Proj(node)) {
		pos  = get_Proj_num(node);
		node = get_Proj_pred(node);
	}

	const backend_info_t *info = be_get_info(node);
	assert(pos < ARR_LEN(info->out_infos));
	return &info->out_infos[pos];
}

static inline const arch_register_req_t *arch_get_irn_register_req(const ir_node *node)
{
	reg_out_info_t *out = get_out_info(node);
	return out->req;
}

/**
 * Get the flags of a node.
 * @param irn The node.
 * @return The flags.
 */
static inline arch_irn_flags_t arch_get_irn_flags(const ir_node *node)
{
	backend_info_t const *const info = be_get_info(node);
	return info->flags;
}

void arch_set_irn_flags(ir_node *node, arch_irn_flags_t flags);

void arch_add_irn_flags(ir_node *node, arch_irn_flags_t flags);

/**
 * Returns true if the given node should not be scheduled (has
 * arch_irn_flag_not_scheduled flag seet)
 */
static inline bool arch_is_irn_not_scheduled(const ir_node *node)
{
	return is_Proj(node)
	    || (arch_get_irn_flags(node) & arch_irn_flag_not_scheduled);
}

#define arch_irn_is(irn, flag) ((arch_get_irn_flags(irn) & arch_irn_flag_ ## flag) != 0)

static inline unsigned arch_get_irn_n_outs(const ir_node *node)
{
	backend_info_t *const info = be_get_info(node);
	return (unsigned)ARR_LEN(info->out_infos);
}

#define be_foreach_out(node, i) \
	for (unsigned i = 0, i##__n = arch_get_irn_n_outs(node); i != i##__n; ++i)

/**
 * Register an instruction set architecture
 */
void be_register_isa_if(const char *name, const arch_isa_if_t *isa);

/**
 * A register.
 */
struct arch_register_t {
	const char                  *name;         /**< The name of the register. */
	arch_register_class_t const *cls;          /**< The class of the register */
	/** register constraint allowing just this register */
	const arch_register_req_t   *single_req;
	arch_register_type_t         type;         /**< The type of the register. */
	unsigned short               index;        /**< The index of the register in
	                                                the class. */
	unsigned short               global_index; /**< The global index this
												    register in the architecture. */
	/** register number in dwarf debugging format */
	unsigned short               dwarf_number;
	/** register number in instruction encoding */
	unsigned short               encoding;
};

/**
 * A class of registers.
 * Like general purpose or floating point.
 */
struct arch_register_class_t {
	const char                  *name;   /**< The name of the register class.*/
	ir_mode                     *mode;   /**< The mode of the register class.*/
	const arch_register_t       *regs;   /**< The array of registers. */
	const arch_register_req_t   *class_req;
	unsigned                     index;  /**< index of this register class */
	unsigned                     n_regs; /**< Number of registers in this
	                                          class. */
	arch_register_class_flags_t  flags;  /**< register class flags. */
};

static inline const arch_register_t *arch_register_for_index(
		const arch_register_class_t *cls, unsigned idx)
{
	assert(idx < cls->n_regs);
	return &cls->regs[idx];
}

/**
 * Convenience macro to check for set constraints.
 * @param req   A pointer to register requirements.
 * @param kind  The kind of constraint to check for
 *              (see arch_register_req_type_t).
 * @return      1, If the kind of constraint is present, 0 if not.
 */
#define arch_register_req_is(req, kind) \
	(((req)->type & (arch_register_req_type_ ## kind)) != 0)

/**
 * Expresses requirements to register allocation for an operand.
 */
struct arch_register_req_t {
	/** The register class this constraint belongs to. */
	const arch_register_class_t *cls;
	/** allowed register bitset (in case of wide-values this is only about the
	 * first register) */
	const unsigned              *limited;
	arch_register_req_type_t     type; /**< The type of the constraint. */
	/** Bitmask of ins which should use the same register (should_be_same). */
	unsigned                     other_same;
	/** Bitmask of ins which shall use a different register (must_be_different) */
	unsigned                     other_different;
	/** Specifies how many sequential registers are required */
	unsigned char                width;
};

static inline bool reg_reqs_equal(const arch_register_req_t *req1,
                                  const arch_register_req_t *req2)
{
	if (req1 == req2)
		return true;

	if (req1->type              != req2->type            ||
	    req1->cls               != req2->cls             ||
	    req1->other_same        != req2->other_same      ||
	    req1->other_different   != req2->other_different ||
	    (req1->limited != NULL) != (req2->limited != NULL))
		return false;

	if (req1->limited != NULL) {
		if (!rbitsets_equal(req1->limited, req2->limited, req1->cls->n_regs))
			return false;
	}

	return true;
}

struct arch_irn_ops_t {
	/**
	 * Get the entity on the stack frame this node depends on.
	 * @param irn  The node in question.
	 * @return The entity on the stack frame or NULL, if the node does not have
	 *         a stack frame entity.
	 */
	ir_entity *(*get_frame_entity)(const ir_node *irn);

	/**
	 * Set the offset of a node carrying an entity on the stack frame.
	 * @param irn  The node.
	 * @param offset The offset of the node's stack frame entity.
	 */
	void (*set_frame_offset)(ir_node *irn, int offset);

	/**
	 * Returns the delta of the stackpointer for nodes that increment or
	 * decrement the stackpointer with a constant value. (push, pop
	 * nodes on most architectures).
	 * A positive value stands for an expanding stack area, a negative value for
	 * a shrinking one.
	 *
	 * @param irn       The node
	 * @return          0 if the stackpointer is not modified with a constant
	 *                  value, otherwise the increment/decrement value
	 */
	int (*get_sp_bias)(const ir_node *irn);

	/**
	 * Get the estimated cycle count for @p irn.
	 *
	 * @param irn  The node.
	 * @return     The estimated cycle count for this operation
	 */
	int (*get_op_estimated_cost)(const ir_node *irn);

	/**
	 * Ask the backend to assimilate @p reload of operand @p i into @p irn.
	 *
	 * @param irn    The node.
	 * @param i      The position of the reload.
	 */
	void (*perform_memory_operand)(ir_node *irn, unsigned i);
};

/**
 * Architecture interface.
 */
struct arch_isa_if_t {
	/**
	 * Initializes the isa interface. This is necessary before calling any
	 * other functions from this interface.
	 */
	void (*init)(void);

	/**
	 * Fress resources allocated by this isa interface.
	 */
	void (*finish)(void);

	/**
	 * Returns the frontend settings needed for this backend.
	 */
	const backend_params *(*get_params)(void);

	/**
	 * lowers current program for target. See the documentation for
	 * be_lower_for_target() for details.
	 */
	void (*lower_for_target)(void);

	/**
	 * returns true if the string is a valid clobbered (register) in this
	 * backend
	 */
	int (*is_valid_clobber)(const char *clobber);

	/**
	 * Start codegeneration
	 * @return a new isa instance
	 */
	arch_env_t *(*begin_codegeneration)(void);

	/**
	 * Free the isa instance.
	 */
	void (*end_codegeneration)(void *self);

	/**
	 * mark node as rematerialized
	 */
	void (*mark_remat)(ir_node *node);

	/**
	 * Create a spill instruction. We assume that spill instructions do not need
	 * any additional registers and do not affect cpu-flags in any way.
	 * Construct a sequence of instructions after @p after (the resulting nodes
	 * are already scheduled).
	 * Returns a mode_M value which is used as input for a reload instruction.
	 */
	ir_node *(*new_spill)(ir_node *value, ir_node *after);

	/**
	 * Create a reload instruction. We assume that reload instructions do not
	 * need any additional registers and do not affect cpu-flags in any way.
	 * Constructs a sequence of instruction before @p before (the resulting
	 * nodes are already scheduled). A rewiring of users is not performed in
	 * this function.
	 * Returns a value representing the restored value.
	 */
	ir_node *(*new_reload)(ir_node *value, ir_node *spilled_value,
	                       ir_node *before);

	/**
	 * Called directly after initialization. Backend should handle all
	 * intrinsics here.
	 */
	void (*handle_intrinsics)(ir_graph *irg);

	/**
	 * Initialize a graph for codegeneration. Code selection is usually
	 * performed in this step.
	 */
	void (*prepare_graph)(ir_graph *irg);

	/**
	 * Called before register allocation.
	 */
	void (*before_ra)(ir_graph *irg);

	/**
	 * Last step in the backend. Called after register allocation.
	 * May perform peephole optimizations and legalizations and finally emit
	 * the code.
	 */
	void (*emit)(ir_graph *irg);
};

#define arch_env_end_codegeneration(env)               ((env)->impl->end_codegeneration(env))
#define arch_env_get_call_abi(env,tp,abi)              ((env)->impl->get_call_abi((tp), (abi)))
#define arch_env_mark_remat(env,node) \
	do { if ((env)->impl->mark_remat != NULL) (env)->impl->mark_remat((node)); } while(0)

#define arch_env_new_spill(env,value,after)            ((env)->impl->new_spill(value, after))
#define arch_env_new_reload(env,value,spilled,before)  ((env)->impl->new_reload(value, spilled, before))

/**
 * ISA base class.
 */
struct arch_env_t {
	const arch_isa_if_t   *impl;
	unsigned               n_registers;     /**< number of registers */
	const arch_register_t *registers;       /**< register array */
	/** number of register classes*/
	unsigned               n_register_classes;
	/** register classes */
	const arch_register_class_t *register_classes;
	const arch_register_t *sp;              /**< The stack pointer register. */
	const arch_register_t *bp;              /**< The base pointer register. */
	unsigned               spill_cost;      /**< cost for a be_Spill node */
	unsigned               reload_cost;     /**< cost for a be_Reload node */
};

static inline bool arch_irn_is_ignore(const ir_node *irn)
{
	const arch_register_req_t *req = arch_get_irn_register_req(irn);
	return arch_register_req_is(req, ignore);
}

static inline bool arch_irn_consider_in_reg_alloc(
		const arch_register_class_t *cls, const ir_node *node)
{
	const arch_register_req_t *req = arch_get_irn_register_req(node);
	return req->cls == cls && !arch_register_req_is(req, ignore);
}

#define be_foreach_value(node, value, code) \
	do { \
		if (get_irn_mode(node) == mode_T) { \
			foreach_out_edge(node, node##__edge) { \
				ir_node *const value = get_edge_src_irn(node##__edge); \
				if (!is_Proj(value)) \
					continue; \
				code \
			} \
		} else { \
			ir_node *const value = node; \
			code \
		} \
	} while (0)

#define be_foreach_definition_(node, ccls, value, req, code) \
	be_foreach_value(node, value, \
		arch_register_req_t const *const req = arch_get_irn_register_req(value); \
		if (req->cls != ccls) \
			continue; \
		code \
	)

/**
 * Iterate over all values defined by an instruction.
 * Only looks at values in a certain register class where the requirements
 * are not marked as ignore.
 * Executes @p code for each definition.
 */
#define be_foreach_definition(node, ccls, value, req, code) \
	be_foreach_definition_(node, ccls, value, req, \
		if (arch_register_req_is(req, ignore)) \
			continue; \
		code \
	)

#define be_foreach_use(node, ccls, in_req, value, value_req, code)           \
	do {                                                                     \
	for (int i_ = 0, n_ = get_irn_arity(node); i_ < n_; ++i_) {              \
		const arch_register_req_t *in_req = arch_get_irn_register_req_in(node, i_); \
		if (in_req->cls != ccls)                                             \
			continue;                                                        \
		ir_node                   *value     = get_irn_n(node, i_);              \
		const arch_register_req_t *value_req = arch_get_irn_register_req(value); \
		if (value_req->type & arch_register_req_type_ignore)                 \
			continue;                                                        \
		code                                                                 \
	}                                                                        \
	} while (0)

bool arch_reg_is_allocatable(const arch_register_req_t *req,
                             const arch_register_t *reg);

typedef struct be_start_info_t {
	unsigned pos;
	ir_node *irn;
} be_start_info_t;

void be_make_start_mem(be_start_info_t *info, ir_node *start, unsigned pos);

void be_make_start_out(be_start_info_t *info, struct obstack *obst, ir_node *start, unsigned pos, arch_register_t const *reg, arch_register_req_type_t flags);

ir_node *be_get_start_proj(ir_graph *irg, be_start_info_t *info);

#endif
