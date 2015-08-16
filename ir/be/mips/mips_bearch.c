/*
 * This file is part of libFirm.
 * Copyright (C) 2016 University of Karlsruhe.
 */

#include "be_t.h"
#include "bearch.h"
#include "bemodule.h"
#include "benode.h"
#include "bera.h"
#include "besched.h"
#include "bespillslots.h"
#include "gen_mips_new_nodes.h"
#include "gen_mips_regalloc_if.h"
#include "iredges.h"
#include "irgwalk.h"
#include "irprog_t.h"
#include "lower_dw.h"
#include "mips_emitter.h"
#include "mips_transform.h"
#include "panic.h"

static int mips_is_mux_allowed(ir_node *const sel, ir_node *const mux_false, ir_node *const mux_true)
{
	(void)sel;
	(void)mux_false;
	(void)mux_true;
	return false;
}

static backend_params mips_backend_params = {
	.byte_order_big_endian         = false,
	.pic_supported                 = false,
	.unaligned_memaccess_supported = false,
	.modulo_shift                  = 32,
	.dep_param                     = NULL, // TODO
	.allow_ifconv                  = &mips_is_mux_allowed,
	.machine_size                  = 32,
	.mode_float_arithmetic         = NULL,  /* will be set later */ // TODO
	.type_long_long                = NULL,  /* will be set later */ // TODO
	.type_unsigned_long_long       = NULL,  /* will be set later */ // TODO
	.type_long_double              = NULL,  /* will be set later */ // TODO
	.stack_param_align             = 4,
	.float_int_overflow            = ir_overflow_indefinite,
};

static void mips_init(void)
{
	mips_create_opcodes();
	mips_register_init();
}

static void mips_finish(void)
{
	mips_free_opcodes();
}

static const backend_params *mips_get_libfirm_params(void)
{
	return &mips_backend_params;
}

static void mips_select_instructions(ir_graph *const irg)
{
	be_timer_push(T_CODEGEN);
	mips_transform_graph(irg);
	be_timer_pop(T_CODEGEN);
	be_dump(DUMP_BE, irg, "code-selection");

	place_code(irg);
	be_dump(DUMP_BE, irg, "place");
}

static bool mode_needs_gp_reg(ir_mode *const mode)
{
	return mode_is_int(mode) || mode_is_reference(mode);
}

static ir_node *mips_new_spill(ir_node *const value, ir_node *const after)
{
	ir_mode *const mode = get_irn_mode(value);
	if (mode_needs_gp_reg(mode)) {
		ir_node  *const block = get_block(after);
		ir_graph *const irg   = get_irn_irg(after);
		ir_node  *const nomem = get_irg_no_mem(irg);
		ir_node  *const frame = get_irg_frame(irg);
		ir_node  *const store = new_bd_mips_sw(NULL, block, nomem, frame, value, NULL, 0);
		sched_add_after(after, store);
		return store;
	}
	panic("TODO");
}

static ir_node *mips_new_reload(ir_node *const value, ir_node *const spill, ir_node *const before)
{
	ir_mode *const mode = get_irn_mode(value);
	if (mode_needs_gp_reg(mode)) {
		ir_node  *const block = get_block(before);
		ir_graph *const irg   = get_irn_irg(before);
		ir_node  *const frame = get_irg_frame(irg);
		ir_node  *const load  = new_bd_mips_lw(NULL, block, spill, frame, NULL, 0);
		sched_add_before(before, load);
		return be_new_Proj(load, pn_mips_lw_res);
	}
	panic("TODO");
}

static regalloc_if_t const mips_regalloc_if = {
	.spill_cost  = 7,
	.reload_cost = 5,
	.new_spill   = mips_new_spill,
	.new_reload  = mips_new_reload,
};

static void mips_collect_frame_entity_nodes(ir_node *const node, void *const data)
{
	be_fec_env_t *const env = (be_fec_env_t*)data;

	if (is_mips_lw(node)) {
		ir_node  *const base  = get_irn_n(node, n_mips_lw_base);
		ir_graph *const irg   = get_irn_irg(node);
		ir_node  *const frame = get_irg_frame(irg);
		if (base == frame) {
			ir_type *const type = get_type_for_mode(mode_Iu); /* TODO */
			be_load_needs_frame_entity(env, node, type);
		}
	}
}

static void mips_set_frame_entity(ir_node *const node, ir_entity *const entity, ir_type const *const type)
{
	(void)type; /* TODO */

	mips_immediate_attr_t *const imm = get_mips_immediate_attr(node);
	imm->ent = entity;
}

static void mips_assign_spill_slots(ir_graph *const irg)
{
	ir_type *const frame_type = get_irg_frame_type(irg);
	default_layout_compound_type(frame_type);

	be_fec_env_t *const fec_env = be_new_frame_entity_coalescer(irg);
	irg_walk_graph(irg, NULL, mips_collect_frame_entity_nodes, fec_env);
	be_assign_entities(fec_env, mips_set_frame_entity, true);
	be_free_frame_entity_coalescer(fec_env);
}

static ir_node *mips_new_IncSP(ir_node *const block, ir_node *const sp, int const offset, unsigned const align)
{
	return be_new_IncSP(&mips_registers[REG_SP], block, sp, offset, align);
}

static void mips_introduce_prologue(ir_graph *const irg, unsigned const frame_size)
{
	ir_node  *const start    = get_irg_start(irg);
	ir_node  *const block    = get_nodes_block(start);
	ir_node  *const start_sp = be_get_Start_proj(irg, &mips_registers[REG_SP]);
	ir_node  *const inc_sp   = mips_new_IncSP(block, start_sp, frame_size, 0);
	sched_add_after(start, inc_sp);
	edges_reroute_except(start_sp, inc_sp, inc_sp);
}

static void mips_introduce_epilogue(ir_node *const ret, unsigned const frame_size)
{
	ir_node  *const block  = get_nodes_block(ret);
	ir_node  *const ret_sp = get_irn_n(ret, n_mips_jr_stack);
	ir_node  *const inc_sp = mips_new_IncSP(block, ret_sp, -(int)frame_size, 0);
	sched_add_before(ret, inc_sp);
	set_irn_n(ret, n_mips_jr_stack, inc_sp);
}

static void mips_introduce_prologue_epilogue(ir_graph *const irg)
{
	ir_type  *const frame_type = get_irg_frame_type(irg);
	unsigned  const frame_size = get_type_size(frame_type);
	if (frame_size == 0)
		return;

	foreach_irn_in(get_irg_end_block(irg), i, ret) {
		assert(is_mips_jr(ret));
		mips_introduce_epilogue(ret, frame_size);
	}

	mips_introduce_prologue(irg, frame_size);
}

static void mips_resolve_frame_entities_walker(ir_node *const node, void *const env)
{
	ir_type *const frame_type = (ir_type*)env;

	/* TODO */
	if (is_mips_lw(node) || is_mips_sw(node)) {
		mips_immediate_attr_t *const imm = get_mips_immediate_attr(node);
		ir_entity             *const ent = imm->ent;
		if (ent && get_entity_owner(ent) == frame_type) {
			imm->ent  = NULL;
			imm->val += get_entity_offset(ent);
		}
	}
}

static void mips_resolve_frame_entities(ir_graph *const irg)
{
	ir_type *const frame_type = get_irg_frame_type(irg);
	irg_walk_graph(irg, NULL, mips_resolve_frame_entities_walker, frame_type);
}

static void mips_generate_code(FILE *const output, char const *const cup_name)
{
	be_begin(output, cup_name);

	foreach_irp_irg(i, irg) {
		if (!be_step_first(irg))
			continue;
		// TODO be_birg_from_irg(irg)->non_ssa_regs = sp_is_non_ssa;
		mips_select_instructions(irg);
		be_step_schedule(irg);
		be_step_regalloc(irg, &mips_regalloc_if);
		mips_assign_spill_slots(irg);
		mips_introduce_prologue_epilogue(irg);
		mips_resolve_frame_entities(irg);
		mips_emit_function(irg);
		be_step_last(irg);
	}

	be_finish();
}

static void mips_lower64(void)
{
	ir_mode *const word_unsigned = mips_reg_classes[CLASS_mips_gp].mode;
	ir_mode *const word_signed   = find_signed_mode(word_unsigned);
	lwrdw_param_t lower_dw_params = {
		// TODO .create_intrinsic = mips_create_instrinsic_fct,
		.word_unsigned    = word_unsigned,
		.word_signed      = word_signed,
		.doubleword_size  = 64,
		.big_endian       = be_is_big_endian(),
	};

	ir_prepare_dw_lowering(&lower_dw_params);
	// TODO
	ir_lower_dw_ops();
}

static void mips_lower_for_target(void)
{
	mips_lower64();
	// TODO
}

static unsigned mips_get_op_estimated_cost(ir_node const *const node)
{
#if 0 // TODO
	if (is_mips_Load(node))
		return 5;
	if (is_mips_Store(node))
		return 7;
#else
	(void)node;
#endif
	return 1;
}

static arch_isa_if_t const mips_isa_if = {
	.n_registers           = N_MIPS_REGISTERS,
	.registers             = mips_registers,
	.n_register_classes    = N_MIPS_CLASSES,
	.register_classes      = mips_reg_classes,
	.init                  = mips_init,
	.finish                = mips_finish,
	.get_params            = mips_get_libfirm_params,
	.generate_code         = mips_generate_code,
	.lower_for_target      = mips_lower_for_target,
	// TODO .is_valid_clobber      = mips_is_valid_clobber,
	.get_op_estimated_cost = mips_get_op_estimated_cost,
};

BE_REGISTER_MODULE_CONSTRUCTOR(be_init_arch_mips)
void be_init_arch_mips(void)
{
	be_register_isa_if("mips", &mips_isa_if);
}
