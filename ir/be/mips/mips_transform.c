/*
 * This file is part of libFirm.
 * Copyright (C) 2016 University of Karlsruhe.
 */

#include "mips_transform.h"

#include "beirg.h"
#include "benode.h"
#include "betranshlp.h"
#include "gen_mips_new_nodes.h"
#include "gen_mips_regalloc_if.h"
#include "nodes.h"
#include "panic.h"
#include "util.h"

static unsigned const callee_saves[] = {
	REG_S0,
	REG_S1,
	REG_S2,
	REG_S3,
	REG_S4,
	REG_S5,
	REG_S6,
	REG_S7,
};

static unsigned const param_regs_gp[] = {
	REG_A0,
	REG_A1,
	REG_A2,
	REG_A3,
};

static ir_node *get_Start_sp(ir_graph *const irg)
{
	return be_get_Start_proj(irg, &mips_registers[REG_SP]);
}

static ir_node *get_Start_zero(ir_graph *const irg)
{
	return be_get_Start_proj(irg, &mips_registers[REG_ZERO]);
}

static inline bool is_simm16(long const val)
{
	return -32768 <= val && val < 32768;
}

static inline bool is_uimm16(long const val)
{
	return 0 <= val && val < 65536;
}

static ir_node *gen_Add(ir_node *const node)
{
	ir_node *const l    = get_Add_left(node);
	ir_node *const r    = get_Add_right(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_is_int(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const new_l = be_transform_node(l);
		if (is_Const(r)) {
			long const val = get_Const_long(r);
			if (is_simm16(val))
				return new_bd_mips_addiu(dbgi, block, new_l, val);
		}
		ir_node  *const new_r = be_transform_node(r);
		return new_bd_mips_addu(dbgi, block, new_l, new_r);
	}
	panic("undhandled Add");
}

static ir_node *gen_Const(ir_node *const node)
{
	ir_mode *const mode = get_irn_mode(node);;
	if (mode_is_int(mode)) {
		long const val = get_Const_long(node);
		if (val == 0) {
			ir_graph *const irg = get_irn_irg(node);
			return get_Start_zero(irg);
		} else if (is_simm16(val)) {
			dbg_info *const dbgi  = get_irn_dbg_info(node);
			ir_node  *const block = be_transform_nodes_block(node);
			ir_graph *const irg   = get_irn_irg(node);
			ir_node  *const zero  = get_Start_zero(irg);
			return new_bd_mips_addiu(dbgi, block, zero, val);
		} else {
			ir_node        *res;
			dbg_info *const dbgi  = get_irn_dbg_info(node);
			ir_node  *const block = be_transform_nodes_block(node);
			int32_t   const hi    = (uint32_t)val >> 16;
			if (hi != 0) {
				res = new_bd_mips_lui(dbgi, block, hi);
			} else {
				ir_graph *const irg = get_irn_irg(node);
				res = get_Start_zero(irg);
			}
			int32_t const lo = val & 0xFFFF;
			if (lo != 0)
				res = new_bd_mips_ori(dbgi, block, res, lo);
			return res;
		}
	}
	panic("unhandled Const");
}

static ir_node *gen_Proj_Proj_Start(ir_node *const node)
{
	assert(get_Proj_num(get_Proj_pred(node)) == pn_Start_T_args);

	ir_graph *const irg = get_irn_irg(node);
	unsigned  const num = get_Proj_num(node);
	assert(num < ARRAY_SIZE(param_regs_gp));
	return be_get_Start_proj(irg, &mips_registers[param_regs_gp[num]]);
}

static ir_node *gen_Proj_Proj(ir_node *const node)
{
	ir_node *const pred      = get_Proj_pred(node);
	ir_node *const pred_pred = get_Proj_pred(pred);
	if (is_Start(pred_pred)) {
		return gen_Proj_Proj_Start(node);
	} else {
		panic("unexpected Proj-Proj");
	}
}

static ir_node *gen_Proj_Start(ir_node *const node)
{
	ir_graph *const irg = get_irn_irg(node);
	switch ((pn_Start)get_Proj_num(node)) {
	case pn_Start_M:            return be_get_Start_mem(irg);
	case pn_Start_P_frame_base: return get_Start_sp(irg);
	case pn_Start_T_args:       return new_r_Bad(irg, mode_T);
	}
	panic("unexpected Proj");
}

static ir_node *gen_Return(ir_node *const node)
{
	unsigned       p     = n_mips_jr_first_result;
	unsigned const n_res = get_Return_n_ress(node);
	unsigned const n_ins = p + n_res + ARRAY_SIZE(callee_saves) + 1 /* fp */;

	ir_graph                   *const irg  = get_irn_irg(node);
	arch_register_req_t const **const reqs = be_allocate_in_reqs(irg, n_ins);
	ir_node                   **const in   = ALLOCAN(ir_node*, n_ins);

	ir_node *const mem = get_Return_mem(node);
	in[n_mips_jr_mem]   = be_transform_node(mem);
	reqs[n_mips_jr_mem] = arch_memory_req;

	in[n_mips_jr_stack]   = get_Start_sp(irg); // TODO
	reqs[n_mips_jr_stack] = &mips_single_reg_req_gp_sp;

	in[n_mips_jr_addr]    = be_get_Start_proj(irg, &mips_registers[REG_RA]);
	reqs[n_mips_jr_addr]  = &mips_class_reg_req_gp;

	if (n_res != 0) {
		if (n_res > 2)
			panic("too many return values");
		ir_node *const res0     = get_Return_res(node, 0);
		ir_mode *const res_mode = get_irn_mode(res0);
		if (mode_is_int(res_mode)) {
			static arch_register_req_t const *const res_reqs[] = {
				&mips_single_reg_req_gp_v0,
				&mips_single_reg_req_gp_v1,
			};
			for (size_t i = 0; i != n_res; ++i) {
				ir_node *const res = get_Return_res(node, i);
				in[p]   = be_transform_node(res);
				reqs[p] = res_reqs[i];
				++p;
			}
		} else {
			panic("only gp reutrn values supported yet");
		}
	}

	for (size_t i = 0; i != ARRAY_SIZE(callee_saves); ++i) {
		arch_register_t const *const reg = &mips_registers[callee_saves[i]];
		in[p]   = be_get_Start_proj(irg, reg);
		reqs[p] = reg->single_req;
		++p;
	}

	in[p]   = be_get_Start_proj(irg, &mips_registers[REG_FP]);
	reqs[p] = &mips_single_reg_req_gp_fp;
	++p;

	assert (p == n_ins);
	dbg_info *const dbgi  = get_irn_dbg_info(node);
	ir_node  *const block = be_transform_nodes_block(node);
	ir_node  *const jr    = new_bd_mips_jr(dbgi, block, n_ins, in, reqs);
	return jr;
}

static ir_node *gen_Start(ir_node *const node)
{
	be_start_out outs[N_MIPS_REGISTERS] = {
		[REG_ZERO] = BE_START_IGNORE,
		[REG_SP]   = BE_START_IGNORE,
		[REG_FP]   = BE_START_IGNORE,
		[REG_RA]   = BE_START_REG,
	};
	for (size_t i = 0; i != ARRAY_SIZE(callee_saves); ++i) {
		outs[callee_saves[i]] = BE_START_REG;
	}

	ir_graph  *const irg  = get_irn_irg(node);
	ir_entity *const ent  = get_irg_entity(irg);
	ir_type   *const type = get_entity_type(ent);
	unsigned         n_gp = 0;
	for (size_t i = 0, n = get_method_n_params(type); i != n; ++i) {
		ir_type *const param_type = get_method_param_type(type, i);
		ir_mode *const param_mode = get_type_mode(param_type);
		if (mode_is_int(param_mode)) {
			if (n_gp == ARRAY_SIZE(param_regs_gp))
				panic("memory parameters not supported yet");
			outs[param_regs_gp[n_gp++]] = BE_START_REG;
		} else {
			panic("unsupported param mode");
		}
	}

	return be_new_Start(irg, outs);
}

static ir_node *gen_Sub(ir_node *const node)
{
	ir_node *const l    = get_Sub_left(node);
	ir_node *const r    = get_Sub_right(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_is_int(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const new_l = be_transform_node(l);
		ir_node  *const new_r = be_transform_node(r);
		return new_bd_mips_subu(dbgi, block, new_l, new_r);
	}
	panic("undhandled Sub");
}

static void mips_register_transformers(void)
{
	be_start_transform_setup();

	be_set_transform_function(op_Add,    gen_Add);
	be_set_transform_function(op_Const,  gen_Const);
	be_set_transform_function(op_Return, gen_Return);
	be_set_transform_function(op_Start,  gen_Start);
	be_set_transform_function(op_Sub,    gen_Sub);

	be_set_transform_proj_function(op_Start, gen_Proj_Start);
	be_set_transform_proj_function(op_Proj,  gen_Proj_Proj);
}

static void mips_set_allocatable_regs(ir_graph *const irg)
{
	be_irg_t       *const birg = be_birg_from_irg(irg);
	struct obstack *const obst = &birg->obst;

	unsigned *const a = rbitset_obstack_alloc(obst, N_MIPS_REGISTERS);
	rbitset_set(a, REG_V0);
	rbitset_set(a, REG_V1);
	rbitset_set(a, REG_A0);
	rbitset_set(a, REG_A1);
	rbitset_set(a, REG_A2);
	rbitset_set(a, REG_A3);
	rbitset_set(a, REG_T0);
	rbitset_set(a, REG_T1);
	rbitset_set(a, REG_T2);
	rbitset_set(a, REG_T3);
	rbitset_set(a, REG_T4);
	rbitset_set(a, REG_T5);
	rbitset_set(a, REG_T6);
	rbitset_set(a, REG_T7);
	rbitset_set(a, REG_S0);
	rbitset_set(a, REG_S1);
	rbitset_set(a, REG_S2);
	rbitset_set(a, REG_S3);
	rbitset_set(a, REG_S4);
	rbitset_set(a, REG_S5);
	rbitset_set(a, REG_S6);
	rbitset_set(a, REG_S7);
	rbitset_set(a, REG_T8);
	rbitset_set(a, REG_T9);
	rbitset_set(a, REG_RA);
	birg->allocatable_regs = a;
}

void mips_transform_graph(ir_graph *const irg)
{
	mips_register_transformers();
	mips_set_allocatable_regs(irg);
	be_transform_graph(irg, NULL);
}
