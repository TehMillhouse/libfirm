/*
 * This file is part of libFirm.
 * Copyright (C) 2016 University of Karlsruhe.
 */

#include "mips_transform.h"

#include <limits.h>

#include "beirg.h"
#include "benode.h"
#include "betranshlp.h"
#include "gen_mips_new_nodes.h"
#include "gen_mips_regalloc_if.h"
#include "nodes.h"
#include "panic.h"
#include "util.h"

static bool mode_needs_gp_reg(ir_mode *const mode)
{
	return mode_is_int(mode) || mode_is_reference(mode);
}

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

static unsigned const caller_saves[] = {
	// TODO REG_AT,
	REG_V0,
	REG_V1,
	REG_A0,
	REG_A1,
	REG_A2,
	REG_A3,
	REG_T0,
	REG_T1,
	REG_T2,
	REG_T3,
	REG_T4,
	REG_T5,
	REG_T6,
	REG_T7,
	REG_T8,
	REG_T9,
	REG_RA,
};

static unsigned const param_regs_gp[] = {
	REG_A0,
	REG_A1,
	REG_A2,
	REG_A3,
};

static unsigned const result_regs_gp[] = {
	REG_V0,
	REG_V1,
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

static ir_node *make_address(dbg_info *const dbgi, ir_node *const block, ir_entity *const ent, int32_t const val)
{
	ir_node *const lui = new_bd_mips_lui(dbgi, block, ent, val);
	return new_bd_mips_addiu(dbgi, block, lui, ent, val);
}

static ir_node *gen_Add(ir_node *const node)
{
	ir_node *const l    = get_Add_left(node);
	ir_node *const r    = get_Add_right(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		if (is_Const(r)) {
			long const val = get_Const_long(r);
			if (is_Address(l)) {
				ir_entity *const ent = get_Address_entity(node);
				return make_address(dbgi, block, ent, val);
			}
			if (is_simm16(val)) {
				ir_node *const new_l = be_transform_node(l);
				return new_bd_mips_addiu(dbgi, block, new_l, NULL, val);
			}
		}
		ir_node *const new_l = be_transform_node(l);
		ir_node *const new_r = be_transform_node(r);
		return new_bd_mips_addu(dbgi, block, new_l, new_r);
	}
	panic("TODO");
}

static ir_node *gen_Address(ir_node *const node)
{
	dbg_info  *const dbgi  = get_irn_dbg_info(node);
	ir_node   *const block = be_transform_nodes_block(node);
	ir_entity *const ent   = get_Address_entity(node);
	return make_address(dbgi, block, ent, 0);
}

typedef ir_node *cons_binop(dbg_info*, ir_node*, ir_node*, ir_node*);
typedef ir_node *cons_binop_imm(dbg_info*, ir_node*, ir_node*, ir_entity*, int32_t);

static ir_node *gen_logic_op(ir_node *const node, cons_binop *const cons, cons_binop_imm *const cons_imm)
{
	dbg_info *const dbgi  = get_irn_dbg_info(node);
	ir_node  *const block = be_transform_nodes_block(node);
	ir_node  *const l     = get_binop_left(node);
	ir_node  *const new_l = be_transform_node(l);
	ir_node  *const r     = get_binop_right(node);
	if (is_Const(r)) {
		long const val = get_Const_long(r);
		if (is_uimm16(val))
			return cons_imm(dbgi, block, new_l, NULL, val);
	}
	ir_node *const new_r = be_transform_node(r);
	return cons(dbgi, block, new_l, new_r);
}

static ir_node *gen_And(ir_node *const node)
{
	return gen_logic_op(node, &new_bd_mips_and, &new_bd_mips_andi);
}

static ir_node *gen_Call(ir_node *const node)
{
	ir_node *const ptr = get_Call_ptr(node);
	if (is_Address(ptr)) {
		ir_graph *const irg = get_irn_irg(node);

		unsigned                          p        = n_mips_jal_first_argument;
		unsigned                    const n_params = get_Call_n_params(node);
		unsigned                    const n_ins    = p + n_params;
		arch_register_req_t const **const reqs     = be_allocate_in_reqs(irg, n_ins);
		ir_node                          *ins[n_ins];

		ir_node *const mem = get_Call_mem(node);
		ins[n_mips_jal_mem]  = be_transform_node(mem);
		reqs[n_mips_jal_mem] = arch_memory_req;

		unsigned n_gp = 0;
		for (size_t i = 0; i != n_params; ++i) {
			ir_node *const param      = get_Call_param(node, i);
			ir_mode *const param_mode = get_irn_mode(param);
			if (mode_needs_gp_reg(param_mode)) {
				if (n_gp == ARRAY_SIZE(param_regs_gp))
					panic("memory parameters not supported yet");
				ins[p]  = be_transform_node(param);
				reqs[p] = mips_registers[param_regs_gp[n_gp++]].single_req;
				++p;
			} else {
				panic("unsupported param mode");
			}
		}

		unsigned const n_res = pn_mips_jal_first_result + ARRAY_SIZE(caller_saves);

		dbg_info  *const dbgi   = get_irn_dbg_info(node);
		ir_node   *const block  = be_transform_nodes_block(node);
		ir_entity *const callee = get_Address_entity(ptr);
		ir_node   *const jal    = new_bd_mips_jal(dbgi, block, n_ins, ins, reqs, n_res, callee);

		arch_set_irn_register_req_out(jal, pn_mips_jal_mem, arch_memory_req);
		for (size_t i = 0; i != ARRAY_SIZE(caller_saves); ++i) {
			arch_set_irn_register_req_out(jal, pn_mips_jal_first_result + i, mips_registers[caller_saves[i]].single_req);
		}

		return jal;
	}
	panic("TODO");
}

static ir_node *make_bcc(ir_node *const cond, ir_node *const l, ir_node *const r, mips_cond_t const cc)
{
	dbg_info *const dbgi  = get_irn_dbg_info(cond);
	ir_node  *const block = be_transform_nodes_block(cond);
	return new_bd_mips_bcc(dbgi, block, l, r, cc);
}

static ir_node *gen_Cond(ir_node *const node)
{
	ir_node *const sel = get_Cond_selector(node);
	if (is_Cmp(sel)) {
		ir_node *const l    = get_Cmp_left(sel);
		ir_node *const r    = get_Cmp_right(sel);
		ir_mode *const mode = get_irn_mode(l);
		if (mode_needs_gp_reg(mode)) {
			ir_relation const rel = get_Cmp_relation(sel);
			switch (rel) {
			{
				mips_cond_t cc;
			case ir_relation_equal:        cc = mips_cc_eq; goto bcc;
			case ir_relation_less_greater: cc = mips_cc_ne; goto bcc;
bcc:;
				ir_node *const new_l = be_transform_node(l);
				ir_node *const new_r = be_transform_node(r);
				return make_bcc(node, new_l, new_r, cc);
			}

			case ir_relation_greater:
			case ir_relation_less:
			case ir_relation_greater_equal:
				panic("TODO");

			case ir_relation_less_equal: {
				if (is_Const(r)) {
					long val = get_Const_long(r);
					if (val != LONG_MAX) {
						val += 1; /* set less than */
						cons_binop_imm *cons;
						if (mode_is_signed(mode)) {
							if (is_simm16(val)) {
								cons = &new_bd_mips_slti;
								goto bcc_ne;
							}
						} else {
							if (is_uimm16(val)) {
								cons = &new_bd_mips_sltiu;
bcc_ne:;
								dbg_info *const dbgi  = get_irn_dbg_info(sel);
								ir_node  *const block = be_transform_nodes_block(sel);
								ir_node  *const new_l = be_transform_node(l);
								ir_node  *const slti  = cons(dbgi, block, new_l, NULL, val);
								ir_graph *const irg   = get_irn_irg(node);
								ir_node  *const zero  = get_Start_zero(irg);
								return make_bcc(node, slti, zero, mips_cc_ne);
							}
						}
					}
				}
				panic("TODO");
			}

			case ir_relation_false:
			case ir_relation_less_equal_greater:
			case ir_relation_unordered:
			case ir_relation_unordered_equal:
			case ir_relation_unordered_less:
			case ir_relation_unordered_less_equal:
			case ir_relation_unordered_greater:
			case ir_relation_unordered_greater_equal:
			case ir_relation_unordered_less_greater:
			case ir_relation_true:
				panic("invalid relation");
			}
		}
	}
	panic("TODO");
}

static ir_node *gen_Conv(ir_node *const node)
{
	ir_node *const val      = get_Conv_op(node);
	ir_mode *const src_mode = get_irn_mode(val);
	ir_mode *const dst_mode = get_irn_mode(node);
	if (mode_needs_gp_reg(dst_mode) && mode_needs_gp_reg(src_mode)) {
		unsigned const dst_size = get_mode_size_bits(dst_mode);
		if (dst_size == 32) {
			if (is_Proj(val)) {
				ir_node *const pred = get_Proj_pred(val);
				if (is_Load(pred))
					return be_transform_node(val);
			}
		}
	}
	panic("TODO");
}

static ir_node *gen_Const(ir_node *const node)
{
	ir_mode *const mode = get_irn_mode(node);;
	if (mode_needs_gp_reg(mode)) {
		long const val = get_Const_long(node);
		if (val == 0) {
			ir_graph *const irg = get_irn_irg(node);
			return get_Start_zero(irg);
		} else if (is_simm16(val)) {
			dbg_info *const dbgi  = get_irn_dbg_info(node);
			ir_node  *const block = be_transform_nodes_block(node);
			ir_graph *const irg   = get_irn_irg(node);
			ir_node  *const zero  = get_Start_zero(irg);
			return new_bd_mips_addiu(dbgi, block, zero, NULL, val);
		} else {
			ir_node        *res;
			dbg_info *const dbgi  = get_irn_dbg_info(node);
			ir_node  *const block = be_transform_nodes_block(node);
			int32_t   const hi    = (uint32_t)val >> 16;
			if (hi != 0) {
				res = new_bd_mips_lui(dbgi, block, NULL, hi);
			} else {
				ir_graph *const irg = get_irn_irg(node);
				res = get_Start_zero(irg);
			}
			int32_t const lo = val & 0xFFFF;
			if (lo != 0)
				res = new_bd_mips_ori(dbgi, block, res, NULL, lo);
			return res;
		}
	}
	panic("TODO");
}

static ir_node *gen_Eor(ir_node *const node)
{
	return gen_logic_op(node, &new_bd_mips_xor, &new_bd_mips_xori);
}

static ir_node *gen_Jmp(ir_node *const node)
{
	dbg_info *const dbgi  = get_irn_dbg_info(node);
	ir_node  *const block = be_transform_nodes_block(node);
	return new_bd_mips_b(dbgi, block);
}

typedef struct mips_addr {
	ir_node   *base;
	ir_entity *ent;
	int32_t    val;
} mips_addr;

static mips_addr match_address(ir_node *ptr)
{
	mips_addr addr = {
		.base = NULL,
		.ent  = NULL, /* TODO */
		.val  = 0,
	};

	if (is_Add(ptr)) {
		ir_node *const r = get_Add_right(ptr);
		if (is_Const(r)) {
			long const val = get_Const_long(r);
			if (is_simm16(val)) {
				addr.val = val;
				ptr = get_Add_left(ptr);
			}
		}
	}

	if (is_Address(ptr)) {
		dbg_info *const dbgi  = get_irn_dbg_info(ptr);
		ir_node  *const block = be_transform_nodes_block(ptr);
		addr.ent  = get_Address_entity(ptr);
		addr.base = new_bd_mips_lui(dbgi, block, addr.ent, addr.val);
	} else {
		addr.base = be_transform_node(ptr);
	}

	return addr;
}

typedef ir_node *cons_loadop(dbg_info*, ir_node*, ir_node*, ir_node*, ir_entity*, int32_t);

static ir_node *gen_Load(ir_node *const node)
{
	ir_mode *const mode = get_Load_mode(node);
	if (mode_needs_gp_reg(mode)) {
		cons_loadop   *cons;
		unsigned const size = get_mode_size_bits(mode);
		if (size == 8) {
			cons = mode_is_signed(mode) ? &new_bd_mips_lb : &new_bd_mips_lbu;
		} else if (size == 16) {
			cons = mode_is_signed(mode) ? &new_bd_mips_lh : &new_bd_mips_lhu;
		} else if (size == 32) {
			cons = new_bd_mips_lw;
		} else {
			panic("invalid load");
		}
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const mem   = be_transform_node(get_Load_mem(node));
		mips_addr const addr  = match_address(get_Load_ptr(node));
		return cons(dbgi, block, mem, addr.base, addr.ent, addr.val);
	}
	panic("TODO");
}

static ir_node *gen_Minus(ir_node *const node)
{
	ir_node *const val  = get_Minus_op(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_graph *const irg   = get_irn_irg(node);
		ir_node  *const new_l = get_Start_zero(irg);
		ir_node  *const new_r = be_transform_node(val);
		return new_bd_mips_subu(dbgi, block, new_l, new_r);
	}
	panic("TODO");
}

static ir_node *gen_Mul(ir_node *const node)
{
	ir_node *const l    = get_Mul_left(node);
	ir_node *const r    = get_Mul_right(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const new_l = be_transform_node(l);
		ir_node  *const new_r = be_transform_node(r);
		return new_bd_mips_mul(dbgi, block, new_l, new_r);
	}
	panic("TODO");
}

static ir_node *gen_Or(ir_node *const node)
{
	return gen_logic_op(node, &new_bd_mips_or, &new_bd_mips_ori);
}

static ir_node *gen_Phi(ir_node *const node)
{
	arch_register_req_t       const *req;
	ir_mode                   *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		req = &mips_class_reg_req_gp;
	} else if (mode == mode_M) {
		req = arch_memory_req;
	} else {
		panic("unhandled mode");
	}
	return be_transform_phi(node, req);
}

static ir_node *gen_Proj_Call(ir_node *const node)
{
	ir_node *const call     = get_Proj_pred(node);
	ir_node *const new_call = be_transform_node(call);
	assert(is_mips_jal(new_call));
	switch ((pn_Call)get_Proj_num(node)) {
	case pn_Call_M: return be_new_Proj(new_call, pn_mips_jal_mem);
	case pn_Call_T_result:
	case pn_Call_X_regular:
	case pn_Call_X_except:
		panic("TODO");
	}
	panic("unexpected Proj");
}

static ir_node *gen_Proj_Proj_Call(ir_node *const node)
{
	ir_node *const pred = get_Proj_pred(node);
	assert(get_Proj_num(pred) == pn_Call_T_result);

	ir_node *const call     = get_Proj_pred(pred);
	ir_node *const new_call = be_transform_node(call);

	ir_mode *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		unsigned const num = get_Proj_num(node);
		if (num >= ARRAY_SIZE(result_regs_gp))
			panic("too many gp results");

		arch_register_req_t const *const req = mips_registers[result_regs_gp[num]].single_req;
		be_foreach_out(new_call, i) {
			arch_register_req_t const *const out_req = arch_get_irn_register_req_out(new_call, i);
			if (out_req == req)
				return be_new_Proj(new_call, i);
		}
	}
	panic("TODO");
}

static ir_node *gen_Proj_Load(ir_node *const node)
{
	ir_node *const pred = get_Proj_pred(node);
	ir_node *const load = be_transform_node(pred);

	unsigned const pn = get_Proj_num(node);
	switch ((pn_Load)pn) {
	case pn_Load_M:   return be_new_Proj(load, pn_mips_lw_M);
	case pn_Load_res: return be_new_Proj(load, pn_mips_lw_res);
	case pn_Load_X_regular:
	case pn_Load_X_except:
		break;
	}
	panic("TODO");
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
	if (is_Call(pred_pred)) {
		return gen_Proj_Proj_Call(node);
	} else if (is_Start(pred_pred)) {
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

static ir_node *gen_Proj_Store(ir_node *const node)
{
	ir_node *const pred  = get_Proj_pred(node);
	ir_node *const store = be_transform_node(pred);

	unsigned const pn = get_Proj_num(node);
	switch ((pn_Store)pn) {
	case pn_Store_M: return store;
	case pn_Store_X_regular:
	case pn_Store_X_except:
		break;
	}
	panic("TODO");
}

static ir_node *gen_Proj_default(ir_node *node)
{
	ir_node *const pred     = get_Proj_pred(node);
	ir_node *const new_pred = be_transform_node(pred);
	unsigned const pn       = get_Proj_num(node);
	return be_new_Proj(new_pred, pn);
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
		if (mode_needs_gp_reg(res_mode)) {
			for (size_t i = 0; i != n_res; ++i) {
				ir_node *const res = get_Return_res(node, i);
				in[p]   = be_transform_node(res);
				reqs[p] = mips_registers[result_regs_gp[i]].single_req;
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
		if (mode_needs_gp_reg(param_mode)) {
			if (n_gp == ARRAY_SIZE(param_regs_gp))
				panic("memory parameters not supported yet");
			outs[param_regs_gp[n_gp++]] = BE_START_REG;
		} else {
			panic("unsupported param mode");
		}
	}

	return be_new_Start(irg, outs);
}

typedef ir_node *cons_storeop(dbg_info*, ir_node*, ir_node*, ir_node*, ir_node*, ir_entity*, int32_t);

static ir_node *gen_Store(ir_node *const node)
{
	ir_node       *old_val = get_Store_value(node);
	ir_mode *const mode    = get_irn_mode(old_val);
	if (mode_needs_gp_reg(mode)) {
		cons_storeop  *cons;
		unsigned const size = get_mode_size_bits(mode);
		if (size == 8) {
			cons = &new_bd_mips_sb;
		} else if (size == 16) {
			cons = &new_bd_mips_sh;
		} else if (size == 32) {
			cons = &new_bd_mips_sw;
		} else {
			panic("invalid store");
		}
		if (is_Conv(old_val)) {
			ir_node *const src_val  = get_Conv_op(old_val);
			ir_mode *const src_mode = get_irn_mode(src_val);
			if (mode_needs_gp_reg(src_mode) && get_mode_size_bits(src_mode) >= size)
				old_val = src_val;
		}
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const mem   = be_transform_node(get_Store_mem(node));
		ir_node  *const val   = be_transform_node(old_val);
		mips_addr const addr  = match_address(get_Store_ptr(node));
		return cons(dbgi, block, mem, addr.base, val, addr.ent, addr.val);
	}
	panic("TODO");
}

static ir_node *gen_Sub(ir_node *const node)
{
	ir_node *const l    = get_Sub_left(node);
	ir_node *const r    = get_Sub_right(node);
	ir_mode *const mode = get_irn_mode(node);
	if (mode_needs_gp_reg(mode)) {
		dbg_info *const dbgi  = get_irn_dbg_info(node);
		ir_node  *const block = be_transform_nodes_block(node);
		ir_node  *const new_l = be_transform_node(l);
		ir_node  *const new_r = be_transform_node(r);
		return new_bd_mips_subu(dbgi, block, new_l, new_r);
	}
	panic("TODO");
}

static void mips_register_transformers(void)
{
	be_start_transform_setup();

	be_set_transform_function(op_Add,     gen_Add);
	be_set_transform_function(op_Address, gen_Address);
	be_set_transform_function(op_And,     gen_And);
	be_set_transform_function(op_Call,    gen_Call);
	be_set_transform_function(op_Eor,     gen_Eor);
	be_set_transform_function(op_Cond,    gen_Cond);
	be_set_transform_function(op_Conv,    gen_Conv);
	be_set_transform_function(op_Const,   gen_Const);
	be_set_transform_function(op_Jmp,     gen_Jmp);
	be_set_transform_function(op_Load,    gen_Load);
	be_set_transform_function(op_Minus,   gen_Minus);
	be_set_transform_function(op_Mul,     gen_Mul);
	be_set_transform_function(op_Or,      gen_Or);
	be_set_transform_function(op_Phi,     gen_Phi);
	be_set_transform_function(op_Return,  gen_Return);
	be_set_transform_function(op_Start,   gen_Start);
	be_set_transform_function(op_Store,   gen_Store);
	be_set_transform_function(op_Sub,     gen_Sub);

	be_set_transform_proj_function(op_Call,  gen_Proj_Call);
	be_set_transform_proj_function(op_Cond,  gen_Proj_default);
	be_set_transform_proj_function(op_Load,  gen_Proj_Load);
	be_set_transform_proj_function(op_Proj,  gen_Proj_Proj);
	be_set_transform_proj_function(op_Start, gen_Proj_Start);
	be_set_transform_proj_function(op_Store, gen_Proj_Store);
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
