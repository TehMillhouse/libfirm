/*
 * This file is part of libFirm.
 * Copyright (C) 2016 University of Karlsruhe.
 */

#include "mips_emitter.h"

#include <inttypes.h>

#include "bearch.h"
#include "beblocksched.h"
#include "beemithlp.h"
#include "beemitter.h"
#include "begnuas.h"
#include "benode.h"
#include "besched.h"
#include "gen_mips_emitter.h"
#include "gen_mips_new_nodes.h"
#include "gen_mips_regalloc_if.h"
#include "mips_nodes_attr.h"
#include "panic.h"
#include "util.h"

static inline ir_node *get_target_block(ir_node const *const node)
{
	return (ir_node*)get_irn_link(node);
}

static void emit_immediate(char const *const prefix, ir_node const *const node)
{
	mips_immediate_attr_t const *const imm = get_mips_immediate_attr_const(node);
	if (imm->ent) {
		if (prefix)
			be_emit_irprintf("%s(", prefix);
		be_gas_emit_entity(imm->ent);
		if (imm->val)
			be_emit_irprintf("%+" PRId32, imm->val);
		if (prefix)
			be_emit_char(')');
	} else {
		be_emit_irprintf("%" PRId32, imm->val);
	}
}

void mips_emitf(ir_node const *const node, char const *fmt, ...)
{
	va_list ap;
	va_start(ap, fmt);

	be_emit_char('\t');
	for (;;) {
		char const *start = fmt;
		while (*fmt != '%' && *fmt != '\n' && *fmt != '\0')
			++fmt;
		if (fmt != start) {
			be_emit_string_len(start, fmt - start);
		}

		if (*fmt == '\n') {
			be_emit_char('\n');
			be_emit_write_line();
			be_emit_char('\t');
			++fmt;
			continue;
		}

		if (*fmt == '\0')
			break;

		++fmt;
		switch (*fmt++) {
			arch_register_t const *reg;

		case '%':
			be_emit_char('%');
			break;

		case 'A': {
			if (!is_digit(*fmt))
				goto unknown;
			unsigned const pos = *fmt++ - '0';
			reg = arch_get_irn_register_in(node, pos);
			emit_immediate("%lo", node);
			be_emit_irprintf("($%s)", reg->name);
			break;
		}

		case 'C': {
			mips_cond_attr_t const *const cond = get_mips_cond_attr_const(node);
			be_emit_string(mips_get_cond_name(cond->cond));
			break;
		}

		case 'D': {
			if (!is_digit(*fmt))
				goto unknown;
			unsigned const pos = *fmt++ - '0';
			reg = arch_get_irn_register_out(node, pos);
			goto emit_R;
		}

		case 'H':
			emit_immediate("%hi", node);
			break;

		case 'I':
			emit_immediate(NULL, node);
			break;

		case 'J': {
			ir_node *const jump  = va_arg(ap, ir_node*);
			ir_node *const label = get_target_block(jump);
			be_gas_emit_block_name(label);
			break;
		}

		case 'L':
			emit_immediate("%lo", node);
			break;

		case 'R':
			reg = va_arg(ap, arch_register_t const*);
emit_R:
			be_emit_char('$');
			be_emit_string(reg->name);
			break;

		case 'S': {
			if (!is_digit(*fmt))
				goto unknown;
			unsigned const pos = *fmt++ - '0';
			reg = arch_get_irn_register_in(node, pos);
			goto emit_R;
		}

		case 'd': {
			int const val = va_arg(ap, int);
			be_emit_irprintf("%d", val);
			break;
		}

		default:
unknown:
			panic("unknown format conversion");
		}
	}

	be_emit_finish_line_gas(node);
	va_end(ap);
}

static void emit_be_Copy(ir_node const *const node)
{
	ir_node               *const op  = be_get_Copy_op(node);
	arch_register_t const *const in  = arch_get_irn_register(op);
	arch_register_t const *const out = arch_get_irn_register(node);
	if (in == out)
		return;

	if (in->cls == &mips_reg_classes[CLASS_mips_gp]) {
		mips_emitf(node, "move\t%R, %R", out, in);
	} else {
		panic("unexpected register class");
	}
}

static void emit_be_IncSP(ir_node const *const node)
{
	int const offs = -be_get_IncSP_offset(node);
	mips_emitf(node, "addiu\t%D0, %S0, %d", offs);
}

static void emit_mips_b(ir_node const *const node)
{
	ir_node *const block = get_nodes_block(node);
	if (get_target_block(block) != get_target_block(node)) {
		mips_emitf(node, "b\t%J", node);
		mips_emitf(NULL, "nop");
	}
}

static void emit_mips_bcc(ir_node const *const node)
{
	ir_node *const t = get_Proj_for_pn(node, pn_mips_bcc_true);
	mips_emitf(node, "b%C\t%S0, %S1, %J", t);
	mips_emitf(NULL, "nop");
	ir_node *const block = get_nodes_block(node);
	ir_node *const f     = get_Proj_for_pn(node, pn_mips_bcc_false);
	if (get_target_block(block) != get_target_block(f)) {
		mips_emitf(node, "b\t%J", f);
		mips_emitf(NULL, "nop");
	}
}

static void mips_register_emitters(void)
{
	be_init_emitters();
	mips_register_spec_emitters();

	be_set_emitter(op_be_Copy,  emit_be_Copy);
	be_set_emitter(op_be_IncSP, emit_be_IncSP);
	be_set_emitter(op_mips_b,   emit_mips_b);
	be_set_emitter(op_mips_bcc, emit_mips_bcc);
}

static void mips_gen_block(ir_node *const block)
{
	be_gas_begin_block(block, true);
	sched_foreach(block, node) {
		be_emit_node(node);
	}
}

void mips_emit_function(ir_graph *const irg)
{
	mips_register_emitters();
	be_gas_elf_type_char = '@';

	ir_entity *const entity = get_irg_entity(irg);
	be_gas_emit_function_prolog(entity, 16, NULL);

	ir_node **const blk_sched = be_create_block_schedule(irg);
	size_t    const n_blocks  = ARR_LEN(blk_sched);

	ir_reserve_resources(irg, IR_RESOURCE_IRN_LINK);

	ir_node *sched_pred = blk_sched[0];
	for (size_t i = 1; i != n_blocks; ++i) {
		ir_node *const block = blk_sched[i];
		foreach_irn_in(block, k, pred) {
			set_irn_link(pred, block);
		}
		set_irn_link(sched_pred, block);
		sched_pred = block;
	}
	ir_node  *const end_bl = get_irg_end_block(irg);
	for (size_t i = 0; i != n_blocks; ++i) {
		ir_node *const block = blk_sched[i];
		if (block != end_bl) // TODO
			mips_gen_block(block);
	}

	ir_free_resources(irg, IR_RESOURCE_IRN_LINK);

	be_gas_emit_function_epilog(entity);
}
