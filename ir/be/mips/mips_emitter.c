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
#include "gen_mips_regalloc_if.h"
#include "mips_nodes_attr.h"
#include "panic.h"
#include "util.h"

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

		case 'D': {
			if (!is_digit(*fmt))
				goto unknown;
			unsigned const pos = *fmt++ - '0';
			reg = arch_get_irn_register_out(node, pos);
			goto emit_R;
		}

		case 'I': {
			mips_immediate_attr_t const *const imm = get_mips_immediate_attr_const(node);
			be_emit_irprintf("%" PRId32, imm->val);
			break;
		}

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

static void mips_register_emitters(void)
{
	be_init_emitters();
	mips_register_spec_emitters();

	be_set_emitter(op_be_Copy, emit_be_Copy);
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
	ir_node  *const end_bl    = get_irg_end_block(irg);
	for (size_t i = 0; i != n_blocks; ++i) {
		ir_node *const block = blk_sched[i];
		if (block != end_bl) // TODO
			mips_gen_block(block);
	}

	be_gas_emit_function_epilog(entity);
}
