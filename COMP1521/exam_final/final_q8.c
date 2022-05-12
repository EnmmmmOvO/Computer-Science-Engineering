// COMP1521 21T2 ... final exam, question 9

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include 'final_q8.h'
#include 'final_q8_opcodes.h'

Instruction
decode_instruction (Word insn_word)
{
	Instruction i = { .op = '[unknown]' };

	/// TODO: complete this function.
	
if (insn_word >> 26 == 0) {
		i.uses_imm = 0;
		i.uses_base = 0;
		i.rd = {r15, r14, r13, r12, r11};
		i.rs = {r25, r24, r23, r22, r21};
		i.rt = {r20, r19, r18, r17, r16};
		if ((insn_word & 0x3f) == 0b100000) {
			i.op[0] = 'a';
			i.op[1] = 'd';
			i.op[2] = 'd';
		} else if ((insn_word & 0x3f) == 0b100001) {
			i.op[0] = 'a';
			i.op[1] = 'd';
			i.op[2] = 'd';
			i.op[3] = 'u';	
		} else if ((insn_word & 0x3f) == 0b100010) {
			i.op[0] = 's';
			i.op[1] = 'u';
			i.op[2] = 'b';	
		} else if ((insn_word & 0x3f) == 0b100011) {
			i.op[0] = 's';
			i.op[1] = 'u';
			i.op[2] = 'b';
			i.op[3] = 'u';	
		}
	} else {
		i.uses_rd = 0;
		if (insn_word >> 26 == 0b001000) {
			i.op[0] = 'a';
			i.op[1] = 'd';
			i.op[2] = 'd';
			i.op[3] = 'i';
			i.uses_base = 0;
			i.uses_rd = 0;
			i.rs = {r25, r24, r23, r22, r21};
			i.rt = {r20, r19, r18, r17, r16};
			i.imm = insn_word & 0xffff;
		} else if (insn_word >> 26 == 0b001001) {
			i.op[0] = 'a';
			i.op[1] = 'd';
			i.op[2] = 'd';
			i.op[3] = 'i';
			i.op[4] = 'u';
			i.uses_base = 0;
			i.uses_rd = 0;
			i.rs = {r25, r24, r23, r22, r21};
			i.rt = {r20, r19, r18, r17, r16};
			i.imm = insn_word & 0xffff;
		} else if (insn_word >> 26 == 0b100000) {
			i.op[0] = 'l';
			i.op[1] = 'b';
			i.uses_rs = 0;
			i.uses_rd = 0;
			i.base = {r25, r24, r23, r22, r21};
			i.rt = {r20, r19, r18, r17, r16};
			i.imm = 0;
		} else if (insn_word >> 26 == 0b100011) {
			i.op[0] = 'l';
			i.op[1] = 'w';
			i.uses_rs = 0;
			i.uses_rd = 0;
			i.base = {r25, r24, r23, r22, r21};
			i.rt = {r20, r19, r18, r17, r16};
			i.imm = 0;
		}
	}
	return i;
}
