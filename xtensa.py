#
# IDAPython Xtensa processor module
# https://github.com/themadinventor/ida-xtensa
#
# Copyright (C) 2014 Fredrik Ahlberg
#
# This program is free software; you can redistribute it and/or modify it under
# the terms of the GNU General Public License as published by the Free Software
# Foundation; either version 2 of the License, or (at your option) any later version.
# 
# This program is distributed in the hope that it will be useful, but WITHOUT 
# ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
# FOR A PARTICULAR PURPOSE. See the GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License along with
# this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
# Street, Fifth Floor, Boston, MA 02110-1301 USA.

#  v0.1 - changes by tinhead
#  bug fix for 'l8ui','l16si','l16ui','l32i','s8i','s16i' and 's32i' size and shift
#  bug fix for 'rsr.epc2','rsr.epc3' detection
#  'ill' added, normally one can work without
#  'rsr.epc4','rsr.epc5','rsr.epc6','rsr.epc7' added
#
#  v0.2 - changes by tinhead
#  bug fix for 'addmi' size
#  bug fix for 'movi' size
#  bug fix for 'l32r' with offset >= 0
#  note: movi.n and addi with values higher than 127 looks bit wired in compare to
#        xt-objdump, better would be something like 'ret.value = 0x80 - ret.value'

import string
from idaapi import *

# If set to 1, use "sp" register name for "a1"
SPECIAL_NAMES = 1

HELP = """
Xtensa CALL0 calling convention (Xtensa ISA RefMan sec. 8.1.2):
a0    - return address for calls
a1    - stack pointer
a2-a7 - function arguments (up to 6, rest on stack)
a2-a5 - function return value (up to 4 words, usually just a2)
a12-a15 callee-saved registers (also a0-a1, the rest are caller-saved)
a15   - frame pointer (optional)
"""

class Operand:
	REG	= 0
	IMM	= 1
	MEM	= 2
	RELA	= 3
	RELAL	= 4
	RELU	= 5
	MEM_INDEX = 6

	def __init__(self, type, size, rshift, size2 = 0, rshift2 = 0, signext = False, vshift = 0, off = 0, xlate = None, dt = dt_byte, regbase = None):
		self.type = type
		self.size = size
		self.rshift = rshift
		self.size2 = size2
		self.rshift2 = rshift2
		self.signext = signext or (self.type in (Operand.RELA, Operand.RELAL, Operand.MEM))
		self.vshift = vshift
		self.off = off
		self.xlate = xlate
		self.dt = dt
		self.regbase = regbase


	def bitfield(self, op, size, rshift):
		val = (op >> rshift) & (0xffffffff >> (32 - size))
		return val

	def parse(self, ret, op, cmd = None):
		val = self.bitfield(op, self.size, self.rshift)
		if self.size2:
			val |= ((op >> self.rshift2) & (0xffffffff >> (32-self.size2))) << self.size

		if self.signext and (val & (1 << (self.size+self.size2-1))):
			val = -((~val)&((1 << (self.size+self.size2-1))-1))-1

		val <<= self.vshift
		val += self.off

		if self.xlate:
			val = self.xlate(val)

		ret.dtyp = self.dt
		if self.type == Operand.REG:
			ret.type = o_reg
			ret.reg = val if val < 16 else 16
		elif self.type == Operand.IMM:
			ret.type = o_imm
			ret.value = val
		elif self.type == Operand.MEM:
			ret.type = o_mem
			ret.addr = (cmd.ea+3+(val<<2))&0xfffffffc if val < 0 else (((cmd.ea+3+(val<<2))-0x40000)&0xfffffffc)
		elif self.type == Operand.MEM_INDEX:
			ret.type = o_displ
			ret.phrase = self.bitfield(op, *self.regbase)
			ret.addr = val
		elif self.type in (Operand.RELA, Operand.RELAL):
			ret.type = o_near
			if val == 0:
			    # Not relocated addr in .o
			    ret.addr = cmd.ea
			else:
			    ret.addr = val + cmd.ea + 4 if self.type == Operand.RELA else ((cmd.ea&0xfffffffc)+4+(val<<2))
		elif self.type == Operand.RELU:
			ret.type = o_near
			ret.addr = val + cmd.ea + 4
		else:
			raise ValueError("unhandled operand type");

# These magic lookup tables are defined in table 3-17 and 3-18 (p.41-42) in
# Xtensa Instruction Set Architecture Reference Manual
def b4const(val):
	lut = (-1, 1, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
	return lut[val]

def b4constu(val):
	lut = (32768, 65536, 2, 3, 4, 5, 6, 7, 8, 10, 12, 16, 32, 64, 128, 256)
	return lut[val]

def movi_n(val):
	return val if val & 0x60 != 0x60 else -(0x20 - val & 0x1f)

def addin(val):
	return val if val else -1

def shimm(val):
	return 32-val

def specreg2sym(val):
	return {
	3: "SAR",
	5: "LITBASE",
	104: "DDR",
	177: "EPC1",
	178: "EPC2",
	179: "EPC3",
	192: "DEPC",
	209: "EXCSAVE1",
	226: "INTERRUPT",
	227: "INTCLEAR",
	228: "INTENABLE",
	230: "PS",
	231: "VECBASE",
	232: "EXCCAUSE",
	234: "CCOUNT",
	235: "PRID",
	238: "EXCVADDR",
	}.get(val, val)


class Instr(object):

	fmt_NONE	= (3, ())
	fmt_NNONE	= (2, ())
	fmt_RRR		= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4)))
	fmt_RRR_extui	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 16), Operand(Operand.IMM, 4, 20, off=1)))
	fmt_RRR_1imm	= (3, (Operand(Operand.IMM, 4, 8),))
	fmt_RRR_2imm	= (3, (Operand(Operand.IMM, 4, 8), Operand(Operand.IMM, 4, 4)))
	fmt_RRR_immr	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8)))
	fmt_RRR_2r	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8)))
	fmt_RRR_2rr	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4)))
	fmt_RRR_sll	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8)))
	fmt_RRR_slli	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 20, xlate=shimm)))
	fmt_RRR_srai	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8, 1, 20)))
	fmt_RRR_sh	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 4, 8)))
	fmt_RRR_ssa	= (3, (Operand(Operand.REG, 4, 8),))
	fmt_RRR_ssai	= (3, (Operand(Operand.IMM, 4, 8, 1, 4),))
	fmt_RRI8	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True)))
	fmt_RRI8_addmi	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 8, 16, signext = True, vshift=8, dt=dt_dword)))
	fmt_RRI8_i12	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.IMM, 8, 16, 4, 8, dt=dt_word)))
	fmt_RRI8_disp	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=0, regbase=(4, 8))))
	fmt_RRI8_disp16	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=1, dt=dt_word, regbase=(4, 8))))
	fmt_RRI8_disp32	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 8, 16, vshift=2, dt=dt_dword, regbase=(4, 8))))
	fmt_RRI8_b	= (3, (Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4), Operand(Operand.RELA, 8, 16)))
	fmt_RRI8_bb	= (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, 1, 12), Operand(Operand.RELA, 8, 16)))
	fmt_RI16	= (3, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM, 16, 8, dt=dt_dword)))
	fmt_BRI8	= (3, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 8, 16)))
	fmt_BRI8_imm	= (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4const), Operand(Operand.RELA, 8, 16)))
	fmt_BRI8_immu	= (3, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, xlate = b4constu), Operand(Operand.RELA, 8, 16)))
	fmt_BRI12	= (3, (Operand(Operand.REG, 4, 8), Operand(Operand.RELA, 12, 12)))
	fmt_CALL	= (3, (Operand(Operand.RELA, 18, 6),))
	fmt_CALL_sh	= (3, (Operand(Operand.RELAL, 18, 6),))
	fmt_CALLX	= (3, (Operand(Operand.REG, 4, 8),))
	fmt_RSR		= (3, (Operand(Operand.IMM, 8, 8, xlate=specreg2sym), Operand(Operand.REG, 4, 4)))
	fmt_RSR_spec	= (3, (Operand(Operand.REG, 4, 4),))
	fmt_RRRN	= (2, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.REG, 4, 4)))
	fmt_RRRN_addi	= (2, (Operand(Operand.REG, 4, 12), Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 4, xlate=addin)))
	fmt_RRRN_2r	= (2, (Operand(Operand.REG, 4, 4), Operand(Operand.REG, 4, 8)))
	fmt_RRRN_disp	= (2, (Operand(Operand.REG, 4, 4), Operand(Operand.MEM_INDEX, 4, 12, vshift=2, regbase=(4, 8))))
	fmt_RI6		= (2, (Operand(Operand.REG, 4, 8), Operand(Operand.RELU, 4, 12, 2, 4)))
	fmt_RI7		= (2, (Operand(Operand.REG, 4, 8), Operand(Operand.IMM, 4, 12, 3, 4, xlate=movi_n)))

	def __init__(self, name, opcode, mask, fmt, flags = 0):
		self.name = name
		self.opcode = opcode
		self.mask = mask
		(self.size, self.fmt) = fmt
		self.flags = flags
		
	def match(self, op):
		return (op & self.mask) == self.opcode

	def parseOperands(self, operands, op, cmd = None):
		for ret, fmt in zip(operands, self.fmt):
			fmt.parse(ret, op, cmd)

	def __str__(self):
		return "<Instr %s %x/%x>" % (self.name, self.opcode, self.mask)

class XtensaProcessor(processor_t):
	id = 0x8000 + 1990
	flag = PR_SEGS | PR_DEFSEG32 | PR_RNAMESOK | PR_ADJSEGS | PRN_HEX | PR_USE32
	cnbits = 8
	dnbits = 8
	psnames = ["xtensa"]
	plnames = ["Tensilica Xtensa"]
	segreg_size = 0
	tbyte_size = 0
	help_text = HELP

	instruc_start = 0

	assembler = {
		"flag": ASH_HEXF3 | ASD_DECF0 | ASO_OCTF1 | ASB_BINF3 | AS_NOTAB
			| AS_ASCIIC | AS_ASCIIZ,
		"uflag": 0,
		"name": "GNU assembler",
		"origin": ".org",
		"end": "end",
		"cmnt": ";",
		"ascsep": '"',
		"accsep": "'",
		"esccodes": "\"'",
		"a_ascii": ".ascii",
		"a_byte": ".byte",
		"a_word": ".short",
		"a_dword": ".int",
		"a_bss": "dfs %s",
		"a_seg": "seg",
		"a_curip": ".",
		"a_public": "",
		"a_weak": "",
		"a_extrn": ".extrn",
		"a_comdef": "",
		"a_align": ".align",
		"lbrace": "(",
		"rbrace": ")",
		"a_mod": "%",
		"a_band": "&",
		"a_bor": "|",
		"a_xor": "^",
		"a_bnot": "~",
		"a_shl": "<<",
		"a_shr": ">>",
		"a_sizeof_fmt": "size %s",
	}

	ops = (
		("abs",    0x600100, 0xff0f0f, Instr.fmt_RRR_2rr ),
		("add",	   0x800000, 0xff000f, Instr.fmt_RRR ),
		("addi",   0x00c002, 0x00f00f, Instr.fmt_RRI8 ),
		("addmi",  0x00d002, 0x00f00f, Instr.fmt_RRI8_addmi ),
		("addx2",  0x900000, 0xff000f, Instr.fmt_RRR ),
		("addx4",  0xa00000, 0xff000f, Instr.fmt_RRR ),
		("addx8",  0xb00000, 0xff000f, Instr.fmt_RRR ),
		("and",    0x100000, 0xff000f, Instr.fmt_RRR ),
		("ball",   0x004007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bany",   0x008007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bbc",    0x005007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bbs",    0x00d007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bbci",   0x006007, 0x00e00f, Instr.fmt_RRI8_bb ),
		("bbsi",   0x00e007, 0x00e00f, Instr.fmt_RRI8_bb ),
		("beq",    0x001007, 0x00f00f, Instr.fmt_RRI8_b ),
		("beqi",   0x000026, 0x0000ff, Instr.fmt_BRI8_imm ), # was RRI8
		("beqz",   0x000016, 0x0000ff, Instr.fmt_BRI12 ),
		("bge",    0x00a007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bgei",   0x0000e6, 0x0000ff, Instr.fmt_BRI8_imm ),
		("bgeu",   0x00b007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bgeui",  0x0000f6, 0x0000ff, Instr.fmt_BRI8_immu ),
		("bgez",   0x0000d6, 0x0000ff, Instr.fmt_BRI12 ),
		("blt",    0x002007, 0x00f00f, Instr.fmt_RRI8_b ),
		("blti",   0x0000a6, 0x0000ff, Instr.fmt_BRI8_imm ),
		("bltu",   0x003007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bltui",  0x0000b6, 0x0000ff, Instr.fmt_BRI8_immu ),
		("bltz",   0x000096, 0x0000ff, Instr.fmt_BRI12 ),
		("bnall",  0x00c007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bnone",  0x000007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bne",    0x009007, 0x00f00f, Instr.fmt_RRI8_b ),
		("bnei",   0x000066, 0x0000ff, Instr.fmt_BRI8_imm ),
		("bnez",   0x000056, 0x0000ff, Instr.fmt_BRI12 ),
		("break",  0x004000, 0xfff00f, Instr.fmt_RRR_2imm ),
		("call0",  0x000005, 0x00003f, Instr.fmt_CALL_sh, CF_CALL ),
		("callx0", 0x0000c0, 0xfff0ff, Instr.fmt_CALLX, CF_CALL | CF_JUMP ),
		("dsync",  0x002030, 0xffffff, Instr.fmt_NONE ),
		("esync",  0x002020, 0xffffff, Instr.fmt_NONE ),
		("extui",  0x040000, 0x0e000f, Instr.fmt_RRR_extui ),
		("extw",   0x0020d0, 0xffffff, Instr.fmt_NONE ),
		("isync",  0x002000, 0xffffff, Instr.fmt_NONE ),
#		("ill",	   0x000000, 0xffffff, Instr.fmt_NONE ),	# normally one not need this
		("j",      0x000006, 0x00003f, Instr.fmt_CALL, CF_STOP ),
		("jx",     0x0000a0, 0xfff0ff, Instr.fmt_CALLX, CF_STOP | CF_JUMP ),
		("l8ui",   0x000002, 0x00f00f, Instr.fmt_RRI8_disp ),
		("l16si",  0x009002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
		("l16ui",  0x001002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
		("l32i",   0x002002, 0x00f00f, Instr.fmt_RRI8_disp32 ),
		("l32r",   0x000001, 0x00000f, Instr.fmt_RI16 ),
		("memw",   0x0020c0, 0xffffff, Instr.fmt_NONE ),
		("moveqz", 0x830000, 0xff000f, Instr.fmt_RRR ),
		("movgez", 0xb30000, 0xff000f, Instr.fmt_RRR ),
		("movi",   0x00a002, 0x00f00f, Instr.fmt_RRI8_i12 ),
		("movltz", 0xa30000, 0xff000f, Instr.fmt_RRR ),
		("movnez", 0x930000, 0xff000f, Instr.fmt_RRR ),
		("mul16s", 0xd10000, 0xff000f, Instr.fmt_RRR ),
		("mul16u", 0xc10000, 0xff000f, Instr.fmt_RRR ),
		("mull",   0x820000, 0xff000f, Instr.fmt_RRR ),
		("neg",    0x600000, 0xff0f0f, Instr.fmt_RRR_2rr ),
		("nsa",    0x40e000, 0xfff00f, Instr.fmt_RRR_2r ),
		("nsau",   0x40f000, 0xfff00f, Instr.fmt_RRR_2r ),
		("nop",    0x0020f0, 0xffffff, Instr.fmt_NONE ),
		("or",     0x200000, 0xff000f, Instr.fmt_RRR ),
		("ret",    0x000080, 0xffffff, Instr.fmt_NONE, CF_STOP ),
		("rfe",    0x003000, 0xffffff, Instr.fmt_NONE, CF_STOP ),
		("rfi",    0x003010, 0xfff0ff, Instr.fmt_RRR_1imm, CF_STOP ),
		("rsil",   0x006000, 0xfff00f, Instr.fmt_RRR_immr ),
		("rsr",    0x030000, 0xff000f, Instr.fmt_RSR ),
		("rsync",  0x002010, 0xffffff, Instr.fmt_NONE ),
		("s8i",    0x004002, 0x00f00f, Instr.fmt_RRI8_disp ),
		("s16i",   0x005002, 0x00f00f, Instr.fmt_RRI8_disp16 ),
		("s32i",   0x006002, 0x00f00f, Instr.fmt_RRI8_disp32 ),
		("sll",    0xa10000, 0xff00ff, Instr.fmt_RRR_sll ),
		("slli",   0x010000, 0xef000f, Instr.fmt_RRR_slli ),
		("sra",    0xb10000, 0xff0f0f, Instr.fmt_RRR_2rr ),
		("srai",   0x210000, 0xef000f, Instr.fmt_RRR_srai ),
		("src",    0x810000, 0xff000f, Instr.fmt_RRR ),
		("srl",    0x910000, 0xff0f0f, Instr.fmt_RRR_2rr ),
		("srli",   0x410000, 0xff000f, Instr.fmt_RRR_sh ),
		("ssa8b",  0x403000, 0xfff0ff, Instr.fmt_RRR_ssa ),
		("ssa8l",  0x402000, 0xfff0ff, Instr.fmt_RRR_ssa ),
		("ssai",   0x404000, 0xfff0ef, Instr.fmt_RRR_ssai ),
		("ssl",    0x401000, 0xfff0ff, Instr.fmt_RRR_ssa ),
		("ssr",    0x400000, 0xfff0ff, Instr.fmt_RRR_ssa ),
		("sub",    0xc00000, 0xff000f, Instr.fmt_RRR ),
		("subx2",  0xd00000, 0xff000f, Instr.fmt_RRR ),
		("subx4",  0xe00000, 0xff000f, Instr.fmt_RRR ),
		("subx8",  0xf00000, 0xff000f, Instr.fmt_RRR ),
		("waiti",  0x007000, 0xfff0ff, Instr.fmt_RRR_1imm ),
		("wdtlb",  0x50e000, 0xfff00f, Instr.fmt_RRR_2r ),
		("witlb",  0x506000, 0xfff00f, Instr.fmt_RRR_2r ),
		("wsr",    0x130000, 0xff000f, Instr.fmt_RSR ),
		("xor",    0x300000, 0xff000f, Instr.fmt_RRR ),
		("xsr",    0x610000, 0xff000f, Instr.fmt_RSR ),
		("movi*",   0x000001, 0x000000, Instr.fmt_NONE ),

		("add.n",   0x000a, 0x000f, Instr.fmt_RRRN ),
		("addi.n",  0x000b, 0x000f, Instr.fmt_RRRN_addi ),
		("beqz.n",  0x008c, 0x00cf, Instr.fmt_RI6 ),
		("bnez.n",  0x00cc, 0x00cf, Instr.fmt_RI6 ),
		("mov.n",   0x000d, 0xf00f, Instr.fmt_RRRN_2r ),
		("break.n", 0xf02d, 0xf0ff, Instr.fmt_RRRN ),
		("ret.n",   0xf00d, 0xffff, Instr.fmt_NNONE, CF_STOP ),
		("l32i.n",  0x0008, 0x000f, Instr.fmt_RRRN_disp ),
		("movi.n",  0x000c, 0x008f, Instr.fmt_RI7 ),
		("nop.n",   0xf03d, 0xffff, Instr.fmt_NNONE ),
		("s32i.n",  0x0009, 0x000f, Instr.fmt_RRRN_disp ),
	)

	def __init__(self):
		processor_t.__init__(self)
		self._init_instructions()
		self._init_registers()
	
	def _add_instruction(self, instr):
		self.instrs_list.append(instr)
	
	def _init_instructions(self):
		self.instrs_list = []
		self.short_insts = []
		self.long_insts = []

		for o in self.ops:
			instr = Instr(*o)
			self._add_instruction(instr)
			if instr.size == 2:
				self.short_insts.append(instr)
			else:
				self.long_insts.append(instr)

		self.instruc = [{ "name": i.name, "feature": i.flags } for i in self.instrs_list]
		self.instruc_end = len(self.instruc)

		self.instrs = {}
		for instr in self.instrs_list:
			self.instrs[instr.name] = instr
		
		self.instrs_ids = {}
		for i, instr in enumerate(self.instrs_list):
			self.instrs_ids[instr.name] = i
			instr.id = i

	def _init_registers(self):
		self.regNames = ["a%d" % d for d in range(16)]
		if SPECIAL_NAMES > 0:
			self.regNames[1] = "sp"
		self.regNames += ["pc", "sar", "CS", "DS"]
		self.reg_ids = {}
		for i, reg in enumerate(self.regNames):
			self.reg_ids[reg] = i

		self.regFirstSreg = self.regCodeSreg = self.reg_ids["CS"]
		self.regLastSreg = self.regDataSreg = self.reg_ids["DS"]
	
	def _pull_op_byte(self):
		ea = self.cmd.ea + self.cmd.size
		byte = get_full_byte(ea)
		self.cmd.size += 1
		return byte

	def _find_instr(self):
		op = self._pull_op_byte()
		op |= self._pull_op_byte() << 8
		
		for instr in self.short_insts:
			if instr.match(op):
				return instr, op

		op |= self._pull_op_byte() << 16

		for instr in self.long_insts:
			if instr.match(op):
				return instr, op

		return None, op

	def ana(self):
		instr, op = self._find_instr()
		if not instr:
			return 0
		
		self.cmd.itype = instr.id

		operands = [self.cmd[i] for i in range(6)]
		for o in operands:
			o.type = o_void
		instr.parseOperands(operands, op, self.cmd)

		if instr.name == "l32r":
			self.cmd.itype = self.instrs_ids["movi*"]
			ea = self.cmd[1].addr
			#val = (get_full_byte(ea + 3) << 24) | (get_full_byte(ea + 2) << 16) | (get_full_byte(ea + 1) << 8) | get_full_byte(ea)
			# get_full_val() is ScratchABit extension to support
			# disassembling .o files.
			val = get_full_val(ea, 4)
			self.cmd[2].type = o_imm
			self.cmd[2].value = val
			self.cmd[1].flags &= ~OF_SHOW
			# If data referenced by l32r was an offset,
			# make movi*'s argument offset too
# Don't do this in ana(), as it may lead to disassembly listing changed just by
# browsing it (because ana() is called to render an instruction). Instead, do this
# below in emu(), which is called once during initial analysis (that means that
# data type won't be automagically propagated to where it's referenced by l32r,
# but listing stability is more important, and doing the above is something for
# plugin anyway).
#			if is_offset(ea, 0):
#				op_offset(self.cmd.ea, 2, REF_OFF32, ref_addr=val)

		return self.cmd.size

	def emu(self):
		if self.cmd[1].type == o_mem and self.cmd[2].type == o_imm:
			# This can be only movi*
			if is_offset(self.cmd[1].addr, 0):
				op_offset(self.cmd.ea, 2, REF_OFF32, ref_addr=self.cmd[2].value)
		for i in range(6):
			op = self.cmd[i]
			if op.type == o_void:
				break
			elif op.type == o_mem:
				ua_dodata2(0, op.addr, op.dtyp)
				ua_add_dref(0, op.addr, dr_R)
			elif op.type == o_near:
				features = self.cmd.get_canon_feature()
				if features & CF_CALL:
					fl = fl_CN
				else:
					fl = fl_JN
				ua_add_cref(0, op.addr, fl)

		feature = self.cmd.get_canon_feature()
		if feature & CF_JUMP:
			QueueMark(Q_jumps, self.cmd.ea)
		if not feature & CF_STOP:
			ua_add_cref(0, self.cmd.ea + self.cmd.size, fl_F)
		return True
	
	def outop(self, op):
		if op.type == o_reg:
			out_register(self.regPrefix + self.regNames[op.reg])
		elif op.type == o_imm:
			instr = self.instrs_list[self.cmd.itype]
			if instr.name in ("extui", "bbci", "bbsi", "slli", "srli", "srai", "ssai"):
				# bit numbers/shifts are always decimal
				OutLong(op.value, 10)
			else:
				OutValue(op, OOFW_IMM)
		elif op.type in (o_near, o_mem):
			ok = out_name_expr(op, op.addr, BADADDR)
			if not ok:
				out_tagon(COLOR_ERROR)
				OutLong(op.addr, 16)
				out_tagoff(COLOR_ERROR)
				QueueMark(Q_noName, self.cmd.ea)
		elif op.type == o_displ:
			out_register(self.regPrefix + self.regNames[op.phrase])
			OutLine(", ")
			OutValue(op, OOF_ADDR)
		else:
			return False
		return True

	def out_asm(self):
		buf = init_output_buffer(1024)
		self.out_asm_cont(buf)

	def out_asm_cont(self, buf):
		OutMnem()

		instr = self.instrs_list[self.cmd.itype]

		for i in range(6):
			if self.cmd[i].type == o_void:
				break

			if self.cmd[i].flags & OF_SHOW == 0:
				continue
			if i > 0:
				out_symbol(',')
			OutChar(' ')
			out_one_operand(i)

		if instr.name == "movi*":
			OutLine(" ; via 0x%x" % self.cmd[1].addr)

		term_output_buffer()
		cvar.gl_comm = 1
		MakeLine(buf)

	def pseudoc_dest(self, oper=0):
		out_one_operand(oper)
		OutLine(" = ")

	def pseudoc_goto(self, addr_op):
		OutLine("goto ")
		out_one_operand(addr_op)

	def pseudoc_call(self, addr_op):
		OutLine("call ")
		out_one_operand(addr_op)

	def pseudoc_memref(self, type):
		OutLine("*(%s*)" % type)
		op = self.cmd[1]
		assert op.type == o_displ
		if op.addr == 0:
			out_register(self.regPrefix + self.regNames[op.phrase])
		else:
			OutLine("(")
			out_register(self.regPrefix + self.regNames[op.phrase])
			OutLine(" + ")
			OutLong(op.addr, 16)
			OutLine(")")

	def out_pseudoc(self):
		buf = init_output_buffer(1024)
		instr = self.instrs_list[self.cmd.itype]
		mnem = instr.name.replace(".n", "")
		op_xlat = {
			"add": "+", "addi": "+", "addmi": "+", "sub": "-",
			"and": "&", "or": "|", "xor": "^",
			"slli": "<<", "srli": ">>"
		}
		if mnem.startswith("mov"):
			if mnem in ("moveqz", "movnez"):
				OutLine("if (")
				out_one_operand(2)
				if mnem == "moveqz":
					OutLine(" == ")
				else:
					OutLine(" != ")
				OutLine("0) ")
			self.pseudoc_dest()
			if mnem == "movi*":
				out_one_operand(2)
			else:
				out_one_operand(1)
		elif mnem in ("j", "jx"):
			self.pseudoc_goto(0)
		elif mnem.startswith("call"):
			self.pseudoc_call(0)
		elif mnem.startswith("ret"):
			OutLine("return")
		elif mnem == "extui":
			self.pseudoc_dest()
			OutLine("bitfield(")
			out_one_operand(1)
			OutLine(", /*lsb*/")
			out_one_operand(2)
			OutLine(", /*sz*/")
			out_one_operand(3)
			OutLine(")")
		elif mnem[0] in ("s", "l") and mnem[1] in string.digits:
			assert mnem[-1] == "i"
			mnem = mnem[:-1]
			if mnem[-1] == "s":
				type = "i"
			else:
				type = "u"
			if mnem[-1] not in string.digits:
				mnem = mnem[:-1]
			type += mnem[1:]
			if mnem[0] == "s":
				self.pseudoc_memref(type)
			else:
				out_one_operand(0)
			OutLine(" = ")
			if mnem[0] == "s":
				out_one_operand(0)
			else:
				self.pseudoc_memref(type)
		elif mnem == "neg":
			self.pseudoc_dest()
			OutLine("-")
			out_one_operand(1)
		elif mnem == "nsau":
			self.pseudoc_dest()
			OutLine("count_leading_zeroes(")
			out_one_operand(1)
			OutLine(")")
		elif mnem == "abs":
			self.pseudoc_dest()
			OutLine("abs(")
			out_one_operand(1)
			OutLine(")")
		elif mnem == "ssai":
			OutLine("$SAR = ")
			out_one_operand(0)
		elif mnem == "ssr":
			OutLine("$SAR = ")
			out_one_operand(0)
			OutLine(" & 0x1f")
		elif mnem == "ssl":
			OutLine("$SAR = 32 - (")
			out_one_operand(0)
			OutLine(" & 0x1f)")
		elif mnem == "sll":
			if self.cmd[0].reg == self.cmd[1].reg:
				out_one_operand(0)
				OutLine(" <<= 32 - $SAR")
			else:
				self.pseudoc_dest()
				out_one_operand(1)
				OutLine(" << (32 - $SAR)")
		elif mnem == "srl":
			if self.cmd[0].reg == self.cmd[1].reg:
				out_one_operand(0)
				OutLine(" >>= $SAR")
			else:
				self.pseudoc_dest()
				out_one_operand(1)
				OutLine(" >> $SAR")
		elif mnem == "sra":
			self.pseudoc_dest()
			OutLine("(i32)")
			out_one_operand(1)
			OutLine(" >> $SAR")
		elif mnem == "srai":
			self.pseudoc_dest()
			OutLine("(i32)")
			out_one_operand(1)
			OutLine(" >> ")
			out_one_operand(2)
		elif mnem == "src":
			self.pseudoc_dest()
			OutLine("UINT64(")
			out_one_operand(1)
			OutLine(", ")
			out_one_operand(2)
			OutLine(") >> $SAR")
		elif mnem in op_xlat:
			out_one_operand(0)
			ch_sign = False

			# If we add negative immediate value, sub instead
			if mnem.startswith("add") and self.cmd[2].type == o_imm and self.cmd[2].value < 0:
				mnem = "sub"
				self.cmd[2].value = -self.cmd[2].value
				ch_sign = True

			if mnem == "or" and self.cmd[1].type == self.cmd[2].type and self.cmd[1].reg == self.cmd[2].reg:
				# "mov" alias
				OutLine(" = ")
				out_one_operand(1)
			elif self.cmd[0].reg == self.cmd[1].reg:
				OutLine(" %s= " % op_xlat[mnem])
				out_one_operand(2)
			elif mnem == "add" and self.cmd[0].reg == self.cmd[2].reg:
				OutLine(" %s= " % op_xlat[mnem])
				out_one_operand(1)
			else:
				OutLine(" = ")
				out_one_operand(1)
				OutLine(" %s " % op_xlat[mnem])
				out_one_operand(2)
			if ch_sign:
				self.cmd[2].value = -self.cmd[2].value
		elif mnem in ("addx2", "addx4", "addx8"):
			out_one_operand(0)
			mult = int(mnem[-1])
			if self.cmd[0].reg == self.cmd[2].reg:
				if self.cmd[0].reg == self.cmd[1].reg:
					OutLine(" *= %d" % (mult + 1))
				else:
					OutLine(" += ")
					out_one_operand(1)
					OutLine(" * %d" % mult)
			else:
				OutLine(" = ")
				if self.cmd[1].reg == self.cmd[2].reg:
					out_one_operand(1)
					OutLine(" * %d" % (mult + 1))
				else:
					out_one_operand(1)
					OutLine(" * %d + " % mult)
					out_one_operand(2)
		elif mnem in ("subx2", "subx4", "subx8"):
			out_one_operand(0)
			mult = int(mnem[-1])
			if self.cmd[1].reg == self.cmd[2].reg:
				if self.cmd[0].reg == self.cmd[1].reg:
					OutLine(" *= %d" % (mult - 1))
				else:
					OutLine(" = ")
					out_one_operand(1)
					OutLine(" * %d" % (mult - 1))
			else:
				OutLine(" = ")
				out_one_operand(1)
				OutLine(" * %d - " % mult)
				out_one_operand(2)
		elif mnem == "mull":
			if self.cmd[0].reg == self.cmd[1].reg:
				out_one_operand(0)
				OutLine(" *= ")
				out_one_operand(2)
			else:
				self.pseudoc_dest()
				#OutLine("(u32)(")
				out_one_operand(1)
				OutLine(" * ")
				out_one_operand(2)
				#OutLine(")")
		elif mnem == "mul16u":
			self.pseudoc_dest()
			OutLine("(u16)")
			out_one_operand(1)
			OutLine(" * ")
			OutLine("(u16)")
			out_one_operand(2)
		elif mnem == "mul16s":
			self.pseudoc_dest()
			OutLine("(i16)")
			out_one_operand(1)
			OutLine(" * ")
			OutLine("(i16)")
			out_one_operand(2)
		elif mnem == "ssa8b":
			OutLine(self.regPrefix + "SAR = 32 - (")
			out_one_operand(0)
			OutLine(" & 3) * 8")
		elif mnem == "ssa8l":
			OutLine(self.regPrefix + "SAR = (")
			out_one_operand(0)
			OutLine(" & 3) * 8")

		elif mnem.startswith("rsr"):
			self.pseudoc_dest(1)
			OutLine(mnem)
			OutLine("(")
			out_one_operand(0)
			OutLine(")")
		elif mnem.startswith("wsr") or mnem.startswith("xsr"):
			OutLine(mnem)
			OutLine("(")
			out_one_operand(0)
			OutLine(", ")
			out_one_operand(1)
			OutLine(")")
		elif mnem == "waiti":
			# Special func with no dest and 1 arg
			OutLine(mnem)
			OutLine("(")
			out_one_operand(0)
			OutLine(")")
		elif mnem == "rsil":
			self.pseudoc_dest()
			OutLine(mnem)
			OutLine("(")
			out_one_operand(1)
			OutLine(")")
		elif mnem == "rfi":
			OutLine("return /*intlevel=")
			out_one_operand(0)
			OutLine("*/")
		elif mnem == "rfe":
			OutLine("return /*exc*/")
		elif mnem in ("wdtlb", "witlb", "break"):
			OutLine(mnem)
			OutLine("(")
			out_one_operand(0)
			OutLine(", ")
			out_one_operand(1)
			OutLine(")")
		# Argument-less special functions
		elif mnem in ("memw",):
			OutLine(mnem)
			OutLine("()")
		elif mnem.startswith("nop"):
			OutLine(mnem)
			OutLine("()")
		elif mnem.endswith("sync"):
			OutLine(mnem)
			OutLine("()")
		elif mnem.startswith("b"):
			cond = mnem[1:]
			OutLine("if (")
			if cond[-1] == "z":
				# 2-operand
				if cond == "eqz":
					out_one_operand(0)
					OutLine(" == 0")
				elif cond == "nez":
					out_one_operand(0)
					OutLine(" != 0")
				elif cond == "ltz":
					OutLine("(i32)")
					out_one_operand(0)
					OutLine(" < 0")
				elif cond == "gez":
					OutLine("(i32)")
					out_one_operand(0)
					OutLine(" >= 0")
				OutLine(") ")
				self.pseudoc_goto(1)
			else:
				# 3-operand
				cond_xlat = {"eq": "==", "ne": "!=", "lt": "<", "ge": ">="}
				is_imm = False
				is_signed = True
				if cond[-1] == "i":
					is_imm = True
					cond = cond[:-1]
				if cond[-1] == "u":
					is_signed = False
					cond = cond[:-1]
				if cond in ("eq", "ne"):
					is_signed = False

				if cond == "bc":
					OutLine("(")
					out_one_operand(0)
					OutLine(" & BIT(")
					out_one_operand(1)
					OutLine(")) == 0")
				elif cond == "bs":
					out_one_operand(0)
					OutLine(" & BIT(")
					out_one_operand(1)
					OutLine(")")
				elif cond == "any":
					out_one_operand(0)
					OutLine(" & ")
					out_one_operand(1)
				elif cond == "none":
					OutLine("(")
					out_one_operand(0)
					OutLine(" & ")
					out_one_operand(1)
					OutLine(") == 0")
				elif cond == "all":
					OutLine("(")
					out_one_operand(0)
					OutLine(" & ")
					out_one_operand(1)
					OutLine(") == ")
					out_one_operand(1)
				elif cond == "nall":
					OutLine("(")
					out_one_operand(0)
					OutLine(" & ")
					out_one_operand(1)
					OutLine(") != ")
					out_one_operand(1)
				else:
					if (cond not in cond_xlat):
						OutLine("Unconverted: ")
						return self.out_asm_cont(buf)

					if is_signed:
						OutLine("(i32)")
					out_one_operand(0)
					OutLine(" %s " % cond_xlat[cond])
					if is_signed:
						OutLine("(i32)")
					out_one_operand(1)
				OutLine(") ")
				self.pseudoc_goto(2)
#				return self.out_asm()
		else:
			return self.out_asm()

		OutLine(" ; ")
		return self.out_asm_cont(buf)
		term_output_buffer()
		cvar.gl_comm = 1
		MakeLine(buf)


#	regPrefix = "$"
#	out = out_pseudoc
	regPrefix = ""
	out = out_asm


def PROCESSOR_ENTRY():
	return XtensaProcessor()
