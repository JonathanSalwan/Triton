#!/usr/bin/env python3
## -*- coding: utf-8 -*-

from __future__        import print_function

from triton            import *
from unicorn           import *
from unicorn.riscv_const import *
from struct            import pack

import sys
import pprint

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024

CODE  = [
    # ADDI
    (b"\x93\x05\x16\x00", "addi x11, x12, #1"),
    (b"\x13\x00\xe0\x00", "addi x0,  x0,  #0xe"),
    (b"\x13\x05\x00\x00", "addi x10, x0,  #0"),
    (b"\x13\x00\x00\x00", "addi x0,  x0,  #0"),    # nop
    (b"\x13\x00\x00\x00", "addi x0,  x0,  #0"),    # nop
    (b"\x13\x00\x00\x00", "addi x0,  x0,  #0"),    # nop
    (b"\x93\x05\x16\x00", "addi x11, x12, #1"),
    (b"\x93\x05\x06\x00", "addi x11, x12, #0"),
    (b"\x13\x05\xe0\x00", "addi x10, x0,  #0xe"),
    (b"\x13\x03\x43\x00", "addi x6,  x6,  #4"),
    (b"\x49\x13",       "c.addi x1,  x1,  #1"),
    (b"\x49\x13",       "c.addi x6,  x6,  #-0xe"),
    (b"\x09\x16",       "c.addi x12, x12, #-30"),
    (b"\x11\x01",       "c.addi x2,  x2,  #4"),
    (b"\x75\x61",       "c.addi16sp  x2,  x2,  #368"),
    (b"\x40\x00",       "c.addi4spn  x8,  x2,  #4"),
    (b"\x8c\x02",       "c.addi4spn x10, x2,   #320"),
    (b"\x85\x47",       "c.li  x15, #1"),
    (b"\x49\x4c",       "c.li  x24, #18"),
    (b"\x09\x54",       "c.li  x8, #-30"),
    (b"\x01\x00",       "c.nop"),
    (b"\x5d\x00",       "c.nop 23"),
    (b"\x65\x00",       "c.nop 25"),

    # ADD
    (b"\x33\x05\x00\x00", "add x10, x0,  x0"),
    (b"\x33\x86\xb0\x00", "add x12, x1, x11"),
    (b"\xb3\x05\x06\x00", "add x11, x12, x0"),
    (b"\xb3\x05\xc0\x00", "add x11, x0, x12"),
    (b"\xbe\x95",       "c.add x11, x11, x15"),
    (b"\x0a\x9a",       "c.add x20, x20, x2"),
    (b"\x0a\x88",       "c.mv  x16, x2"),
    (b"\xb2\x8a",       "c.mv  x21, x12"),

    # AND(I)
    (b"\x13\xf0\xf0\x0f", "andi  x0,  x1,  #0xff"),
    (b"\x13\x75\xf0\x0f", "andi  x10, x0,  #0xff"),
    (b"\x93\x76\x17\x00", "andi  x13, x14, #0x01"),
    (b"\x93\x76\x07\x01", "andi  x13, x14, #0x10"),
    (b"\x49\x13",       "c.andi  x14, x14, #2"),
    (b"\x19\x98",       "c.andi  x8,  x8, #-26"),
    (b"\xb3\x71\x52\x00", "and   x3,  x4,  x5"),
    (b"\xb3\x75\xc5\x00", "and   x11, x10, x12"),
    (b"\x71\x8f",       "c.and   x14, x14, x12"),

    # AUIPC
    (b"\x17\xe5\xcd\xab", "auipc x10, #0xabcde"),
    (b"\x17\x15\x00\x00", "auipc x10,  #0x1"),
    (b"\x17\xd9\xf1\xe2", "auipc x18, #0xf1e2d"),
    (b"\x17\x10\x00\x00", "auipc x0,  #0x1"),

    # SB / SH / SW
    (b"\x23\x0c\xa1\x00", "sb x10, 0x18(sp)"),
    (b"\xa3\x0c\xa1\x00", "sb x10, 0x19(sp)"),
    (b"\x23\x00\xc1\x02", "sb x12, 0x20(sp)"),
    (b"\x23\x2a\xe1\x00", "sw x14, 0x14(sp)"),
    (b"\x23\x20\xa1\x02", "sw x10, 0x20(sp)"),
    (b"\x23\x11\xe1\x02", "sh x14, 0x22(sp)"),
    (b"\x23\x10\x01\x00", "sh x0, 0(sp)"),
    (b"\x23\x12\xa1\x02", "sh x10, 0x24(sp)"),
    (b"\x23\x20\xe1\x00", "sw x14, 0(sp)"),

    # LB / LH / LW
    (b"\x03\x25\x01\x00", "lw x10, 0(sp)"),
    (b"\x03\x07\x01\x00", "lb x14, 0(sp)"),
    (b"\x03\x07\x01\x02", "lb x14, 0x20(sp)"),
    (b"\x83\x15\x81\x01", "lh x11, 0x18(sp)"),
    # LBU / LHU
    (b"\x03\x4a\x91\x01", "lbu x20, 0x19(sp)"),
    (b"\x83\x55\x41\x02", "lhu x11, 0x24(sp)"),

    # Compressed load/store
    (b"\x0a\x85",       "c.mv x10, x2"),
    (b"\x4c\x49",       "c.lw x11,   0x14(x10)"),
    (b"\x42\x43",       "c.lwsp x6,  0x10(sp)"),
    (b"\x10\xcd",       "c.sw   x12, 0x18(x10)"),
    (b"\x42\xc8",       "c.swsp x16, 0x10(sp)"),

    #(b"\x01\x25",  "c.jal 0x600"), # 32-bit only

    # LUI
    (b"\x37\xfa\xff\xff", "lui   x20, #0xfffff"),
    (b"\xb7\x0a\x01\x01", "lui   x21, #0x1010"),
    (b"\x37\x5b\x34\x12", "lui   x22, #0x12345"),
    (b"\x37\x00\x00\x00", "lui   x0,  #0"),
    (b"\x65\x67",       "c.lui   x14, #0x19"),
    (b"\x75\x74",       "c.lui   x8,  #0xffffd"),

    # OR(I)
    (b"\x93\x65\x05\x0f", "ori   x11, x10, #0xf0"),
    (b"\x93\x65\x76\x00", "ori   x11, x12, #0x7"),
    (b"\x33\x66\xb5\x00", "or    x12, x10, x11"),
    (b"\x51\x8f",       "c.or    x14, x14, x12"),

    # MUL
    (b"\x33\x85\xb5\x02", "mul   x10, x11, x11"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x86\xc5\x02", "mul   x12, x11, x12"),
    (b"\x33\x07\xa0\x02", "mul   x14, x0,  x10"),
    (b"\x33\x17\xc6\x02", "mulh  x14, x12, x12"),
    (b"\x33\x27\xc6\x02", "mulhsu  x14, x12, x12"),
    (b"\x33\x27\xe6\x02", "mulhsu  x14, x12, x14"),
    (b"\x33\x27\xe6\x02", "mulhsu  x14, x12, x14"),
    (b"\x33\x27\xe6\x02", "mulhsu  x14, x12, x14"),
    (b"\xb3\x26\xb5\x02", "mulhsu  x13, x10, x11"),
    (b"\x33\x37\xe6\x02", "mulhu   x14, x12, x14"),
    (b"\xb3\x36\xe5\x02", "mulhu   x13, x10, x14"),

    # DIV/U
    (b"\x33\x46\xa6\x02", "div   x12, x12, x10"),
    (b"\x33\x56\xa6\x02", "divu  x12, x12, x10"),
    # div-by-zero corner case
    (b"\xb7\x08\x00\x00", "lui   x17, #0"),
    (b"\xb3\x45\x16\x03", "div   x11, x12, x17"),
    (b"\xb3\x58\x16\x03", "divu  x17, x12, x17"),

    # REM/U
    (b"\xb3\x65\xa6\x02", "rem   x11, x12, x10"),
    (b"\xb3\x75\xa6\x02", "remu  x11, x12, x10"),
    # corner cases
    (b"\xb7\x08\x00\x00", "lui   x17, #0"),
    (b"\xb3\x65\x16\x03", "rem   x11, x12, x17"), # division by zero
    (b"\xb3\x75\x17\x03", "remu  x11, x14, x17"),
    (b"\xb7\xf8\xff\xff", "lui   x17, #0xfffff"),
    (b"\x93\x98\x38\x01", "slli  x17, x17, #19"),
    (b"\x13\x05\xf0\xff", "addi  x10, x0,  #-1"),
    (b"\xb3\xe5\xa8\x02", "rem   x11, x17, x10"), # signed overflow

    # SUB/W
    (b"\xb3\x05\xa0\x40", "sub   x11, x0,  x10"),
    (b"\xb3\x05\xb0\x40", "sub   x11, x0,  x11"),  # neg
    (b"\xb3\x05\xa7\x40", "sub   x11, x14, x10"),
    (b"\x33\x00\xe7\x40", "sub   x0,  x14, x14"),
    (b"\x89\x8d",       "c.sub   x11,  x11, x10"),

    # XOR(I)
    (b"\xb3\x45\xb5\x00", "xor   x11, x10, x11"),
    (b"\x33\x45\xa5\x00", "xor   x10, x10, x10"),
    (b"\x33\x45\x00\x00", "xor   x10, x0,  x0"),
    (b"\xb9\x8f",       "c.xor   x15, x15, x14"),
    (b"\x93\x47\x36\x0f", "xori  x15, x12, #0xf3"),
    (b"\x93\x47\xe6\xff", "xori  x15, x12, #-2"),
    (b"\x93\x47\xf6\xff", "xori  x15, x12, #-1"),  # not

    # SLT
    (b"\x33\x28\xb5\x00", "slt   x16, x10, x11"),
    (b"\x33\x28\x84\x00", "slt   x16, x8,  x8"),
    (b"\xb3\xa0\x05\x00", "slt   x1,  x11, x0"),   # sltz
    (b"\xb3\x20\xb0\x00", "slt   x1,  x0,  x11"),  # sgtz
    (b"\xb3\x20\x00\x00", "slt   x1,  x0,  x0"),   # sltz
    (b"\xb3\xa0\xa0\x00", "slt   x1,  x1,  x10"),
    # SLTI
    (b"\x13\xa8\x15\x00", "slti  x16, x11, #1"),
    (b"\x13\x28\x87\xff", "slti  x16, x14, #-8"),
    (b"\x13\x28\xd7\x01", "slti  x16, x14, #29"),
    # SLT(I)U
    (b"\x93\x30\x15\x00", "sltiu x1,  x10, #1"),   # seqz
    (b"\x13\xb8\x05\x01", "sltiu x16, x11, #0x10"),
    (b"\x13\xb8\xb5\xff", "sltiu x16, x11, #-5"),
    (b"\x33\xb8\xb5\x00", "sltu  x16, x11, x11"),
    (b"\x33\x38\xb5\x00", "sltu  x16, x10, x11"),
    (b"\xb3\x30\xa0\x00", "sltu  x1,  x0,  x10"),  # snez
    (b"\xb3\x30\xb0\x00", "sltu  x1,  x0,  x11"),  # snez

    # SLL
    (b"\x13\xe5\xf5\x0f", "ori   x10, x11, #0xff"),
    (b"\x93\x65\xe6\x0f", "ori   x11, x12, #0xfe"),
    (b"\x33\x15\xb5\x00", "sll   x10, x10, x11"),
    (b"\xb3\x15\xb5\x00", "sll   x11, x10, x11"),
    (b"\xb3\x15\xb5\x00", "sll   x12, x13, x12"),
    (b"\x33\x16\xf8\x00", "sll   x12, x16, x15"),
    (b"\x93\x10\x85\x00", "slli  x1,  x10, #8"),
    (b"\x93\x15\xf5\x00", "slli  x11, x10, #0xf"),
    (b"\x12\x06",       "c.slli  x12, x12, #0x4"),
    (b"\xf2\x0f",       "c.slli  x31, x31, #0x1c"),
    # SRA
    (b"\x13\xe5\xf5\x0f", "ori   x10, x11, #0xff"),
    (b"\x93\x65\xe6\x0f", "ori   x11, x12, #0xfe"),
    (b"\x33\x55\xb5\x40", "sra   x10, x10, x11"),
    (b"\xb3\x55\xb5\x40", "sra   x11, x10, x11"),
    (b"\x33\xd6\xe7\x40", "sra   x12, x15, x14"),
    (b"\xb3\x55\xb5\x40", "sra   x11, x10, x11"),
    (b"\x93\x55\x85\x40", "srai  x11, x10, #8"),
    (b"\x93\x55\xf5\x40", "srai  x11, x10, #0xf"),
    (b"\x85\x85",       "c.srai  x11, x11, #0x1"),
    (b"\xb7\x05\x00\x88", "lui   x11, #0x88000"),
    (b"\xfd\x85",       "c.srai  x11, x11, #0x1f"),
    # SRL
    (b"\x13\xe5\xf5\x0f", "ori   x10, x11, #0xff"),
    (b"\x93\x65\xe6\x0f", "ori   x11, x12, #0xfe"),
    (b"\x33\x55\xb5\x00", "srl   x10, x10, x11"),
    (b"\xb3\x55\xb5\x00", "srl   x11, x10, x11"),
    (b"\x33\xd6\xe7\x00", "srl   x12, x15, x14"),
    (b"\xb3\x55\xb5\x00", "srl   x11, x10, x11"),
    (b"\x93\x55\x85\x00", "srli  x11, x10, #8"),
    (b"\x93\x55\xf5\x00", "srli  x11, x10, #0xf"),
    (b"\x85\x81",       "c.srli  x11, x11, #0x1"),
    (b"\xb7\x05\x00\x88", "lui   x11, #0x88000"),
    (b"\xfd\x81",       "c.srli  x11, x11, #0x1f"),

]

def emu_with_unicorn(opcode, istate):
    # Initialize emulator in RV32 mode
    mu = Uc(UC_ARCH_RISCV, UC_MODE_RISCV32)

    # map memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    mu.mem_write(STACK,             bytes(istate['stack']))
    mu.mem_write(HEAP,              bytes(istate['heap']))
    mu.reg_write(UC_RISCV_REG_X0,   istate['x0'])
    mu.reg_write(UC_RISCV_REG_X1,   istate['x1'])
    mu.reg_write(UC_RISCV_REG_X2,   istate['x2'])
    mu.reg_write(UC_RISCV_REG_X3,   istate['x3'])
    mu.reg_write(UC_RISCV_REG_X4,   istate['x4'])
    mu.reg_write(UC_RISCV_REG_X5,   istate['x5'])
    mu.reg_write(UC_RISCV_REG_X6,   istate['x6'])
    mu.reg_write(UC_RISCV_REG_X7,   istate['x7'])
    mu.reg_write(UC_RISCV_REG_X8,   istate['x8'])
    mu.reg_write(UC_RISCV_REG_X9,   istate['x9'])
    mu.reg_write(UC_RISCV_REG_X10,  istate['x10'])
    mu.reg_write(UC_RISCV_REG_X11,  istate['x11'])
    mu.reg_write(UC_RISCV_REG_X12,  istate['x12'])
    mu.reg_write(UC_RISCV_REG_X13,  istate['x13'])
    mu.reg_write(UC_RISCV_REG_X14,  istate['x14'])
    mu.reg_write(UC_RISCV_REG_X15,  istate['x15'])
    mu.reg_write(UC_RISCV_REG_X16,  istate['x16'])
    mu.reg_write(UC_RISCV_REG_X17,  istate['x17'])
    mu.reg_write(UC_RISCV_REG_X18,  istate['x18'])
    mu.reg_write(UC_RISCV_REG_X19,  istate['x19'])
    mu.reg_write(UC_RISCV_REG_X20,  istate['x20'])
    mu.reg_write(UC_RISCV_REG_X21,  istate['x21'])
    mu.reg_write(UC_RISCV_REG_X22,  istate['x22'])
    mu.reg_write(UC_RISCV_REG_X23,  istate['x23'])
    mu.reg_write(UC_RISCV_REG_X24,  istate['x24'])
    mu.reg_write(UC_RISCV_REG_X25,  istate['x25'])
    mu.reg_write(UC_RISCV_REG_X26,  istate['x26'])
    mu.reg_write(UC_RISCV_REG_X27,  istate['x27'])
    mu.reg_write(UC_RISCV_REG_X28,  istate['x28'])
    mu.reg_write(UC_RISCV_REG_X29,  istate['x29'])
    mu.reg_write(UC_RISCV_REG_X30,  istate['x30'])
    mu.reg_write(UC_RISCV_REG_X31,  istate['x31'])
    mu.reg_write(UC_RISCV_REG_F0,   istate['f0'])
    mu.reg_write(UC_RISCV_REG_F1,   istate['f1'])
    mu.reg_write(UC_RISCV_REG_F2,   istate['f2'])
    mu.reg_write(UC_RISCV_REG_F3,   istate['f3'])
    mu.reg_write(UC_RISCV_REG_F4,   istate['f4'])
    mu.reg_write(UC_RISCV_REG_F5,   istate['f5'])
    mu.reg_write(UC_RISCV_REG_F6,   istate['f6'])
    mu.reg_write(UC_RISCV_REG_F7,   istate['f7'])
    mu.reg_write(UC_RISCV_REG_F8,   istate['f8'])
    mu.reg_write(UC_RISCV_REG_F9,   istate['f9'])
    mu.reg_write(UC_RISCV_REG_F10,  istate['f10'])
    mu.reg_write(UC_RISCV_REG_F11,  istate['f11'])
    mu.reg_write(UC_RISCV_REG_F12,  istate['f12'])
    mu.reg_write(UC_RISCV_REG_F13,  istate['f13'])
    mu.reg_write(UC_RISCV_REG_F14,  istate['f14'])
    mu.reg_write(UC_RISCV_REG_F15,  istate['f15'])
    mu.reg_write(UC_RISCV_REG_F16,  istate['f16'])
    mu.reg_write(UC_RISCV_REG_F17,  istate['f17'])
    mu.reg_write(UC_RISCV_REG_F18,  istate['f18'])
    mu.reg_write(UC_RISCV_REG_F19,  istate['f19'])
    mu.reg_write(UC_RISCV_REG_F20,  istate['f20'])
    mu.reg_write(UC_RISCV_REG_F21,  istate['f21'])
    mu.reg_write(UC_RISCV_REG_F22,  istate['f22'])
    mu.reg_write(UC_RISCV_REG_F23,  istate['f23'])
    mu.reg_write(UC_RISCV_REG_F24,  istate['f24'])
    mu.reg_write(UC_RISCV_REG_F25,  istate['f25'])
    mu.reg_write(UC_RISCV_REG_F26,  istate['f26'])
    mu.reg_write(UC_RISCV_REG_F27,  istate['f27'])
    mu.reg_write(UC_RISCV_REG_F28,  istate['f28'])
    mu.reg_write(UC_RISCV_REG_F29,  istate['f29'])
    mu.reg_write(UC_RISCV_REG_F30,  istate['f30'])
    mu.reg_write(UC_RISCV_REG_F31,  istate['f31'])
    mu.reg_write(UC_RISCV_REG_PC,   istate['pc'])

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(istate['pc'], istate['pc'] + len(opcode), 0, 1)

    ostate = {
        "stack": mu.mem_read(STACK, 0x100),
        "heap":  mu.mem_read(HEAP, 0x100),
        "x0":    mu.reg_read(UC_RISCV_REG_X0),
        "x1":    mu.reg_read(UC_RISCV_REG_X1),
        "x2":    mu.reg_read(UC_RISCV_REG_X2),
        "x3":    mu.reg_read(UC_RISCV_REG_X3),
        "x4":    mu.reg_read(UC_RISCV_REG_X4),
        "x5":    mu.reg_read(UC_RISCV_REG_X5),
        "x6":    mu.reg_read(UC_RISCV_REG_X6),
        "x7":    mu.reg_read(UC_RISCV_REG_X7),
        "x8":    mu.reg_read(UC_RISCV_REG_X8),
        "x9":    mu.reg_read(UC_RISCV_REG_X9),
        "x10":   mu.reg_read(UC_RISCV_REG_X10),
        "x11":   mu.reg_read(UC_RISCV_REG_X11),
        "x12":   mu.reg_read(UC_RISCV_REG_X12),
        "x13":   mu.reg_read(UC_RISCV_REG_X13),
        "x14":   mu.reg_read(UC_RISCV_REG_X14),
        "x15":   mu.reg_read(UC_RISCV_REG_X15),
        "x16":   mu.reg_read(UC_RISCV_REG_X16),
        "x17":   mu.reg_read(UC_RISCV_REG_X17),
        "x18":   mu.reg_read(UC_RISCV_REG_X18),
        "x19":   mu.reg_read(UC_RISCV_REG_X19),
        "x20":   mu.reg_read(UC_RISCV_REG_X20),
        "x21":   mu.reg_read(UC_RISCV_REG_X21),
        "x22":   mu.reg_read(UC_RISCV_REG_X22),
        "x23":   mu.reg_read(UC_RISCV_REG_X23),
        "x24":   mu.reg_read(UC_RISCV_REG_X24),
        "x25":   mu.reg_read(UC_RISCV_REG_X25),
        "x26":   mu.reg_read(UC_RISCV_REG_X26),
        "x27":   mu.reg_read(UC_RISCV_REG_X27),
        "x28":   mu.reg_read(UC_RISCV_REG_X28),
        "x29":   mu.reg_read(UC_RISCV_REG_X29),
        "x30":   mu.reg_read(UC_RISCV_REG_X30),
        "x31":   mu.reg_read(UC_RISCV_REG_X31),
        "f0":    mu.reg_read(UC_RISCV_REG_F0),
        "f1":    mu.reg_read(UC_RISCV_REG_F1),
        "f2":    mu.reg_read(UC_RISCV_REG_F2),
        "f3":    mu.reg_read(UC_RISCV_REG_F3),
        "f4":    mu.reg_read(UC_RISCV_REG_F4),
        "f5":    mu.reg_read(UC_RISCV_REG_F5),
        "f6":    mu.reg_read(UC_RISCV_REG_F6),
        "f7":    mu.reg_read(UC_RISCV_REG_F7),
        "f8":    mu.reg_read(UC_RISCV_REG_F8),
        "f9":    mu.reg_read(UC_RISCV_REG_F9),
        "f10":   mu.reg_read(UC_RISCV_REG_F10),
        "f11":   mu.reg_read(UC_RISCV_REG_F11),
        "f12":   mu.reg_read(UC_RISCV_REG_F12),
        "f13":   mu.reg_read(UC_RISCV_REG_F13),
        "f14":   mu.reg_read(UC_RISCV_REG_F14),
        "f15":   mu.reg_read(UC_RISCV_REG_F15),
        "f16":   mu.reg_read(UC_RISCV_REG_F16),
        "f17":   mu.reg_read(UC_RISCV_REG_F17),
        "f18":   mu.reg_read(UC_RISCV_REG_F18),
        "f19":   mu.reg_read(UC_RISCV_REG_F19),
        "f20":   mu.reg_read(UC_RISCV_REG_F20),
        "f21":   mu.reg_read(UC_RISCV_REG_F21),
        "f22":   mu.reg_read(UC_RISCV_REG_F22),
        "f23":   mu.reg_read(UC_RISCV_REG_F23),
        "f24":   mu.reg_read(UC_RISCV_REG_F24),
        "f25":   mu.reg_read(UC_RISCV_REG_F25),
        "f26":   mu.reg_read(UC_RISCV_REG_F26),
        "f27":   mu.reg_read(UC_RISCV_REG_F27),
        "f28":   mu.reg_read(UC_RISCV_REG_F28),
        "f29":   mu.reg_read(UC_RISCV_REG_F29),
        "f30":   mu.reg_read(UC_RISCV_REG_F30),
        "f31":   mu.reg_read(UC_RISCV_REG_F31),
        "pc":    mu.reg_read(UC_RISCV_REG_PC),
    }
    return ostate


def emu_with_triton(opcode, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.RV32)

    inst = Instruction(opcode)
    inst.setAddress(istate['pc'])

    ctx.setConcreteMemoryAreaValue(STACK,           bytes(istate['stack']))
    ctx.setConcreteMemoryAreaValue(HEAP,            bytes(istate['heap']))
    ctx.setConcreteRegisterValue(ctx.registers.x0,  0)
    ctx.setConcreteRegisterValue(ctx.registers.x1,  istate['x1'])
    ctx.setConcreteRegisterValue(ctx.registers.x2,  istate['x2'])
    ctx.setConcreteRegisterValue(ctx.registers.x3,  istate['x3'])
    ctx.setConcreteRegisterValue(ctx.registers.x4,  istate['x4'])
    ctx.setConcreteRegisterValue(ctx.registers.x5,  istate['x5'])
    ctx.setConcreteRegisterValue(ctx.registers.x6,  istate['x6'])
    ctx.setConcreteRegisterValue(ctx.registers.x7,  istate['x7'])
    ctx.setConcreteRegisterValue(ctx.registers.x8,  istate['x8'])
    ctx.setConcreteRegisterValue(ctx.registers.x9,  istate['x9'])
    ctx.setConcreteRegisterValue(ctx.registers.x10, istate['x10'])
    ctx.setConcreteRegisterValue(ctx.registers.x11, istate['x11'])
    ctx.setConcreteRegisterValue(ctx.registers.x12, istate['x12'])
    ctx.setConcreteRegisterValue(ctx.registers.x13, istate['x13'])
    ctx.setConcreteRegisterValue(ctx.registers.x14, istate['x14'])
    ctx.setConcreteRegisterValue(ctx.registers.x15, istate['x15'])
    ctx.setConcreteRegisterValue(ctx.registers.x16, istate['x16'])
    ctx.setConcreteRegisterValue(ctx.registers.x17, istate['x17'])
    ctx.setConcreteRegisterValue(ctx.registers.x18, istate['x18'])
    ctx.setConcreteRegisterValue(ctx.registers.x19, istate['x19'])
    ctx.setConcreteRegisterValue(ctx.registers.x20, istate['x20'])
    ctx.setConcreteRegisterValue(ctx.registers.x21, istate['x21'])
    ctx.setConcreteRegisterValue(ctx.registers.x22, istate['x22'])
    ctx.setConcreteRegisterValue(ctx.registers.x23, istate['x23'])
    ctx.setConcreteRegisterValue(ctx.registers.x24, istate['x24'])
    ctx.setConcreteRegisterValue(ctx.registers.x25, istate['x25'])
    ctx.setConcreteRegisterValue(ctx.registers.x26, istate['x26'])
    ctx.setConcreteRegisterValue(ctx.registers.x27, istate['x27'])
    ctx.setConcreteRegisterValue(ctx.registers.x28, istate['x28'])
    ctx.setConcreteRegisterValue(ctx.registers.x29, istate['x29'])
    ctx.setConcreteRegisterValue(ctx.registers.x30, istate['x30'])
    ctx.setConcreteRegisterValue(ctx.registers.x31, istate['x31'])
    ctx.setConcreteRegisterValue(ctx.registers.f0,  istate['f0'])
    ctx.setConcreteRegisterValue(ctx.registers.f1,  istate['f1'])
    ctx.setConcreteRegisterValue(ctx.registers.f2,  istate['f2'])
    ctx.setConcreteRegisterValue(ctx.registers.f3,  istate['f3'])
    ctx.setConcreteRegisterValue(ctx.registers.f4,  istate['f4'])
    ctx.setConcreteRegisterValue(ctx.registers.f5,  istate['f5'])
    ctx.setConcreteRegisterValue(ctx.registers.f6,  istate['f6'])
    ctx.setConcreteRegisterValue(ctx.registers.f7,  istate['f7'])
    ctx.setConcreteRegisterValue(ctx.registers.f8,  istate['f8'])
    ctx.setConcreteRegisterValue(ctx.registers.f9,  istate['f9'])
    ctx.setConcreteRegisterValue(ctx.registers.f10, istate['f10'])
    ctx.setConcreteRegisterValue(ctx.registers.f11, istate['f11'])
    ctx.setConcreteRegisterValue(ctx.registers.f12, istate['f12'])
    ctx.setConcreteRegisterValue(ctx.registers.f13, istate['f13'])
    ctx.setConcreteRegisterValue(ctx.registers.f14, istate['f14'])
    ctx.setConcreteRegisterValue(ctx.registers.f15, istate['f15'])
    ctx.setConcreteRegisterValue(ctx.registers.f16, istate['f16'])
    ctx.setConcreteRegisterValue(ctx.registers.f17, istate['f17'])
    ctx.setConcreteRegisterValue(ctx.registers.f18, istate['f18'])
    ctx.setConcreteRegisterValue(ctx.registers.f19, istate['f19'])
    ctx.setConcreteRegisterValue(ctx.registers.f20, istate['f20'])
    ctx.setConcreteRegisterValue(ctx.registers.f21, istate['f21'])
    ctx.setConcreteRegisterValue(ctx.registers.f22, istate['f22'])
    ctx.setConcreteRegisterValue(ctx.registers.f23, istate['f23'])
    ctx.setConcreteRegisterValue(ctx.registers.f24, istate['f24'])
    ctx.setConcreteRegisterValue(ctx.registers.f25, istate['f25'])
    ctx.setConcreteRegisterValue(ctx.registers.f26, istate['f26'])
    ctx.setConcreteRegisterValue(ctx.registers.f27, istate['f27'])
    ctx.setConcreteRegisterValue(ctx.registers.f28, istate['f28'])
    ctx.setConcreteRegisterValue(ctx.registers.f29, istate['f29'])
    ctx.setConcreteRegisterValue(ctx.registers.f30, istate['f30'])
    ctx.setConcreteRegisterValue(ctx.registers.f31, istate['f31'])
    ctx.setConcreteRegisterValue(ctx.registers.pc,  istate['pc'])

    ctx.processing(inst)

    #print
    #print(inst)
    #for x in inst.getSymbolicExpressions():
    #    print(x)
    #print

    ostate = {
        "stack": ctx.getConcreteMemoryAreaValue(STACK, 0x100),
        "heap":  ctx.getConcreteMemoryAreaValue(HEAP, 0x100),

        "x0":    0,
        "x1":    ctx.getSymbolicRegisterValue(ctx.registers.x1),
        "x2":    ctx.getSymbolicRegisterValue(ctx.registers.x2),
        "x3":    ctx.getSymbolicRegisterValue(ctx.registers.x3),
        "x4":    ctx.getSymbolicRegisterValue(ctx.registers.x4),
        "x5":    ctx.getSymbolicRegisterValue(ctx.registers.x5),
        "x6":    ctx.getSymbolicRegisterValue(ctx.registers.x6),
        "x7":    ctx.getSymbolicRegisterValue(ctx.registers.x7),
        "x8":    ctx.getSymbolicRegisterValue(ctx.registers.x8),
        "x9":    ctx.getSymbolicRegisterValue(ctx.registers.x9),
        "x10":   ctx.getSymbolicRegisterValue(ctx.registers.x10),
        "x11":   ctx.getSymbolicRegisterValue(ctx.registers.x11),
        "x12":   ctx.getSymbolicRegisterValue(ctx.registers.x12),
        "x13":   ctx.getSymbolicRegisterValue(ctx.registers.x13),
        "x14":   ctx.getSymbolicRegisterValue(ctx.registers.x14),
        "x15":   ctx.getSymbolicRegisterValue(ctx.registers.x15),
        "x16":   ctx.getSymbolicRegisterValue(ctx.registers.x16),
        "x17":   ctx.getSymbolicRegisterValue(ctx.registers.x17),
        "x18":   ctx.getSymbolicRegisterValue(ctx.registers.x18),
        "x19":   ctx.getSymbolicRegisterValue(ctx.registers.x19),
        "x20":   ctx.getSymbolicRegisterValue(ctx.registers.x20),
        "x21":   ctx.getSymbolicRegisterValue(ctx.registers.x21),
        "x22":   ctx.getSymbolicRegisterValue(ctx.registers.x22),
        "x23":   ctx.getSymbolicRegisterValue(ctx.registers.x23),
        "x24":   ctx.getSymbolicRegisterValue(ctx.registers.x24),
        "x25":   ctx.getSymbolicRegisterValue(ctx.registers.x25),
        "x26":   ctx.getSymbolicRegisterValue(ctx.registers.x26),
        "x27":   ctx.getSymbolicRegisterValue(ctx.registers.x27),
        "x28":   ctx.getSymbolicRegisterValue(ctx.registers.x28),
        "x29":   ctx.getSymbolicRegisterValue(ctx.registers.x29),
        "x30":   ctx.getSymbolicRegisterValue(ctx.registers.x30),
        "x31":   ctx.getSymbolicRegisterValue(ctx.registers.x31),
        "f0":    ctx.getSymbolicRegisterValue(ctx.registers.f0),
        "f1":    ctx.getSymbolicRegisterValue(ctx.registers.f1),
        "f2":    ctx.getSymbolicRegisterValue(ctx.registers.f2),
        "f3":    ctx.getSymbolicRegisterValue(ctx.registers.f3),
        "f4":    ctx.getSymbolicRegisterValue(ctx.registers.f4),
        "f5":    ctx.getSymbolicRegisterValue(ctx.registers.f5),
        "f6":    ctx.getSymbolicRegisterValue(ctx.registers.f6),
        "f7":    ctx.getSymbolicRegisterValue(ctx.registers.f7),
        "f8":    ctx.getSymbolicRegisterValue(ctx.registers.f8),
        "f9":    ctx.getSymbolicRegisterValue(ctx.registers.f9),
        "f10":   ctx.getSymbolicRegisterValue(ctx.registers.f10),
        "f11":   ctx.getSymbolicRegisterValue(ctx.registers.f11),
        "f12":   ctx.getSymbolicRegisterValue(ctx.registers.f12),
        "f13":   ctx.getSymbolicRegisterValue(ctx.registers.f13),
        "f14":   ctx.getSymbolicRegisterValue(ctx.registers.f14),
        "f15":   ctx.getSymbolicRegisterValue(ctx.registers.f15),
        "f16":   ctx.getSymbolicRegisterValue(ctx.registers.f16),
        "f17":   ctx.getSymbolicRegisterValue(ctx.registers.f17),
        "f18":   ctx.getSymbolicRegisterValue(ctx.registers.f18),
        "f19":   ctx.getSymbolicRegisterValue(ctx.registers.f19),
        "f20":   ctx.getSymbolicRegisterValue(ctx.registers.f20),
        "f21":   ctx.getSymbolicRegisterValue(ctx.registers.f21),
        "f22":   ctx.getSymbolicRegisterValue(ctx.registers.f22),
        "f23":   ctx.getSymbolicRegisterValue(ctx.registers.f23),
        "f24":   ctx.getSymbolicRegisterValue(ctx.registers.f24),
        "f25":   ctx.getSymbolicRegisterValue(ctx.registers.f25),
        "f26":   ctx.getSymbolicRegisterValue(ctx.registers.f26),
        "f27":   ctx.getSymbolicRegisterValue(ctx.registers.f27),
        "f28":   ctx.getSymbolicRegisterValue(ctx.registers.f28),
        "f29":   ctx.getSymbolicRegisterValue(ctx.registers.f29),
        "f30":   ctx.getSymbolicRegisterValue(ctx.registers.f30),
        "f31":   ctx.getSymbolicRegisterValue(ctx.registers.f31),
        "pc":    ctx.getSymbolicRegisterValue(ctx.registers.pc),
    }
    return ostate


def diff_state(state1, state2):
    for k, v in list(state1.items()):
        if (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: (UC) != (TT)' %(k))
        elif not (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: %#x (UC) != %#x (TT)' %(k, v, state2[k]))
    return


if __name__ == '__main__':
    # initial state
    state = {
        "stack": bytearray(b"".join([pack('B', 255 - i) for i in range(256)])),
        "heap":  bytearray(b"".join([pack('B', i) for i in range(256)])),
        "x0":    0x0,
        "x1":    0x0,
        "x2":    STACK,
        "x3":    0x0,
        "x4":    0x0,
        "x5":    0x0,
        "x6":    0x0,
        "x7":    0x0,
        "x8":    0x0,
        "x9":    0x0,
        "x10":   0x0,
        "x11":   0x0,
        "x12":   0x0,
        "x13":   0x0,
        "x14":   0x0,
        "x15":   0x0,
        "x16":   0x0,
        "x17":   0x0,
        "x18":   0x0,
        "x19":   0x0,
        "x20":   0x0,
        "x21":   0x0,
        "x22":   0x0,
        "x23":   0x0,
        "x24":   0x0,
        "x25":   0x0,
        "x26":   0x0,
        "x27":   0x0,
        "x28":   0x0,
        "x29":   0x0,
        "x30":   0x0,
        "x31":   0x2107ff,
        "f0":    0x89abcdef,
        "f1":    0x76543210,
        "f2":    0x56567878,
        "f3":    0x9098cd01,
        "f4":    0x0,
        "f5":    0x0,
        "f6":    0x0,
        "f7":    0x0,
        "f8":    0x0,
        "f9":    0x0,
        "f10":   0x0,
        "f11":   0x0,
        "f12":   0x0,
        "f13":   0x0,
        "f14":   0x0,
        "f15":   0x0,
        "f16":   0x0,
        "f17":   0x0,
        "f18":   0x0,
        "f19":   0x0,
        "f20":   0x0,
        "f21":   0x0,
        "f22":   0x0,
        "f23":   0x0,
        "f24":   0x0,
        "f25":   0x0,
        "f26":   0x0,
        "f27":   0x0,
        "f28":   0x0,
        "f29":   0x0,
        "f30":   0x0,
        "f31":   0x0,
        "pc":    ADDR,
    }

    for opcode, disassembly in CODE:
        try:
            uc_state = emu_with_unicorn(opcode, state)
            tt_state = emu_with_triton(opcode, state)
        except Exception as e:
            print('[KO] %s' %(disassembly))
            print('\t%s' %(e))
            sys.exit(-1)

        if uc_state != tt_state:
            print('[KO] %s' %(disassembly))
            diff_state(uc_state, tt_state)
            sys.exit(-1)

        print('[OK] %s' %(disassembly))
        state = tt_state

    sys.exit(0)
