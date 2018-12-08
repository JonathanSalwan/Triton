#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## TODO : Check memory
##

import sys
import pprint

from triton              import *
from unicorn             import *
from unicorn.arm64_const import *

ADDR  = 0x100000
STACK = 0x200000
SIZE  = 3 * 1024 * 1024
CODE  = [
    ("\x80\x46\x82\xd2", "movz x0, #0x1234"),
    ("\x80\x46\xa2\xd2", "movz x0, #0x1234, lsl #16"),
    ("\x80\x46\xc2\xd2", "movz x0, #0x1234, lsl #32"),
    ("\x80\x46\xe2\xd2", "movz x0, #0x1234, lsl #48"),
    ("\x21\x64\x88\xd2", "movz x1, #0x4321"),
    ("\x21\x64\xa8\xd2", "movz x1, #0x4321, lsl #16"),
    ("\x21\x64\xc8\xd2", "movz x1, #0x4321, lsl #32"),
    ("\x21\x64\xe8\xd2", "movz x1, #0x4321, lsl #48"),
    ("\x21\x64\xe8\xd2", "movz x1, #0x4321, lsl #48"),
    ("\x21\x64\xc8\xd2", "movz x1, #0x4321, lsl #32"),
    ("\x21\x64\xa8\xd2", "movz x1, #0x4321, lsl #16"),
    ("\x60\x00\x02\x8b", "add x0, x3, x2"),
    ("\x20\x00\x02\x8b", "add x0, x1, x2"),
    ("\x80\x46\xa2\xd2", "movz x0, #0x1234, lsl #16"),
    ("\x00\x00\x00\x8b", "add x0, x0, x0"),
    ("\x60\xc0\x22\x8b", "add x0, x3, w2, sxtw"),
    ("\x82\x46\x82\xd2", "movz x2, #0x1234"),
    ("\x01\xcf\x8a\xd2", "movz x1, #0x5678"),
    ("\x20\x80\x22\x8b", "add x0, x1, w2, sxtb"),
    ("\x20\xa0\x22\x8b", "add x0, x1, w2, sxth"),
    ("\x20\xc0\x22\x8b", "add x0, x1, w2, sxtw"),
    ("\x20\xe0\x22\x8b", "add x0, x1, x2, sxtx"),
    ("\x20\x00\x02\x8b", "add x0, x1, x2, lsl #0"),
    ("\x20\x04\x02\x8b", "add x0, x1, x2, lsl #1"),
    ("\x20\x20\x02\x8b", "add x0, x1, x2, lsl #8"),
    ("\x20\x40\x02\x8b", "add x0, x1, x2, lsl #16"),
    ("\x20\x80\x02\x8b", "add x0, x1, x2, lsl #32"),
    ("\x20\x84\x02\x8b", "add x0, x1, x2, lsl #33"),
    ("\x20\x88\x02\x8b", "add x0, x1, x2, lsl #34"),
    ("\x20\x00\x42\x8b", "add x0, x1, x2, lsr #0"),
    ("\x20\x04\x42\x8b", "add x0, x1, x2, lsr #1"),
    ("\x20\x20\x42\x8b", "add x0, x1, x2, lsr #8"),
    ("\x20\x40\x42\x8b", "add x0, x1, x2, lsr #16"),
    ("\x20\x80\x42\x8b", "add x0, x1, x2, lsr #32"),
    ("\x20\x84\x42\x8b", "add x0, x1, x2, lsr #33"),
    ("\x20\x88\x42\x8b", "add x0, x1, x2, lsr #34"),
    ("\x20\x20\x82\x8b", "add x0, x1, x2, asr #8"),
    ("\x20\x40\x82\x8b", "add x0, x1, x2, asr #16"),
    ("\x20\x80\x82\x8b", "add x0, x1, x2, asr #32"),
    ("\x20\x84\x82\x8b", "add x0, x1, x2, asr #33"),
    ("\x20\x88\x82\x8b", "add x0, x1, x2, asr #34"),
    ("\x20\x88\x82\x8b", "add x0, x1, x2, asr #34"),
    ("\x20\x88\x19\x91", "add x0, x1, #1634"),
    ("\x20\x58\x21\x91", "add x0, x1, #2134"),
    ("\x20\x58\x61\x91", "add x0, x1, #2134, lsl #12"),
    ("\x20\x00\x02\x9a", "adc x0, x1, x2"),
    ("\x20\x00\x02\x1a", "adc w0, w1, w2"),
]

def emu_with_unicorn(opcode, istate=None):
    # Initialize emulator in X86-32bit mode
    mu = Uc(UC_ARCH_ARM64, UC_MODE_ARM)

    # map 2MB memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    mu.mem_write(ADDR, opcode)

    if istate:
        mu.reg_write(UC_ARM64_REG_X0,   istate['x0'])
        mu.reg_write(UC_ARM64_REG_X1,   istate['x1'])
        mu.reg_write(UC_ARM64_REG_X2,   istate['x2'])
        mu.reg_write(UC_ARM64_REG_X3,   istate['x3'])
        mu.reg_write(UC_ARM64_REG_X4,   istate['x4'])
        mu.reg_write(UC_ARM64_REG_X5,   istate['x5'])
        mu.reg_write(UC_ARM64_REG_X6,   istate['x6'])
        mu.reg_write(UC_ARM64_REG_X7,   istate['x7'])
        mu.reg_write(UC_ARM64_REG_X8,   istate['x8'])
        mu.reg_write(UC_ARM64_REG_X9,   istate['x9'])
        mu.reg_write(UC_ARM64_REG_X10,  istate['x10'])
        mu.reg_write(UC_ARM64_REG_X11,  istate['x11'])
        mu.reg_write(UC_ARM64_REG_X12,  istate['x12'])
        mu.reg_write(UC_ARM64_REG_X13,  istate['x13'])
        mu.reg_write(UC_ARM64_REG_X14,  istate['x14'])
        mu.reg_write(UC_ARM64_REG_X15,  istate['x15'])
        mu.reg_write(UC_ARM64_REG_X16,  istate['x16'])
        mu.reg_write(UC_ARM64_REG_X17,  istate['x17'])
        mu.reg_write(UC_ARM64_REG_X18,  istate['x18'])
        mu.reg_write(UC_ARM64_REG_X19,  istate['x19'])
        mu.reg_write(UC_ARM64_REG_X20,  istate['x20'])
        mu.reg_write(UC_ARM64_REG_X21,  istate['x21'])
        mu.reg_write(UC_ARM64_REG_X22,  istate['x22'])
        mu.reg_write(UC_ARM64_REG_X23,  istate['x23'])
        mu.reg_write(UC_ARM64_REG_X24,  istate['x24'])
        mu.reg_write(UC_ARM64_REG_X25,  istate['x25'])
        mu.reg_write(UC_ARM64_REG_X26,  istate['x26'])
        mu.reg_write(UC_ARM64_REG_X27,  istate['x27'])
        mu.reg_write(UC_ARM64_REG_X28,  istate['x28'])
        mu.reg_write(UC_ARM64_REG_X29,  istate['x29'])
        mu.reg_write(UC_ARM64_REG_X30,  istate['x30'])
        mu.reg_write(UC_ARM64_REG_PC,   istate['pc'])
        mu.reg_write(UC_ARM64_REG_SP,   istate['sp'])
        mu.reg_write(UC_ARM64_REG_NZCV, istate['n'] << 31 | istate['z'] << 30 | istate['c'] << 29 | istate['v'] << 28)
    else:
        ## Why it's set at the first inst? Dunno...
        mu.reg_write(UC_ARM64_REG_NZCV, 0)

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(ADDR, ADDR + len(opcode))

    ostate = {
        "x0":  mu.reg_read(UC_ARM64_REG_X0),
        "x1":  mu.reg_read(UC_ARM64_REG_X1),
        "x2":  mu.reg_read(UC_ARM64_REG_X2),
        "x3":  mu.reg_read(UC_ARM64_REG_X3),
        "x4":  mu.reg_read(UC_ARM64_REG_X4),
        "x5":  mu.reg_read(UC_ARM64_REG_X5),
        "x6":  mu.reg_read(UC_ARM64_REG_X6),
        "x7":  mu.reg_read(UC_ARM64_REG_X7),
        "x8":  mu.reg_read(UC_ARM64_REG_X8),
        "x9":  mu.reg_read(UC_ARM64_REG_X9),
        "x10": mu.reg_read(UC_ARM64_REG_X10),
        "x11": mu.reg_read(UC_ARM64_REG_X11),
        "x12": mu.reg_read(UC_ARM64_REG_X12),
        "x13": mu.reg_read(UC_ARM64_REG_X13),
        "x14": mu.reg_read(UC_ARM64_REG_X14),
        "x15": mu.reg_read(UC_ARM64_REG_X15),
        "x16": mu.reg_read(UC_ARM64_REG_X16),
        "x17": mu.reg_read(UC_ARM64_REG_X17),
        "x18": mu.reg_read(UC_ARM64_REG_X18),
        "x19": mu.reg_read(UC_ARM64_REG_X19),
        "x20": mu.reg_read(UC_ARM64_REG_X20),
        "x21": mu.reg_read(UC_ARM64_REG_X21),
        "x22": mu.reg_read(UC_ARM64_REG_X22),
        "x23": mu.reg_read(UC_ARM64_REG_X23),
        "x24": mu.reg_read(UC_ARM64_REG_X24),
        "x25": mu.reg_read(UC_ARM64_REG_X25),
        "x26": mu.reg_read(UC_ARM64_REG_X26),
        "x27": mu.reg_read(UC_ARM64_REG_X27),
        "x28": mu.reg_read(UC_ARM64_REG_X28),
        "x29": mu.reg_read(UC_ARM64_REG_X29),
        "x30": mu.reg_read(UC_ARM64_REG_X30),
        "x30": mu.reg_read(UC_ARM64_REG_X30),
        "pc":  mu.reg_read(UC_ARM64_REG_PC),
        "sp":  mu.reg_read(UC_ARM64_REG_SP),
        "n": ((mu.reg_read(UC_ARM64_REG_NZCV) >> 31) & 1),
        "z": ((mu.reg_read(UC_ARM64_REG_NZCV) >> 30) & 1),
        "c": ((mu.reg_read(UC_ARM64_REG_NZCV) >> 29) & 1),
        "v": ((mu.reg_read(UC_ARM64_REG_NZCV) >> 28) & 1),
    }
    return ostate

def emu_with_triton(opcode, istate=None):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.AARCH64)

    inst = Instruction(opcode)
    inst.setAddress(ADDR)

    if istate:
        ctx.setConcreteRegisterValue(ctx.registers.x0,  istate['x0'])
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
        ctx.setConcreteRegisterValue(ctx.registers.pc,  istate['pc'])
        ctx.setConcreteRegisterValue(ctx.registers.sp,  istate['sp'])
        ctx.setConcreteRegisterValue(ctx.registers.n,   istate['n'])
        ctx.setConcreteRegisterValue(ctx.registers.z,   istate['z'])
        ctx.setConcreteRegisterValue(ctx.registers.c,   istate['c'])
        ctx.setConcreteRegisterValue(ctx.registers.v,   istate['v'])

    ctx.processing(inst)

    ostate = {
        "x0":  ctx.getSymbolicRegisterValue(ctx.registers.x0),
        "x1":  ctx.getSymbolicRegisterValue(ctx.registers.x1),
        "x2":  ctx.getSymbolicRegisterValue(ctx.registers.x2),
        "x3":  ctx.getSymbolicRegisterValue(ctx.registers.x3),
        "x4":  ctx.getSymbolicRegisterValue(ctx.registers.x4),
        "x5":  ctx.getSymbolicRegisterValue(ctx.registers.x5),
        "x6":  ctx.getSymbolicRegisterValue(ctx.registers.x6),
        "x7":  ctx.getSymbolicRegisterValue(ctx.registers.x7),
        "x8":  ctx.getSymbolicRegisterValue(ctx.registers.x8),
        "x9":  ctx.getSymbolicRegisterValue(ctx.registers.x9),
        "x10": ctx.getSymbolicRegisterValue(ctx.registers.x10),
        "x11": ctx.getSymbolicRegisterValue(ctx.registers.x11),
        "x12": ctx.getSymbolicRegisterValue(ctx.registers.x12),
        "x13": ctx.getSymbolicRegisterValue(ctx.registers.x13),
        "x14": ctx.getSymbolicRegisterValue(ctx.registers.x14),
        "x15": ctx.getSymbolicRegisterValue(ctx.registers.x15),
        "x16": ctx.getSymbolicRegisterValue(ctx.registers.x16),
        "x17": ctx.getSymbolicRegisterValue(ctx.registers.x17),
        "x18": ctx.getSymbolicRegisterValue(ctx.registers.x18),
        "x19": ctx.getSymbolicRegisterValue(ctx.registers.x19),
        "x20": ctx.getSymbolicRegisterValue(ctx.registers.x20),
        "x21": ctx.getSymbolicRegisterValue(ctx.registers.x21),
        "x22": ctx.getSymbolicRegisterValue(ctx.registers.x22),
        "x23": ctx.getSymbolicRegisterValue(ctx.registers.x23),
        "x24": ctx.getSymbolicRegisterValue(ctx.registers.x24),
        "x25": ctx.getSymbolicRegisterValue(ctx.registers.x25),
        "x26": ctx.getSymbolicRegisterValue(ctx.registers.x26),
        "x27": ctx.getSymbolicRegisterValue(ctx.registers.x27),
        "x28": ctx.getSymbolicRegisterValue(ctx.registers.x28),
        "x29": ctx.getSymbolicRegisterValue(ctx.registers.x29),
        "x30": ctx.getSymbolicRegisterValue(ctx.registers.x30),
        "x30": ctx.getSymbolicRegisterValue(ctx.registers.x30),
        "pc":  ctx.getSymbolicRegisterValue(ctx.registers.pc),
        "sp":  ctx.getSymbolicRegisterValue(ctx.registers.sp),
        "n":   ctx.getSymbolicRegisterValue(ctx.registers.n),
        "z":   ctx.getSymbolicRegisterValue(ctx.registers.z),
        "c":   ctx.getSymbolicRegisterValue(ctx.registers.c),
        "v":   ctx.getSymbolicRegisterValue(ctx.registers.v),
    }
    return ostate

def diff_state(state1, state2):
    for k, v in state1.items():
        if v != state2[k]:
            print '\t%s: %#x (UC) != %#x (TT)' %(k, v, state2[k])
    return

if __name__ == '__main__':
    state = None

    for opcode, disassembly in CODE:
        try:
            uc_state = emu_with_unicorn(opcode, state)
            tt_state = emu_with_triton(opcode, state)
        except Exception, e:
            print '[KO] %s' %(disassembly)
            print '\t%s' %(e)
            sys.exit(-1)

        if uc_state != tt_state:
            print '[KO] %s' %(disassembly)
            diff_state(uc_state, tt_state)
            sys.exit(-1)

        print '[OK] %s' %(disassembly)
        state = tt_state

    sys.exit(0)
