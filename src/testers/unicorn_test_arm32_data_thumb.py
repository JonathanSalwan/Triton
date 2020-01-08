#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from __future__          import print_function
from triton              import *
from unicorn             import *
from unicorn.arm_const   import *

import sys
import pprint
import random

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024
CODE  = [
    # ADC -------------------------------------------------------------------- #
    (b"\x41\xf1\x02\x00", "adc r0, r1, #2"),
    (b"\x41\xeb\x02\x00", "adc r0, r1, r2"),

    # ADCS ------------------------------------------------------------------- #
    (b"\x51\xf1\x02\x00", "adcs r0, r1, #2"),
    (b"\x51\xeb\x02\x00", "adcs r0, r1, r2"),

    # ADD -------------------------------------------------------------------- #
    (b"\x00\xf1\x02\x00", "add r0, #2"),
    (b"\x00\xf1\x02\x00", "add r0, r0, #2"),
    (b"\x01\xf1\x02\x00", "add r0, r1, #2"),
    (b"\x01\xeb\x02\x00", "add r0, r1, r2"),
    (b"\x01\xeb\xa2\x00", "add r0, r1, r2, asr #2"),
    (b"\x01\xeb\x82\x00", "add r0, r1, r2, lsl #2"),
    (b"\x01\xeb\x92\x00", "add r0, r1, r2, lsr #2"),
    (b"\x01\xeb\xb2\x00", "add r0, r1, r2, ror #2"),
    (b"\x01\xeb\x32\x00", "add r0, r1, r2, rrx"),

    # ADDS ------------------------------------------------------------------- #
    (b"\x02\x30",         "adds r0, #2"),
    (b"\x80\x1c",         "adds r0, r0, #2"),
    (b"\x88\x1c",         "adds r0, r1, #2"),
    (b"\x88\x18",         "adds r0, r1, r2"),
    (b"\x11\xeb\xa2\x00", "adds r0, r1, r2, asr #2"),
    (b"\x11\xeb\x82\x00", "adds r0, r1, r2, lsl #2"),
    (b"\x11\xeb\x92\x00", "adds r0, r1, r2, lsr #2"),
    (b"\x11\xeb\xb2\x00", "adds r0, r1, r2, ror #2"),
    (b"\x11\xeb\x32\x00", "adds r0, r1, r2, rrx"),

    # CMP -------------------------------------------------------------------- #
    (b"\x88\x42",         "cmp r0, r1"),
    (b"\x04\x28",         "cmp r0, #4"),
    (b"\xb0\xeb\x21\x1f", "cmp r0, r1, asr #4"),
    (b"\xb0\xeb\x01\x1f", "cmp r0, r1, lsl #4"),
    (b"\xb0\xeb\x11\x1f", "cmp r0, r1, lsr #4"),
    (b"\xb0\xeb\x31\x1f", "cmp r0, r1, ror #4"),
    (b"\xb0\xeb\x31\x0f", "cmp r0, r1, rrx"),

    # EOR -------------------------------------------------------------------- #
    (b"\x80\xea\x01\x00", "eor r0, r1"),

    # MOV -------------------------------------------------------------------- #
    (b"\x4f\xf0\x02\x00", "mov r0, #2"),
    (b"\x11\x46",         "mov r1, r2"),

    # MOVS ------------------------------------------------------------------- #
    (b"\x02\x20",         "movs r0, #2"),
    (b"\x11\x00",         "movs r1, r2"),

    # MOV(S) with SP as operand ---------------------------------------------- #
    (b"\x85\x46",         "mov sp, r0"),
    (b"\x5f\xea\x00\x0d", "movs sp, r0"),

    # SUB -------------------------------------------------------------------- #
    (b"\xa0\xf1\x02\x00", "sub r0, #2"),
    (b"\xa0\xf1\x02\x00", "sub r0, r0, #2"),
    (b"\xa1\xf1\x02\x00", "sub r0, r1, #2"),
    (b"\xa1\xeb\x02\x00", "sub r0, r1, r2"),
    (b"\xa1\xeb\xa2\x00", "sub r0, r1, r2, asr #2"),
    (b"\xa1\xeb\x82\x00", "sub r0, r1, r2, lsl #2"),
    (b"\xa1\xeb\x92\x00", "sub r0, r1, r2, lsr #2"),
    (b"\xa1\xeb\xb2\x00", "sub r0, r1, r2, ror #2"),
    (b"\xa1\xeb\x32\x00", "sub r0, r1, r2, rrx"),

    # SUBS ------------------------------------------------------------------- #
    (b"\x02\x38",         "subs r0, #2"),
    (b"\x80\x1e",         "subs r0, r0, #2"),
    (b"\x88\x1e",         "subs r0, r1, #2"),
    (b"\x88\x1a",         "subs r0, r1, r2"),
    (b"\xb1\xeb\xa2\x00", "subs r0, r1, r2, asr #2"),
    (b"\xb1\xeb\x82\x00", "subs r0, r1, r2, lsl #2"),
    (b"\xb1\xeb\x92\x00", "subs r0, r1, r2, lsr #2"),
    (b"\xb1\xeb\xb2\x00", "subs r0, r1, r2, ror #2"),
    (b"\xb1\xeb\x32\x00", "subs r0, r1, r2, rrx"),
]

def emu_with_unicorn(opcode, istate):
    # Initialize emulator in arm32 mode
    mu = Uc(UC_ARCH_ARM, UC_MODE_THUMB)

    # map memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    apsr = mu.reg_read(UC_ARM_REG_APSR)
    nzcv = istate['n'] << 31 | istate['z'] << 30 | istate['c'] << 29 | istate['v'] << 28

    mu.mem_write(STACK,                bytes(istate['stack']))
    mu.mem_write(HEAP,                 bytes(istate['heap']))
    mu.reg_write(UC_ARM_REG_R0,        istate['r0'])
    mu.reg_write(UC_ARM_REG_R1,        istate['r1'])
    mu.reg_write(UC_ARM_REG_R2,        istate['r2'])
    mu.reg_write(UC_ARM_REG_R3,        istate['r3'])
    mu.reg_write(UC_ARM_REG_R4,        istate['r4'])
    mu.reg_write(UC_ARM_REG_R5,        istate['r5'])
    mu.reg_write(UC_ARM_REG_R6,        istate['r6'])
    mu.reg_write(UC_ARM_REG_R7,        istate['r7'])
    mu.reg_write(UC_ARM_REG_R8,        istate['r8'])
    mu.reg_write(UC_ARM_REG_R9,        istate['r9'])
    mu.reg_write(UC_ARM_REG_R10,       istate['r10'])
    mu.reg_write(UC_ARM_REG_R11,       istate['r11'])
    mu.reg_write(UC_ARM_REG_R12,       istate['r12'])
    mu.reg_write(UC_ARM_REG_SP,        istate['sp'])
    mu.reg_write(UC_ARM_REG_R14,       istate['r14'])
    mu.reg_write(UC_ARM_REG_PC,        istate['pc'])
    mu.reg_write(UC_ARM_REG_APSR,      apsr & 0x0fffffff | nzcv)

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(istate['pc'] | 1, istate['pc'] + len(opcode) + 2, count=1)

    ostate = {
        "stack": mu.mem_read(STACK, 0x100),
        "heap":  mu.mem_read(HEAP, 0x100),
        "r0":    mu.reg_read(UC_ARM_REG_R0),
        "r1":    mu.reg_read(UC_ARM_REG_R1),
        "r2":    mu.reg_read(UC_ARM_REG_R2),
        "r3":    mu.reg_read(UC_ARM_REG_R3),
        "r4":    mu.reg_read(UC_ARM_REG_R4),
        "r5":    mu.reg_read(UC_ARM_REG_R5),
        "r6":    mu.reg_read(UC_ARM_REG_R6),
        "r7":    mu.reg_read(UC_ARM_REG_R7),
        "r8":    mu.reg_read(UC_ARM_REG_R8),
        "r9":    mu.reg_read(UC_ARM_REG_R9),
        "r10":   mu.reg_read(UC_ARM_REG_R10),
        "r11":   mu.reg_read(UC_ARM_REG_R11),
        "r12":   mu.reg_read(UC_ARM_REG_R12),
        "sp":    mu.reg_read(UC_ARM_REG_SP),
        "r14":   mu.reg_read(UC_ARM_REG_R14),
        "pc":    mu.reg_read(UC_ARM_REG_PC),
        "n":   ((mu.reg_read(UC_ARM_REG_APSR) >> 31) & 1),
        "z":   ((mu.reg_read(UC_ARM_REG_APSR) >> 30) & 1),
        "c":   ((mu.reg_read(UC_ARM_REG_APSR) >> 29) & 1),
        "v":   ((mu.reg_read(UC_ARM_REG_APSR) >> 28) & 1),
    }
    return ostate

def emu_with_triton(opcode, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.ARM32)

    inst = Instruction(opcode)
    inst.setAddress(istate['pc'])

    ctx.setConcreteMemoryAreaValue(STACK,           bytes(istate['stack']))
    ctx.setConcreteMemoryAreaValue(HEAP,            bytes(istate['heap']))
    ctx.setConcreteRegisterValue(ctx.registers.r0,  istate['r0'])
    ctx.setConcreteRegisterValue(ctx.registers.r1,  istate['r1'])
    ctx.setConcreteRegisterValue(ctx.registers.r2,  istate['r2'])
    ctx.setConcreteRegisterValue(ctx.registers.r3,  istate['r3'])
    ctx.setConcreteRegisterValue(ctx.registers.r4,  istate['r4'])
    ctx.setConcreteRegisterValue(ctx.registers.r5,  istate['r5'])
    ctx.setConcreteRegisterValue(ctx.registers.r6,  istate['r6'])
    ctx.setConcreteRegisterValue(ctx.registers.r7,  istate['r7'])
    ctx.setConcreteRegisterValue(ctx.registers.r8,  istate['r8'])
    ctx.setConcreteRegisterValue(ctx.registers.r9,  istate['r9'])
    ctx.setConcreteRegisterValue(ctx.registers.r10, istate['r10'])
    ctx.setConcreteRegisterValue(ctx.registers.r11, istate['r11'])
    ctx.setConcreteRegisterValue(ctx.registers.r12, istate['r12'])
    ctx.setConcreteRegisterValue(ctx.registers.sp,  istate['sp'])
    ctx.setConcreteRegisterValue(ctx.registers.r14, istate['r14'])
    ctx.setConcreteRegisterValue(ctx.registers.pc,  istate['pc'] | 1) # NOTE: Enable Thumb mode by setting lsb of PC.
    ctx.setConcreteRegisterValue(ctx.registers.n,   istate['n'])
    ctx.setConcreteRegisterValue(ctx.registers.z,   istate['z'])
    ctx.setConcreteRegisterValue(ctx.registers.c,   istate['c'])
    ctx.setConcreteRegisterValue(ctx.registers.v,   istate['v'])

    ctx.processing(inst)

    # print()
    # print(inst)
    # for x in inst.getSymbolicExpressions():
    #    print(x)
    # print()

    ostate = {
        "stack": ctx.getConcreteMemoryAreaValue(STACK, 0x100),
        "heap":  ctx.getConcreteMemoryAreaValue(HEAP, 0x100),
        "r0":    ctx.getSymbolicRegisterValue(ctx.registers.r0),
        "r1":    ctx.getSymbolicRegisterValue(ctx.registers.r1),
        "r2":    ctx.getSymbolicRegisterValue(ctx.registers.r2),
        "r3":    ctx.getSymbolicRegisterValue(ctx.registers.r3),
        "r4":    ctx.getSymbolicRegisterValue(ctx.registers.r4),
        "r5":    ctx.getSymbolicRegisterValue(ctx.registers.r5),
        "r6":    ctx.getSymbolicRegisterValue(ctx.registers.r6),
        "r7":    ctx.getSymbolicRegisterValue(ctx.registers.r7),
        "r8":    ctx.getSymbolicRegisterValue(ctx.registers.r8),
        "r9":    ctx.getSymbolicRegisterValue(ctx.registers.r9),
        "r10":   ctx.getSymbolicRegisterValue(ctx.registers.r10),
        "r11":   ctx.getSymbolicRegisterValue(ctx.registers.r11),
        "r12":   ctx.getSymbolicRegisterValue(ctx.registers.r12),
        "sp":    ctx.getSymbolicRegisterValue(ctx.registers.sp),
        "r14":   ctx.getSymbolicRegisterValue(ctx.registers.r14),
        "pc":    ctx.getSymbolicRegisterValue(ctx.registers.pc),
        "n":     ctx.getSymbolicRegisterValue(ctx.registers.n),
        "z":     ctx.getSymbolicRegisterValue(ctx.registers.z),
        "c":     ctx.getSymbolicRegisterValue(ctx.registers.c),
        "v":     ctx.getSymbolicRegisterValue(ctx.registers.v),
    }
    return ostate

def diff_state(state1, state2):
    for k, v in list(state1.items()):
        if (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: (UC) != (TT)' %(k))
        elif not (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: %#x (UC) != %#x (TT)' %(k, v, state2[k]))
    return

def print_state(istate, uc_ostate, tt_ostate):
    for k in sorted(istate.keys()):
        if k in ['stack', 'heap']:
            continue

        diff = "!=" if uc_ostate[k] != tt_ostate[k] else "=="

        print("{:>3s}: {:08x} | {:08x} {} {:08x}".format(k, istate[k], uc_ostate[k], diff, tt_ostate[k]))


if __name__ == '__main__':
    # initial state
    state = {
        "stack": b"".join([bytes(255 - i) for i in range(256)]),
        "heap":  b"".join([bytes(i) for i in range(256)]),
        "r0":    random.randint(0x0, 0xffffffff),
        "r1":    random.randint(0x0, 0xffffffff),
        "r2":    random.randint(0x0, 0xffffffff),
        "r3":    random.randint(0x0, 0xffffffff),
        "r4":    random.randint(0x0, 0xffffffff),
        "r5":    random.randint(0x0, 0xffffffff),
        "r6":    random.randint(0x0, 0xffffffff),
        "r7":    random.randint(0x0, 0xffffffff),
        "r8":    random.randint(0x0, 0xffffffff),
        "r9":    random.randint(0x0, 0xffffffff),
        "r10":   random.randint(0x0, 0xffffffff),
        "r11":   random.randint(0x0, 0xffffffff),
        "r12":   random.randint(0x0, 0xffffffff),
        "sp":    STACK,
        "r14":   random.randint(0x0, 0xffffffff),
        "pc":    ADDR,
        "n":     random.randint(0x0, 0x1),
        "z":     random.randint(0x0, 0x1),
        "c":     random.randint(0x0, 0x1),
        "v":     random.randint(0x0, 0x1),
    }

    # NOTE: This tests each instruction separatly. Therefore, it keeps track of
    # PC and resets the initial state after testing each instruction.
    pc = ADDR
    for opcode, disassembly in CODE:
        try:
            state['pc'] = pc
            uc_state = emu_with_unicorn(opcode, state)
            tt_state = emu_with_triton(opcode, state)
            pc += len(opcode)
        except Exception as e:
            print('[KO] %s' %(disassembly))
            print('\t%s' %(e))
            sys.exit(-1)

        if uc_state != tt_state:
            print('[KO] %s' %(disassembly))
            diff_state(uc_state, tt_state)
            print_state(state, uc_state, tt_state)
            sys.exit(-1)

        print('[OK] %s' %(disassembly))

    sys.exit(0)
