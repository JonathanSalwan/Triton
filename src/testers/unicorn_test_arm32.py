#!/usr/bin/env python2
## -*- coding: utf-8 -*-

from __future__          import print_function
from triton              import *
from unicorn             import *
from unicorn.arm_const   import *

import sys
import pprint

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024
CODE  = [
    # adc r1, #2
    # adc r1, r2
    # adc r1, r2, asr #4
    # adc r1, r2, lsl #4
    # adc r1, r2, lsr #4
    # adc r1, r2, ror #4
    # adc r1, r2, asr r3
    # adc r1, r2, lsl r3
    # adc r1, r2, lsr r3
    # adc r1, r2, ror r3
    # adc r0, r1, #2
    # adc r0, r1, r2
    # adc r0, r1, r2, asr #4
    # adc r0, r1, r2, lsl #4
    # adc r0, r1, r2, lsr #4
    # adc r0, r1, r2, ror #4
    # adc r0, r1, r2, asr r3
    # adc r0, r1, r2, lsl r3
    # adc r0, r1, r2, lsr r3
    # adc r0, r1, r2, ror r3
    # adceq r0, r1, #2
    # adcne r0, r1, #2
    # adccs r0, r1, #2
    # adccc r0, r1, #2
    # adcmi r0, r1, #2
    # adcpl r0, r1, #2
    # adcvs r0, r1, #2
    # adcvc r0, r1, #2
    # adchi r0, r1, #2
    # adcls r0, r1, #2
    # adcge r0, r1, #2
    # adclt r0, r1, #2
    # adcgt r0, r1, #2
    # adcle r0, r1, #2
    # adcal r0, r1, #2
    # adcs r0, r1, #2
    # adcs r0, r1, r2
    # adcs r0, r1, r2, asr #4
    # adcs r0, r1, r2, lsl #4
    # adcs r0, r1, r2, lsr #4
    # adcs r0, r1, r2, ror #4
    # adcs r0, r1, r2, asr r3
    # adcs r0, r1, r2, lsl r3
    # adcs r0, r1, r2, lsr r3
    # adcs r0, r1, r2, ror r3

    # (b"\x02\x10\xa1\xe2", "adc r1, #2"),
    (b"\x02\x10\xa1\xe0", "adc r1, r2"),
    (b"\x42\x12\xa1\xe0", "adc r1, r2, asr #4"),
    (b"\x02\x12\xa1\xe0", "adc r1, r2, lsl #4"),
    (b"\x22\x12\xa1\xe0", "adc r1, r2, lsr #4"),
    (b"\x62\x12\xa1\xe0", "adc r1, r2, ror #4"),
    (b"\x52\x13\xa1\xe0", "adc r1, r2, asr r3"),
    (b"\x12\x13\xa1\xe0", "adc r1, r2, lsl r3"),
    (b"\x32\x13\xa1\xe0", "adc r1, r2, lsr r3"),
    (b"\x72\x13\xa1\xe0", "adc r1, r2, ror r3"),
    (b"\x02\x00\xa1\xe2", "adc r0, r1, #2"),
    (b"\x02\x00\xa1\xe0", "adc r0, r1, r2"),
    (b"\x42\x02\xa1\xe0", "adc r0, r1, r2, asr #4"),
    (b"\x02\x02\xa1\xe0", "adc r0, r1, r2, lsl #4"),
    (b"\x22\x02\xa1\xe0", "adc r0, r1, r2, lsr #4"),
    (b"\x62\x02\xa1\xe0", "adc r0, r1, r2, ror #4"),
    (b"\x52\x03\xa1\xe0", "adc r0, r1, r2, asr r3"),
    (b"\x12\x03\xa1\xe0", "adc r0, r1, r2, lsl r3"),
    (b"\x32\x03\xa1\xe0", "adc r0, r1, r2, lsr r3"),
    (b"\x72\x03\xa1\xe0", "adc r0, r1, r2, ror r3"),
    (b"\x02\x00\xa1\x02", "adceq r0, r1, #2"),
    (b"\x02\x00\xa1\x12", "adcne r0, r1, #2"),
    (b"\x02\x00\xa1\x22", "adccs r0, r1, #2"),
    (b"\x02\x00\xa1\x32", "adccc r0, r1, #2"),
    (b"\x02\x00\xa1\x42", "adcmi r0, r1, #2"),
    (b"\x02\x00\xa1\x52", "adcpl r0, r1, #2"),
    (b"\x02\x00\xa1\x62", "adcvs r0, r1, #2"),
    (b"\x02\x00\xa1\x72", "adcvc r0, r1, #2"),
    (b"\x02\x00\xa1\x82", "adchi r0, r1, #2"),
    (b"\x02\x00\xa1\x92", "adcls r0, r1, #2"),
    (b"\x02\x00\xa1\xa2", "adcge r0, r1, #2"),
    (b"\x02\x00\xa1\xb2", "adclt r0, r1, #2"),
    (b"\x02\x00\xa1\xc2", "adcgt r0, r1, #2"),
    (b"\x02\x00\xa1\xd2", "adcle r0, r1, #2"),
    (b"\x02\x00\xa1\xe2", "adcal r0, r1, #2"),
    (b"\x02\x00\xb1\xe2", "adcs r0, r1, #2"),
    (b"\x02\x00\xb1\xe0", "adcs r0, r1, r2"),
    (b"\x42\x02\xb1\xe0", "adcs r0, r1, r2, asr #4"),
    (b"\x02\x02\xb1\xe0", "adcs r0, r1, r2, lsl #4"),
    (b"\x22\x02\xb1\xe0", "adcs r0, r1, r2, lsr #4"),
    (b"\x62\x02\xb1\xe0", "adcs r0, r1, r2, ror #4"),
    (b"\x52\x03\xb1\xe0", "adcs r0, r1, r2, asr r3"),
    (b"\x12\x03\xb1\xe0", "adcs r0, r1, r2, lsl r3"),
    (b"\x32\x03\xb1\xe0", "adcs r0, r1, r2, lsr r3"),
    (b"\x72\x03\xb1\xe0", "adcs r0, r1, r2, ror r3"),

    (b"\x04\x01\xa0\xe3", "mov r0, #0x4, #2"),
]

def emu_with_unicorn(opcode, istate):
    # Initialize emulator in arm32 mode
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)

    # map memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

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
    mu.reg_write(UC_ARM_REG_APSR_NZCV, istate['n'] << 31 | istate['z'] << 30 | istate['c'] << 29 | istate['v'] << 28)

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(istate['pc'], istate['pc'] + len(opcode))

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
        "n":   ((mu.reg_read(UC_ARM_REG_APSR_NZCV) >> 31) & 1),
        "z":   ((mu.reg_read(UC_ARM_REG_APSR_NZCV) >> 30) & 1),
        "c":   ((mu.reg_read(UC_ARM_REG_APSR_NZCV) >> 29) & 1),
        "v":   ((mu.reg_read(UC_ARM_REG_APSR_NZCV) >> 28) & 1),
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
    ctx.setConcreteRegisterValue(ctx.registers.pc,  istate['pc'])
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

if __name__ == '__main__':
    # initial state
    state = {
        "stack": b"".join([bytes(255 - i) for i in range(256)]),
        "heap":  b"".join([bytes(i) for i in range(256)]),
        "r0":    0,
        "r1":    0,
        "r2":    0,
        "r3":    0,
        "r4":    0,
        "r5":    0,
        "r6":    0,
        "r7":    0,
        "r8":    0,
        "r9":    0,
        "r10":   0,
        "r11":   0,
        "r12":   0,
        "sp":    STACK,
        "r14":   0,
        "pc":    ADDR,
        "n":     0,
        "z":     0,
        "c":     0,
        "v":     0,
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
