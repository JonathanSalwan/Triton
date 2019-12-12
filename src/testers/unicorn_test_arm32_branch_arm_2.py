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
ADDR2 = 0x300000
STACK = 0x500000
HEAP  = 0x600000
SIZE  = 10 * 1024 * 1024

TARGET = 0x200000

CODE2 = [
    (b"\x00\xbf", "nop"),           # Thumb
]

CODE  = [
    # B ---------------------------------------------------------------------- #
    (b"\xfe\xff\x07\x0a", "beq #0x200001"),
    (b"\xfe\xff\x07\x1a", "bne #0x200001"),
    (b"\xfe\xff\x07\x2a", "bcs #0x200001"),
    (b"\xfe\xff\x07\x3a", "bcc #0x200001"),
    (b"\xfe\xff\x07\x4a", "bmi #0x200001"),
    (b"\xfe\xff\x07\x5a", "bpl #0x200001"),
    (b"\xfe\xff\x07\x6a", "bvs #0x200001"),
    (b"\xfe\xff\x07\x7a", "bvc #0x200001"),
    (b"\xfe\xff\x07\x8a", "bhi #0x200001"),
    (b"\xfe\xff\x07\x9a", "bls #0x200001"),
    (b"\xfe\xff\x07\xaa", "bge #0x200001"),
    (b"\xfe\xff\x07\xba", "blt #0x200001"),
    (b"\xfe\xff\x07\xca", "bgt #0x200001"),
    (b"\xfe\xff\x07\xda", "ble #0x200001"),
    (b"\xfe\xff\x07\xea", "bal #0x200001"),

    # BL --------------------------------------------------------------------- #
    (b"\xfe\xff\x07\x0b", "bleq #0x200001"),
    (b"\xfe\xff\x07\x1b", "blne #0x200001"),
    (b"\xfe\xff\x07\x2b", "blcs #0x200001"),
    (b"\xfe\xff\x07\x3b", "blcc #0x200001"),
    (b"\xfe\xff\x07\x4b", "blmi #0x200001"),
    (b"\xfe\xff\x07\x5b", "blpl #0x200001"),
    (b"\xfe\xff\x07\x6b", "blvs #0x200001"),
    (b"\xfe\xff\x07\x7b", "blvc #0x200001"),
    (b"\xfe\xff\x07\x8b", "blhi #0x200001"),
    (b"\xfe\xff\x07\x9b", "blls #0x200001"),
    (b"\xfe\xff\x07\xab", "blge #0x200001"),
    (b"\xfe\xff\x07\xbb", "bllt #0x200001"),
    (b"\xfe\xff\x07\xcb", "blgt #0x200001"),
    (b"\xfe\xff\x07\xdb", "blle #0x200001"),
    (b"\xfe\xff\x07\xeb", "blal #0x200001"),

    # BLX -------------------------------------------------------------------- #
    (b"\xfe\xff\x07\xfa", "blxeq #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxne #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxcs #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxcc #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxmi #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxpl #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxvs #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxvc #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxhi #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxls #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxge #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxlt #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxgt #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxle #0x200001"),
    (b"\xfe\xff\x07\xfa", "blxal #0x200001"),

    (b"\x30\xff\x2f\x01", "blxeq r0"),
    (b"\x30\xff\x2f\x11", "blxne r0"),
    (b"\x30\xff\x2f\x21", "blxcs r0"),
    (b"\x30\xff\x2f\x31", "blxcc r0"),
    (b"\x30\xff\x2f\x41", "blxmi r0"),
    (b"\x30\xff\x2f\x51", "blxpl r0"),
    (b"\x30\xff\x2f\x61", "blxvs r0"),
    (b"\x30\xff\x2f\x71", "blxvc r0"),
    (b"\x30\xff\x2f\x81", "blxhi r0"),
    (b"\x30\xff\x2f\x91", "blxls r0"),
    (b"\x30\xff\x2f\xa1", "blxge r0"),
    (b"\x30\xff\x2f\xb1", "blxlt r0"),
    (b"\x30\xff\x2f\xc1", "blxgt r0"),
    (b"\x30\xff\x2f\xd1", "blxle r0"),
    (b"\x30\xff\x2f\xe1", "blxal r0"),

    (b"\x3d\xff\x2f\x01", "blxeq sp"),
    (b"\x3d\xff\x2f\x11", "blxne sp"),
    (b"\x3d\xff\x2f\x21", "blxcs sp"),
    (b"\x3d\xff\x2f\x31", "blxcc sp"),
    (b"\x3d\xff\x2f\x41", "blxmi sp"),
    (b"\x3d\xff\x2f\x51", "blxpl sp"),
    (b"\x3d\xff\x2f\x61", "blxvs sp"),
    (b"\x3d\xff\x2f\x71", "blxvc sp"),
    (b"\x3d\xff\x2f\x81", "blxhi sp"),
    (b"\x3d\xff\x2f\x91", "blxls sp"),
    (b"\x3d\xff\x2f\xa1", "blxge sp"),
    (b"\x3d\xff\x2f\xb1", "blxlt sp"),
    (b"\x3d\xff\x2f\xc1", "blxgt sp"),
    (b"\x3d\xff\x2f\xd1", "blxle sp"),
    (b"\x3d\xff\x2f\xe1", "blxal sp"),

    (b"\x3f\xff\x2f\x01", "blxeq pc"),
    (b"\x3f\xff\x2f\x11", "blxne pc"),
    (b"\x3f\xff\x2f\x21", "blxcs pc"),
    (b"\x3f\xff\x2f\x31", "blxcc pc"),
    (b"\x3f\xff\x2f\x41", "blxmi pc"),
    (b"\x3f\xff\x2f\x51", "blxpl pc"),
    (b"\x3f\xff\x2f\x61", "blxvs pc"),
    (b"\x3f\xff\x2f\x71", "blxvc pc"),
    (b"\x3f\xff\x2f\x81", "blxhi pc"),
    (b"\x3f\xff\x2f\x91", "blxls pc"),
    (b"\x3f\xff\x2f\xa1", "blxge pc"),
    (b"\x3f\xff\x2f\xb1", "blxlt pc"),
    (b"\x3f\xff\x2f\xc1", "blxgt pc"),
    (b"\x3f\xff\x2f\xd1", "blxle pc"),
    (b"\x3f\xff\x2f\xe1", "blxal pc"),

    # BX --------------------------------------------------------------------- #
    (b"\x10\xff\x2f\x01", "bxeq r0"),
    (b"\x10\xff\x2f\x11", "bxne r0"),
    (b"\x10\xff\x2f\x21", "bxcs r0"),
    (b"\x10\xff\x2f\x31", "bxcc r0"),
    (b"\x10\xff\x2f\x41", "bxmi r0"),
    (b"\x10\xff\x2f\x51", "bxpl r0"),
    (b"\x10\xff\x2f\x61", "bxvs r0"),
    (b"\x10\xff\x2f\x71", "bxvc r0"),
    (b"\x10\xff\x2f\x81", "bxhi r0"),
    (b"\x10\xff\x2f\x91", "bxls r0"),
    (b"\x10\xff\x2f\xa1", "bxge r0"),
    (b"\x10\xff\x2f\xb1", "bxlt r0"),
    (b"\x10\xff\x2f\xc1", "bxgt r0"),
    (b"\x10\xff\x2f\xd1", "bxle r0"),
    (b"\x10\xff\x2f\xe1", "bxal r0"),

    (b"\x1d\xff\x2f\x01", "bxeq sp"),
    (b"\x1d\xff\x2f\x11", "bxne sp"),
    (b"\x1d\xff\x2f\x21", "bxcs sp"),
    (b"\x1d\xff\x2f\x31", "bxcc sp"),
    (b"\x1d\xff\x2f\x41", "bxmi sp"),
    (b"\x1d\xff\x2f\x51", "bxpl sp"),
    (b"\x1d\xff\x2f\x61", "bxvs sp"),
    (b"\x1d\xff\x2f\x71", "bxvc sp"),
    (b"\x1d\xff\x2f\x81", "bxhi sp"),
    (b"\x1d\xff\x2f\x91", "bxls sp"),
    (b"\x1d\xff\x2f\xa1", "bxge sp"),
    (b"\x1d\xff\x2f\xb1", "bxlt sp"),
    (b"\x1d\xff\x2f\xc1", "bxgt sp"),
    (b"\x1d\xff\x2f\xd1", "bxle sp"),
    (b"\x1d\xff\x2f\xe1", "bxal sp"),

    (b"\x1f\xff\x2f\x01", "bxeq pc"),
    (b"\x1f\xff\x2f\x11", "bxne pc"),
    (b"\x1f\xff\x2f\x21", "bxcs pc"),
    (b"\x1f\xff\x2f\x31", "bxcc pc"),
    (b"\x1f\xff\x2f\x41", "bxmi pc"),
    (b"\x1f\xff\x2f\x51", "bxpl pc"),
    (b"\x1f\xff\x2f\x61", "bxvs pc"),
    (b"\x1f\xff\x2f\x71", "bxvc pc"),
    (b"\x1f\xff\x2f\x81", "bxhi pc"),
    (b"\x1f\xff\x2f\x91", "bxls pc"),
    (b"\x1f\xff\x2f\xa1", "bxge pc"),
    (b"\x1f\xff\x2f\xb1", "bxlt pc"),
    (b"\x1f\xff\x2f\xc1", "bxgt pc"),
    (b"\x1f\xff\x2f\xd1", "bxle pc"),
    (b"\x1f\xff\x2f\xe1", "bxal pc"),
]


def hook_code(mu, address, size, istate):
    print(">>> Tracing instruction at 0x%x, instruction size = 0x%x" %(address, size))

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

    # print_state(istate, istate, ostate)


def emu_with_unicorn(opcode, istate):
    # Initialize emulator in arm32 mode
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)

    # map memory for this emulation
    # print("[UC] Mapping memory from {:#x} to {:#x}".format(ADDR, ADDR + SIZE));
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    # Valid memory region to land when testing branches.
    index = 0
    for op, _ in CODE2:
        mu.mem_write(ADDR2+index, op)
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

    # tracing all instructions with customized callback
    # mu.hook_add(UC_HOOK_CODE, hook_code, user_data=istate)

    # emulate code in infinite time & unlimited instructions
    # print("[UC] Executing from {:#x} to {:#x}".format(istate['pc'], istate['pc'] + len(opcode)))
    mu.emu_start(istate['pc'], istate['pc'] + len(opcode), count=1)

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
        "r0":    TARGET | 0x1,
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
