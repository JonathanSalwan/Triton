#!/usr/bin/env python3
## -*- coding: utf-8 -*-

from __future__          import print_function
from triton              import *
from unicorn             import *
from unicorn.arm_const   import *

import pprint
import random
import struct
import sys

ADDR  = 0x000000
STACK = 0x100000
HEAP  = 0x200000
SIZE  = 5 * 1024 * 1024

CODE = [
    [
        (0x00, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
        (0x08, b"\x93\x4f\x82\xe1", "strex r4, r3, [r2]"),
    ],

    [
        (0x00, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
        (0x04, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x08, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x04, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x08, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xe1", "ldrex r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xe1", "strex r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x01", "ldrexeq r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x01", "strexeq r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x11", "ldrexne r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x11", "strexne r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x21", "ldrexcs r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x21", "strexcs r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x31", "ldrexcc r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x31", "strexcc r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x41", "ldrexmi r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x41", "strexmi r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x51", "ldrexpl r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x51", "strexpl r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x61", "ldrexvs r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x61", "strexvs r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x71", "ldrexvc r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x71", "strexvc r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x81", "ldrexhi r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x81", "strexhi r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\x91", "ldrexls r0, [r2]"),
        (0x04, b"\x91\x0f\x82\x91", "strexls r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xa1", "ldrexge r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xa1", "strexge r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xb1", "ldrexlt r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xb1", "strexlt r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xc1", "ldrexgt r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xc1", "strexgt r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xd1", "ldrexle r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xd1", "strexle r0, r1, [r2]"),
    ],

    [
        (0x00, b"\x9f\x0f\x92\xe1", "ldrexal r0, [r2]"),
        (0x04, b"\x91\x0f\x82\xe1", "strexal r0, r1, [r2]"),
    ],
]


def hook_code(mu, address, size, istate):
    opcode = mu.mem_read(address, size)
    cpsr = mu.reg_read(ARM_REG_CPSR)
    thumb = (cpsr >> 5) & 0x1

    md = Cs(CS_ARCH_ARM, CS_MODE_THUMB if thumb else CS_MODE_ARM)
    md.detail = True
    i = list(md.disasm(opcode, address))[0]
    disasm = "{} {}".format(i.mnemonic, i.op_str)
    opcode_str = " ".join(["%02x" % b for b in opcode])

    print("[UC] {}\t{:08x}: {}".format(opcode_str, address, disasm))


def emu_with_unicorn(test_code, start, stop, istate):
    # Initialize emulator in arm32 mode.
    mu = Uc(UC_ARCH_ARM, UC_MODE_ARM)

    # Map memory for this emulation.
    mu.mem_map(ADDR, SIZE)

    # Write machine code to be emulated to memory.
    index = 0
    for _, op, _ in test_code:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    # Retrieve APSR register value.
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

    # mu.hook_add(UC_HOOK_CODE, hook_code)

    # Emulate code from start to stop.
    try:
        mu.emu_start(start, stop)
    except UcError as e:
        print("[UC] Error: {}".format(e))

    ostate = {
        "stack": bytearray(mu.mem_read(STACK, 0x100)),
        "heap":  bytearray(mu.mem_read(HEAP, 0x100)),
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


def emu_with_triton(test_code, start, stop, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.ARM32)

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

    code = {}
    for addr, opcode, disasm in test_code:
        code[addr] = (opcode, disasm)

    addr = start & ~0x1
    while addr != stop:
        opcode, disasm = code[addr]

        inst = Instruction(opcode)

        inst.setAddress(addr)

        ctx.processing(inst)

        # print()
        # print(inst)
        # for x in inst.getSymbolicExpressions():
        #    print(x)
        # print()

        addr = ctx.getSymbolicRegisterValue(ctx.registers.pc)

    ostate = {
        "stack": bytearray(ctx.getConcreteMemoryAreaValue(STACK, 0x100)),
        "heap":  bytearray(ctx.getConcreteMemoryAreaValue(HEAP, 0x100)),
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


def diff_heap(istate, uc_ostate, tt_ostate):
    print("IN|UC|TT")
    for a, b, c in zip(istate['heap'], uc_ostate['heap'], tt_ostate['heap']):
        if a != b or a != c:
            print("{:02x}|{:02x}|{:02x}".format(a, b, c), sep=" ")


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
    start = 0x00 | 0    # Address of the first instruction.

    # Initial state.
    state = {
        "stack": bytearray([255 - i for i in range(256)]),
        "heap":  bytearray([i for i in range(256)]),
        "r0":    random.randint(0x0, 0xffffffff),
        "r1":    0xdeadbeef,
        "r2":    HEAP + 10 * 4,
        "r3":    0xcafecafe,
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
        "pc":    start,
        "n":     random.randint(0x0, 0x1),
        "z":     random.randint(0x0, 0x1),
        "c":     random.randint(0x0, 0x1),
        "v":     random.randint(0x0, 0x1),
    }


    for i, test_block in enumerate(CODE):
        stop = test_block[-1][0] + 0x4

        disassembly = f"test-block: #{i}"

        try:
            uc_state = emu_with_unicorn(test_block, start, stop, state)
            tt_state = emu_with_triton(test_block, start, stop, state)
            uc_state["pc"] = tt_state["pc"]
        except Exception as e:
            print('[KO] %s' %(disassembly))
            print('\t%s' %(e))
            sys.exit(-1)

        for a, b in zip(uc_state['heap'], tt_state['heap']):
            if a != b:
                print('[KO] %s (heap differs!)' %(disassembly))
                diff_heap(state, uc_state, tt_state)
                print_state(state, uc_state, tt_state)
                sys.exit(-1)

        if uc_state != tt_state:
            print('[KO] %s' %(disassembly))
            diff_state(uc_state, tt_state)
            print_state(state, uc_state, tt_state)
            sys.exit(-1)

        print('[OK] %s' %(disassembly))

    sys.exit(0)
