#!/usr/bin/env python3
## -*- coding: utf-8 -*-

from __future__          import print_function
from triton              import *
from unicorn             import *
from unicorn.arm_const   import *

import pprint
import random
import sys

ADDR  = 0x000000
STACK = 0x100000
HEAP  = 0x200000
SIZE  = 5 * 1024 * 1024

# Switchs from Thumb to ARM and back.
IT_INSTRS = [
    # ITxyz EQ -------------------------------------------------------------- #
    (0x00, b"\x08\xbf", "it    eq"),
    (0x00, b"\x04\xbf", "itt   eq"),
    (0x00, b"\x0c\xbf", "ite   eq"),
    (0x00, b"\x02\xbf", "ittt  eq"),
    (0x00, b"\x0a\xbf", "itet  eq"),
    (0x00, b"\x06\xbf", "itte  eq"),
    (0x00, b"\x0e\xbf", "itee  eq"),
    (0x00, b"\x01\xbf", "itttt eq"),
    (0x00, b"\x09\xbf", "itett eq"),
    (0x00, b"\x05\xbf", "ittet eq"),
    (0x00, b"\x0d\xbf", "iteet eq"),
    (0x00, b"\x03\xbf", "ittte eq"),
    (0x00, b"\x0b\xbf", "itete eq"),
    (0x00, b"\x07\xbf", "ittee eq"),
    (0x00, b"\x0f\xbf", "iteee eq"),

    # ITxyz NE -------------------------------------------------------------- #
    (0x00, b"\x18\xbf", "it    ne"),
    (0x00, b"\x1c\xbf", "itt   ne"),
    (0x00, b"\x14\xbf", "ite   ne"),
    (0x00, b"\x1e\xbf", "ittt  ne"),
    (0x00, b"\x16\xbf", "itet  ne"),
    (0x00, b"\x1a\xbf", "itte  ne"),
    (0x00, b"\x12\xbf", "itee  ne"),
    (0x00, b"\x1f\xbf", "itttt ne"),
    (0x00, b"\x17\xbf", "itett ne"),
    (0x00, b"\x1b\xbf", "ittet ne"),
    (0x00, b"\x13\xbf", "iteet ne"),
    (0x00, b"\x1d\xbf", "ittte ne"),
    (0x00, b"\x15\xbf", "itete ne"),
    (0x00, b"\x19\xbf", "ittee ne"),
    (0x00, b"\x11\xbf", "iteee ne"),

    # ITxyz HS | CS ---------------------------------------------------------- #
    (0x00, b"\x28\xbf", "it    hs"),
    (0x00, b"\x24\xbf", "itt   hs"),
    (0x00, b"\x2c\xbf", "ite   hs"),
    (0x00, b"\x22\xbf", "ittt  hs"),
    (0x00, b"\x2a\xbf", "itet  hs"),
    (0x00, b"\x26\xbf", "itte  hs"),
    (0x00, b"\x2e\xbf", "itee  hs"),
    (0x00, b"\x21\xbf", "itttt hs"),
    (0x00, b"\x29\xbf", "itett hs"),
    (0x00, b"\x25\xbf", "ittet hs"),
    (0x00, b"\x2d\xbf", "iteet hs"),
    (0x00, b"\x23\xbf", "ittte hs"),
    (0x00, b"\x2b\xbf", "itete hs"),
    (0x00, b"\x27\xbf", "ittee hs"),
    (0x00, b"\x2f\xbf", "iteee hs"),

    (0x00, b"\x28\xbf", "it    cs"),
    (0x00, b"\x24\xbf", "itt   cs"),
    (0x00, b"\x2c\xbf", "ite   cs"),
    (0x00, b"\x22\xbf", "ittt  cs"),
    (0x00, b"\x2a\xbf", "itet  cs"),
    (0x00, b"\x26\xbf", "itte  cs"),
    (0x00, b"\x2e\xbf", "itee  cs"),
    (0x00, b"\x21\xbf", "itttt cs"),
    (0x00, b"\x29\xbf", "itett cs"),
    (0x00, b"\x25\xbf", "ittet cs"),
    (0x00, b"\x2d\xbf", "iteet cs"),
    (0x00, b"\x23\xbf", "ittte cs"),
    (0x00, b"\x2b\xbf", "itete cs"),
    (0x00, b"\x27\xbf", "ittee cs"),
    (0x00, b"\x2f\xbf", "iteee cs"),

    # ITxyz LO | CC ---------------------------------------------------------- #
    (0x00, b"\x38\xbf", "it    lo"),
    (0x00, b"\x3c\xbf", "itt   lo"),
    (0x00, b"\x34\xbf", "ite   lo"),
    (0x00, b"\x3e\xbf", "ittt  lo"),
    (0x00, b"\x36\xbf", "itet  lo"),
    (0x00, b"\x3a\xbf", "itte  lo"),
    (0x00, b"\x32\xbf", "itee  lo"),
    (0x00, b"\x3f\xbf", "itttt lo"),
    (0x00, b"\x37\xbf", "itett lo"),
    (0x00, b"\x3b\xbf", "ittet lo"),
    (0x00, b"\x33\xbf", "iteet lo"),
    (0x00, b"\x3d\xbf", "ittte lo"),
    (0x00, b"\x35\xbf", "itete lo"),
    (0x00, b"\x39\xbf", "ittee lo"),
    (0x00, b"\x31\xbf", "iteee lo"),

    (0x00, b"\x38\xbf", "it    cc"),
    (0x00, b"\x3c\xbf", "itt   cc"),
    (0x00, b"\x34\xbf", "ite   cc"),
    (0x00, b"\x3e\xbf", "ittt  cc"),
    (0x00, b"\x36\xbf", "itet  cc"),
    (0x00, b"\x3a\xbf", "itte  cc"),
    (0x00, b"\x32\xbf", "itee  cc"),
    (0x00, b"\x3f\xbf", "itttt cc"),
    (0x00, b"\x37\xbf", "itett cc"),
    (0x00, b"\x3b\xbf", "ittet cc"),
    (0x00, b"\x33\xbf", "iteet cc"),
    (0x00, b"\x3d\xbf", "ittte cc"),
    (0x00, b"\x35\xbf", "itete cc"),
    (0x00, b"\x39\xbf", "ittee cc"),
    (0x00, b"\x31\xbf", "iteee cc"),

    # ITxyz MI -------------------------------------------------------------- #
    (0x00, b"\x48\xbf", "it    mi"),
    (0x00, b"\x44\xbf", "itt   mi"),
    (0x00, b"\x4c\xbf", "ite   mi"),
    (0x00, b"\x42\xbf", "ittt  mi"),
    (0x00, b"\x4a\xbf", "itet  mi"),
    (0x00, b"\x46\xbf", "itte  mi"),
    (0x00, b"\x4e\xbf", "itee  mi"),
    (0x00, b"\x41\xbf", "itttt mi"),
    (0x00, b"\x49\xbf", "itett mi"),
    (0x00, b"\x45\xbf", "ittet mi"),
    (0x00, b"\x4d\xbf", "iteet mi"),
    (0x00, b"\x43\xbf", "ittte mi"),
    (0x00, b"\x4b\xbf", "itete mi"),
    (0x00, b"\x47\xbf", "ittee mi"),
    (0x00, b"\x4f\xbf", "iteee mi"),

    # ITxyz PL -------------------------------------------------------------- #
    (0x00, b"\x58\xbf", "it    pl"),
    (0x00, b"\x5c\xbf", "itt   pl"),
    (0x00, b"\x54\xbf", "ite   pl"),
    (0x00, b"\x5e\xbf", "ittt  pl"),
    (0x00, b"\x56\xbf", "itet  pl"),
    (0x00, b"\x5a\xbf", "itte  pl"),
    (0x00, b"\x52\xbf", "itee  pl"),
    (0x00, b"\x5f\xbf", "itttt pl"),
    (0x00, b"\x57\xbf", "itett pl"),
    (0x00, b"\x5b\xbf", "ittet pl"),
    (0x00, b"\x53\xbf", "iteet pl"),
    (0x00, b"\x5d\xbf", "ittte pl"),
    (0x00, b"\x55\xbf", "itete pl"),
    (0x00, b"\x59\xbf", "ittee pl"),
    (0x00, b"\x51\xbf", "iteee pl"),

    # ITxyz VS -------------------------------------------------------------- #
    (0x00, b"\x68\xbf", "it    vs"),
    (0x00, b"\x64\xbf", "itt   vs"),
    (0x00, b"\x6c\xbf", "ite   vs"),
    (0x00, b"\x62\xbf", "ittt  vs"),
    (0x00, b"\x6a\xbf", "itet  vs"),
    (0x00, b"\x66\xbf", "itte  vs"),
    (0x00, b"\x6e\xbf", "itee  vs"),
    (0x00, b"\x61\xbf", "itttt vs"),
    (0x00, b"\x69\xbf", "itett vs"),
    (0x00, b"\x65\xbf", "ittet vs"),
    (0x00, b"\x6d\xbf", "iteet vs"),
    (0x00, b"\x63\xbf", "ittte vs"),
    (0x00, b"\x6b\xbf", "itete vs"),
    (0x00, b"\x67\xbf", "ittee vs"),
    (0x00, b"\x6f\xbf", "iteee vs"),

    # ITxyz VC -------------------------------------------------------------- #
    (0x00, b"\x78\xbf", "it    vc"),
    (0x00, b"\x7c\xbf", "itt   vc"),
    (0x00, b"\x74\xbf", "ite   vc"),
    (0x00, b"\x7e\xbf", "ittt  vc"),
    (0x00, b"\x76\xbf", "itet  vc"),
    (0x00, b"\x7a\xbf", "itte  vc"),
    (0x00, b"\x72\xbf", "itee  vc"),
    (0x00, b"\x7f\xbf", "itttt vc"),
    (0x00, b"\x77\xbf", "itett vc"),
    (0x00, b"\x7b\xbf", "ittet vc"),
    (0x00, b"\x73\xbf", "iteet vc"),
    (0x00, b"\x7d\xbf", "ittte vc"),
    (0x00, b"\x75\xbf", "itete vc"),
    (0x00, b"\x79\xbf", "ittee vc"),
    (0x00, b"\x71\xbf", "iteee vc"),

    # ITxyz HI -------------------------------------------------------------- #
    (0x00, b"\x88\xbf", "it    hi"),
    (0x00, b"\x84\xbf", "itt   hi"),
    (0x00, b"\x8c\xbf", "ite   hi"),
    (0x00, b"\x82\xbf", "ittt  hi"),
    (0x00, b"\x8a\xbf", "itet  hi"),
    (0x00, b"\x86\xbf", "itte  hi"),
    (0x00, b"\x8e\xbf", "itee  hi"),
    (0x00, b"\x81\xbf", "itttt hi"),
    (0x00, b"\x89\xbf", "itett hi"),
    (0x00, b"\x85\xbf", "ittet hi"),
    (0x00, b"\x8d\xbf", "iteet hi"),
    (0x00, b"\x83\xbf", "ittte hi"),
    (0x00, b"\x8b\xbf", "itete hi"),
    (0x00, b"\x87\xbf", "ittee hi"),
    (0x00, b"\x8f\xbf", "iteee hi"),

    # ITxyz LS -------------------------------------------------------------- #
    (0x00, b"\x98\xbf", "it    ls"),
    (0x00, b"\x9c\xbf", "itt   ls"),
    (0x00, b"\x94\xbf", "ite   ls"),
    (0x00, b"\x9e\xbf", "ittt  ls"),
    (0x00, b"\x96\xbf", "itet  ls"),
    (0x00, b"\x9a\xbf", "itte  ls"),
    (0x00, b"\x92\xbf", "itee  ls"),
    (0x00, b"\x9f\xbf", "itttt ls"),
    (0x00, b"\x97\xbf", "itett ls"),
    (0x00, b"\x9b\xbf", "ittet ls"),
    (0x00, b"\x93\xbf", "iteet ls"),
    (0x00, b"\x9d\xbf", "ittte ls"),
    (0x00, b"\x95\xbf", "itete ls"),
    (0x00, b"\x99\xbf", "ittee ls"),
    (0x00, b"\x91\xbf", "iteee ls"),

    # ITxyz GE -------------------------------------------------------------- #
    (0x00, b"\xa8\xbf", "it    ge"),
    (0x00, b"\xa4\xbf", "itt   ge"),
    (0x00, b"\xac\xbf", "ite   ge"),
    (0x00, b"\xa2\xbf", "ittt  ge"),
    (0x00, b"\xaa\xbf", "itet  ge"),
    (0x00, b"\xa6\xbf", "itte  ge"),
    (0x00, b"\xae\xbf", "itee  ge"),
    (0x00, b"\xa1\xbf", "itttt ge"),
    (0x00, b"\xa9\xbf", "itett ge"),
    (0x00, b"\xa5\xbf", "ittet ge"),
    (0x00, b"\xad\xbf", "iteet ge"),
    (0x00, b"\xa3\xbf", "ittte ge"),
    (0x00, b"\xab\xbf", "itete ge"),
    (0x00, b"\xa7\xbf", "ittee ge"),
    (0x00, b"\xaf\xbf", "iteee ge"),

    # ITxyz LT -------------------------------------------------------------- #
    (0x00, b"\xb8\xbf", "it    lt"),
    (0x00, b"\xbc\xbf", "itt   lt"),
    (0x00, b"\xb4\xbf", "ite   lt"),
    (0x00, b"\xbe\xbf", "ittt  lt"),
    (0x00, b"\xb6\xbf", "itet  lt"),
    (0x00, b"\xba\xbf", "itte  lt"),
    (0x00, b"\xb2\xbf", "itee  lt"),
    (0x00, b"\xbf\xbf", "itttt lt"),
    (0x00, b"\xb7\xbf", "itett lt"),
    (0x00, b"\xbb\xbf", "ittet lt"),
    (0x00, b"\xb3\xbf", "iteet lt"),
    (0x00, b"\xbd\xbf", "ittte lt"),
    (0x00, b"\xb5\xbf", "itete lt"),
    (0x00, b"\xb9\xbf", "ittee lt"),
    (0x00, b"\xb1\xbf", "iteee lt"),

    # ITxyz GT -------------------------------------------------------------- #
    (0x00, b"\xc8\xbf", "it    gt"),
    (0x00, b"\xc4\xbf", "itt   gt"),
    (0x00, b"\xcc\xbf", "ite   gt"),
    (0x00, b"\xc2\xbf", "ittt  gt"),
    (0x00, b"\xca\xbf", "itet  gt"),
    (0x00, b"\xc6\xbf", "itte  gt"),
    (0x00, b"\xce\xbf", "itee  gt"),
    (0x00, b"\xc1\xbf", "itttt gt"),
    (0x00, b"\xc9\xbf", "itett gt"),
    (0x00, b"\xc5\xbf", "ittet gt"),
    (0x00, b"\xcd\xbf", "iteet gt"),
    (0x00, b"\xc3\xbf", "ittte gt"),
    (0x00, b"\xcb\xbf", "itete gt"),
    (0x00, b"\xc7\xbf", "ittee gt"),
    (0x00, b"\xcf\xbf", "iteee gt"),

    # ITxyz LE -------------------------------------------------------------- #
    (0x00, b"\xd8\xbf", "it    le"),
    (0x00, b"\xdc\xbf", "itt   le"),
    (0x00, b"\xd4\xbf", "ite   le"),
    (0x00, b"\xde\xbf", "ittt  le"),
    (0x00, b"\xd6\xbf", "itet  le"),
    (0x00, b"\xda\xbf", "itte  le"),
    (0x00, b"\xd2\xbf", "itee  le"),
    (0x00, b"\xdf\xbf", "itttt le"),
    (0x00, b"\xd7\xbf", "itett le"),
    (0x00, b"\xdb\xbf", "ittet le"),
    (0x00, b"\xd3\xbf", "iteet le"),
    (0x00, b"\xdd\xbf", "ittte le"),
    (0x00, b"\xd5\xbf", "itete le"),
    (0x00, b"\xd9\xbf", "ittee le"),
    (0x00, b"\xd1\xbf", "iteee le"),
]

CODE1 = [
    (0x02, b"\x4f\xf0\x01\x00", "mov   r0, 1"),
    (0x06, b"\x4f\xf0\x02\x01", "mov   r1, 2"),
    (0x0a, b"\x4f\xf0\x03\x02", "mov   r2, 3"),
    (0x0e, b"\x4f\xf0\x04\x03", "mov   r3, 4"),
    (0x12, b"\x4f\xf0\x05\x04", "mov   r4, 5"),
]

CODE2 = [
    (0x02, b"\x01\x20", "movs   r0, 1"),
    (0x04, b"\x02\x21", "movs   r1, 2"),
    (0x06, b"\x03\x22", "movs   r2, 3"),
    (0x08, b"\x04\x23", "movs   r3, 4"),
    (0x0a, b"\x05\x24", "movs   r4, 5"),
]

CODE3 = [
    (0x02, b"\x5f\xf0\xff\x30", "movs   r0, #-1"),
    (0x06, b"\x5f\xf0\xff\x31", "movs   r1, #-1"),
    (0x0a, b"\x5f\xf0\xff\x32", "movs   r2, #-1"),
    (0x0e, b"\x5f\xf0\xff\x33", "movs   r3, #-1"),
    (0x12, b"\x5f\xf0\xff\x34", "movs   r4, #-1"),
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
    start = 0x00 | 1    # Address of the first instruction.

    # Initial state.
    state = {
        "stack": bytearray([255 - i for i in range(256)]),
        "heap":  bytearray([i for i in range(256)]),
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
        "pc":    start,
        "n":     random.randint(0x0, 0x1),
        "z":     random.randint(0x0, 0x1),
        "c":     random.randint(0x0, 0x1),
        "v":     random.randint(0x0, 0x1),
    }

    for it_inst in IT_INSTRS:
        for code_block in [CODE1, CODE2, CODE3]:
            stop  = code_block[-1][0] + len(code_block[-1][1])  # Address of the last instruction + size.

            test_block = [it_inst] + code_block

            disassembly = it_inst[2]

            try:
                uc_state = emu_with_unicorn(test_block, start, stop, state)
                tt_state = emu_with_triton(test_block, start, stop, state)
                uc_state["pc"] = tt_state["pc"]
            except Exception as e:
                print('[KO] %s' %(disassembly))
                print('%s' %('\n'.join(['\t' + d for _, _, d in test_block])))
                print('\t%s' %(e))
                sys.exit(-1)

            if uc_state != tt_state:
                print('[KO] %s' %(disassembly))
                print('%s' %('\n'.join(['\t' + d for _, _, d in test_block])))
                diff_state(uc_state, tt_state)
                print_state(state, uc_state, tt_state)
                sys.exit(-1)

            print('[OK] %s' %(disassembly))

    sys.exit(0)
