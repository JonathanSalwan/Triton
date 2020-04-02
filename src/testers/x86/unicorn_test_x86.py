#!/usr/bin/env python
## -*- coding: utf-8 -*-

from __future__        import print_function

from triton            import *
from unicorn           import *
from unicorn.x86_const import *
from struct            import pack

import sys
import pprint

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024

CODE  = [
    (b"\x48\xb8\xaf\xbe\xad\xde\xaf\xbe\xad\xde",   "mov rax, 0xdeadbeafdeadbeaf"),
    (b"\x48\xff\xc0",                               "inc rax"),
    (b"\x48\xc7\xc3\x00\x00\x20\x00",               "mov rbx, 0x200000"),
    (b"\x0f\x28\x0b",                               "movaps xmm1, [rbx]"),
    (b"\x66\x0f\x3a\x14\xc8\x00",                   "pextrb eax, xmm1, 0"),
    (b"\x66\x0f\x3a\x14\xc8\x01",                   "pextrb eax, xmm1, 1"),
    (b"\x66\x0f\x3a\x14\xc8\x02",                   "pextrb eax, xmm1, 2"),
    (b"\x66\x0f\x3a\x14\xc8\x03",                   "pextrb eax, xmm1, 3"),
    (b"\x66\x0f\x3a\x14\xc8\x04",                   "pextrb eax, xmm1, 4"),
    (b"\x66\x0f\x3a\x14\xc8\x05",                   "pextrb eax, xmm1, 5"),
    (b"\x66\x0f\x3a\x14\xc8\x06",                   "pextrb eax, xmm1, 6"),
    (b"\x66\x0f\x3a\x14\xc8\x07",                   "pextrb eax, xmm1, 8"),
    (b"\x66\x0f\x3a\x14\xc8\x08",                   "pextrb eax, xmm1, 9"),
    (b"\x66\x0f\x3a\x14\xc8\x09",                   "pextrb eax, xmm1, 10"),
    (b"\x66\x0f\x3a\x14\xc8\x0a",                   "pextrb eax, xmm1, 11"),
    (b"\x66\x0f\x3a\x14\xc8\x0b",                   "pextrb eax, xmm1, 12"),
    (b"\x66\x0f\x3a\x14\xc8\x0c",                   "pextrb eax, xmm1, 13"),
    (b"\x66\x0f\x3a\x14\xc8\x0d",                   "pextrb eax, xmm1, 14"),
    (b"\x66\x0f\x3a\x14\xc8\x0e",                   "pextrb eax, xmm1, 15"),
    (b"\x66\x0f\x3a\x14\xc8\x0f",                   "pextrb eax, xmm1, 16"),
    (b"\x66\x0f\x3a\x14\xc8\x10",                   "pextrb eax, xmm1, 17"),
    (b"\x66\x0f\x3a\x14\xc8\x11",                   "pextrb eax, xmm1, 18"),
    (b"\x66\x0f\x3a\x14\xc8\x12",                   "pextrb eax, xmm1, 19"),
    (b"\x66\x0f\x3a\x14\xc8\x13",                   "pextrb eax, xmm1, 20"),
    (b"\x66\x0f\x3a\x14\xc8\x14",                   "pextrb eax, xmm1, 21"),
    (b"\x66\x0f\x3a\x14\xc8\x15",                   "pextrb eax, xmm1, 22"),
    (b"\x66\x0f\x3a\x14\xc8\x16",                   "pextrb eax, xmm1, 23"),
    (b"\x66\x0f\x3a\x14\xc8\x17",                   "pextrb eax, xmm1, 24"),
    (b"\x66\x0f\x3a\x14\xc8\x18",                   "pextrb eax, xmm1, 25"),
    (b"\x66\x0f\x3a\x14\xc8\x19",                   "pextrb eax, xmm1, 26"),
    (b"\x66\x0f\x3a\x14\xc8\x1a",                   "pextrb eax, xmm1, 27"),
    (b"\x66\x0f\x3a\x14\xc8\x1b",                   "pextrb eax, xmm1, 28"),
    (b"\x66\x0f\x3a\x14\xc8\x1c",                   "pextrb eax, xmm1, 29"),
    (b"\x66\x0f\x3a\x14\xc8\x1d",                   "pextrb eax, xmm1, 30"),
    (b"\x66\x0f\x3a\x14\xc8\x1e",                   "pextrb eax, xmm1, 31"),
    (b"\x66\x0f\x3a\x14\xc8\x1f",                   "pextrb eax, xmm1, 32"),
    (b"\x66\x0f\x3a\x14\xc8\x20",                   "pextrb eax, xmm1, 33"),
    (b"\xc4\xe3\x79\x14\xc8\x00",                   "vpextrb eax, xmm1, 0"),
    (b"\xc4\xe3\x79\x14\xc8\x01",                   "vpextrb eax, xmm1, 1"),
    (b"\xc4\xe3\x79\x14\xc8\x02",                   "vpextrb eax, xmm1, 2"),
    (b"\xc4\xe3\x79\x14\xc8\x03",                   "vpextrb eax, xmm1, 3"),
    (b"\xc4\xe3\x79\x14\xc8\x04",                   "vpextrb eax, xmm1, 4"),
    (b"\xc4\xe3\x79\x14\xc8\x05",                   "vpextrb eax, xmm1, 5"),
    (b"\xc4\xe3\x79\x14\xc8\x06",                   "vpextrb eax, xmm1, 6"),
    (b"\xc4\xe3\x79\x14\xc8\x07",                   "vpextrb eax, xmm1, 8"),
    (b"\xc4\xe3\x79\x14\xc8\x08",                   "vpextrb eax, xmm1, 9"),
    (b"\xc4\xe3\x79\x14\xc8\x09",                   "vpextrb eax, xmm1, 10"),
    (b"\xc4\xe3\x79\x14\xc8\x0a",                   "vpextrb eax, xmm1, 11"),
    (b"\xc4\xe3\x79\x14\xc8\x0b",                   "vpextrb eax, xmm1, 12"),
    (b"\xc4\xe3\x79\x14\xc8\x0c",                   "vpextrb eax, xmm1, 13"),
    (b"\xc4\xe3\x79\x14\xc8\x0d",                   "vpextrb eax, xmm1, 14"),
    (b"\xc4\xe3\x79\x14\xc8\x0e",                   "vpextrb eax, xmm1, 15"),
    (b"\xc4\xe3\x79\x14\xc8\x0f",                   "vpextrb eax, xmm1, 16"),
    (b"\xc4\xe3\x79\x14\xc8\x10",                   "vpextrb eax, xmm1, 17"),
    (b"\xc4\xe3\x79\x14\xc8\x11",                   "vpextrb eax, xmm1, 18"),
    (b"\xc4\xe3\x79\x14\xc8\x12",                   "vpextrb eax, xmm1, 19"),
    (b"\xc4\xe3\x79\x14\xc8\x13",                   "vpextrb eax, xmm1, 20"),
    (b"\xc4\xe3\x79\x14\xc8\x14",                   "vpextrb eax, xmm1, 21"),
    (b"\xc4\xe3\x79\x14\xc8\x15",                   "vpextrb eax, xmm1, 22"),
    (b"\xc4\xe3\x79\x14\xc8\x16",                   "vpextrb eax, xmm1, 23"),
    (b"\xc4\xe3\x79\x14\xc8\x17",                   "vpextrb eax, xmm1, 24"),
    (b"\xc4\xe3\x79\x14\xc8\x18",                   "vpextrb eax, xmm1, 25"),
    (b"\xc4\xe3\x79\x14\xc8\x19",                   "vpextrb eax, xmm1, 26"),
    (b"\xc4\xe3\x79\x14\xc8\x1a",                   "vpextrb eax, xmm1, 27"),
    (b"\xc4\xe3\x79\x14\xc8\x1b",                   "vpextrb eax, xmm1, 28"),
    (b"\xc4\xe3\x79\x14\xc8\x1c",                   "vpextrb eax, xmm1, 29"),
    (b"\xc4\xe3\x79\x14\xc8\x1d",                   "vpextrb eax, xmm1, 30"),
    (b"\xc4\xe3\x79\x14\xc8\x1e",                   "vpextrb eax, xmm1, 31"),
    (b"\xc4\xe3\x79\x14\xc8\x1f",                   "vpextrb eax, xmm1, 32"),
    (b"\xc4\xe3\x79\x14\xc8\x20",                   "vpextrb eax, xmm1, 33"),
]


def emu_with_unicorn(opcode, istate):
    # Initialize emulator in x86_64 mode
    mu = Uc(UC_ARCH_X86, UC_MODE_64)

    # map memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    mu.mem_write(STACK,             bytes(istate['stack']))
    mu.mem_write(HEAP,              bytes(istate['heap']))
    mu.reg_write(UC_X86_REG_EFLAGS, istate['eflags'])
    mu.reg_write(UC_X86_REG_RAX,    istate['rax'])
    mu.reg_write(UC_X86_REG_RBX,    istate['rbx'])
    mu.reg_write(UC_X86_REG_RCX,    istate['rcx'])
    mu.reg_write(UC_X86_REG_RDX,    istate['rdx'])
    mu.reg_write(UC_X86_REG_RSI,    istate['rsi'])
    mu.reg_write(UC_X86_REG_RDI,    istate['rdi'])
    mu.reg_write(UC_X86_REG_RIP,    istate['rip'])
    mu.reg_write(UC_X86_REG_RSP,    istate['rsp'])
    mu.reg_write(UC_X86_REG_RBP,    istate['rbp'])
    mu.reg_write(UC_X86_REG_R8,     istate['r8'])
    mu.reg_write(UC_X86_REG_R9,     istate['r9'])
    mu.reg_write(UC_X86_REG_R10,    istate['r10'])
    mu.reg_write(UC_X86_REG_R11,    istate['r11'])
    mu.reg_write(UC_X86_REG_R12,    istate['r12'])
    mu.reg_write(UC_X86_REG_R13,    istate['r13'])
    mu.reg_write(UC_X86_REG_R14,    istate['r14'])
    mu.reg_write(UC_X86_REG_R15,    istate['r15'])
    mu.reg_write(UC_X86_REG_XMM0,   istate['xmm0'])
    mu.reg_write(UC_X86_REG_XMM1,   istate['xmm1'])
    mu.reg_write(UC_X86_REG_XMM2,   istate['xmm2'])
    mu.reg_write(UC_X86_REG_XMM3,   istate['xmm3'])
    mu.reg_write(UC_X86_REG_XMM4,   istate['xmm4'])
    mu.reg_write(UC_X86_REG_XMM5,   istate['xmm5'])
    mu.reg_write(UC_X86_REG_XMM6,   istate['xmm6'])
    mu.reg_write(UC_X86_REG_XMM7,   istate['xmm7'])
    mu.reg_write(UC_X86_REG_XMM8,   istate['xmm8'])
    mu.reg_write(UC_X86_REG_XMM9,   istate['xmm9'])

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(istate['rip'], istate['rip'] + len(opcode))

    ostate = {
        "stack":   mu.mem_read(STACK, 0x100),
        "heap":    mu.mem_read(HEAP, 0x100),
        "eflags":  mu.reg_read(UC_X86_REG_EFLAGS),
        "rax":     mu.reg_read(UC_X86_REG_RAX),
        "rbx":     mu.reg_read(UC_X86_REG_RBX),
        "rcx":     mu.reg_read(UC_X86_REG_RCX),
        "rdx":     mu.reg_read(UC_X86_REG_RDX),
        "rsi":     mu.reg_read(UC_X86_REG_RSI),
        "rdi":     mu.reg_read(UC_X86_REG_RDI),
        "rip":     mu.reg_read(UC_X86_REG_RIP),
        "rsp":     mu.reg_read(UC_X86_REG_RSP),
        "rbp":     mu.reg_read(UC_X86_REG_RBP),
        "r8":      mu.reg_read(UC_X86_REG_R8),
        "r9":      mu.reg_read(UC_X86_REG_R9),
        "r10":     mu.reg_read(UC_X86_REG_R10),
        "r11":     mu.reg_read(UC_X86_REG_R11),
        "r12":     mu.reg_read(UC_X86_REG_R12),
        "r13":     mu.reg_read(UC_X86_REG_R13),
        "r14":     mu.reg_read(UC_X86_REG_R14),
        "r15":     mu.reg_read(UC_X86_REG_R15),
        "xmm0":    mu.reg_read(UC_X86_REG_XMM0),
        "xmm1":    mu.reg_read(UC_X86_REG_XMM1),
        "xmm2":    mu.reg_read(UC_X86_REG_XMM2),
        "xmm3":    mu.reg_read(UC_X86_REG_XMM3),
        "xmm4":    mu.reg_read(UC_X86_REG_XMM4),
        "xmm5":    mu.reg_read(UC_X86_REG_XMM5),
        "xmm6":    mu.reg_read(UC_X86_REG_XMM6),
        "xmm7":    mu.reg_read(UC_X86_REG_XMM7),
        "xmm8":    mu.reg_read(UC_X86_REG_XMM8),
        "xmm9":    mu.reg_read(UC_X86_REG_XMM9),
    }
    return ostate


def emu_with_triton(opcode, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.X86_64)

    inst = Instruction(opcode)
    inst.setAddress(istate['rip'])

    ctx.setConcreteMemoryAreaValue(STACK,               bytes(istate['stack']))
    ctx.setConcreteMemoryAreaValue(HEAP,                bytes(istate['heap']))
    ctx.setConcreteRegisterValue(ctx.registers.eflags,  istate['eflags'])
    ctx.setConcreteRegisterValue(ctx.registers.rax,     istate['rax'])
    ctx.setConcreteRegisterValue(ctx.registers.rbx,     istate['rbx'])
    ctx.setConcreteRegisterValue(ctx.registers.rcx,     istate['rcx'])
    ctx.setConcreteRegisterValue(ctx.registers.rdx,     istate['rdx'])
    ctx.setConcreteRegisterValue(ctx.registers.rsi,     istate['rsi'])
    ctx.setConcreteRegisterValue(ctx.registers.rdi,     istate['rdi'])
    ctx.setConcreteRegisterValue(ctx.registers.rip,     istate['rip'])
    ctx.setConcreteRegisterValue(ctx.registers.rsp,     istate['rsp'])
    ctx.setConcreteRegisterValue(ctx.registers.rbp,     istate['rbp'])
    ctx.setConcreteRegisterValue(ctx.registers.r8,      istate['r8'])
    ctx.setConcreteRegisterValue(ctx.registers.r9,      istate['r9'])
    ctx.setConcreteRegisterValue(ctx.registers.r10,     istate['r10'])
    ctx.setConcreteRegisterValue(ctx.registers.r11,     istate['r11'])
    ctx.setConcreteRegisterValue(ctx.registers.r12,     istate['r12'])
    ctx.setConcreteRegisterValue(ctx.registers.r13,     istate['r13'])
    ctx.setConcreteRegisterValue(ctx.registers.r14,     istate['r14'])
    ctx.setConcreteRegisterValue(ctx.registers.r15,     istate['r15'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm0,    istate['xmm0'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm1,    istate['xmm1'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm2,    istate['xmm2'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm3,    istate['xmm3'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm4,    istate['xmm4'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm5,    istate['xmm5'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm6,    istate['xmm6'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm7,    istate['xmm7'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm8,    istate['xmm8'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm9,    istate['xmm9'])

    ctx.processing(inst)
    #print(inst)
    #for se in inst.getSymbolicExpressions():
    #    print(se)

    ostate = {
        "stack":  ctx.getConcreteMemoryAreaValue(STACK, 0x100),
        "heap":   ctx.getConcreteMemoryAreaValue(HEAP, 0x100),
        "rax":    ctx.getSymbolicRegisterValue(ctx.registers.rax),
        "rbx":    ctx.getSymbolicRegisterValue(ctx.registers.rbx),
        "rcx":    ctx.getSymbolicRegisterValue(ctx.registers.rcx),
        "rdx":    ctx.getSymbolicRegisterValue(ctx.registers.rdx),
        "rsi":    ctx.getSymbolicRegisterValue(ctx.registers.rsi),
        "rdi":    ctx.getSymbolicRegisterValue(ctx.registers.rdi),
        "rip":    ctx.getSymbolicRegisterValue(ctx.registers.rip),
        "rsp":    ctx.getSymbolicRegisterValue(ctx.registers.rsp),
        "rbp":    ctx.getSymbolicRegisterValue(ctx.registers.rbp),
        "r8":     ctx.getSymbolicRegisterValue(ctx.registers.r8),
        "r9":     ctx.getSymbolicRegisterValue(ctx.registers.r9),
        "r10":    ctx.getSymbolicRegisterValue(ctx.registers.r10),
        "r11":    ctx.getSymbolicRegisterValue(ctx.registers.r11),
        "r12":    ctx.getSymbolicRegisterValue(ctx.registers.r12),
        "r13":    ctx.getSymbolicRegisterValue(ctx.registers.r13),
        "r14":    ctx.getSymbolicRegisterValue(ctx.registers.r14),
        "r15":    ctx.getSymbolicRegisterValue(ctx.registers.r15),
        "xmm0":   ctx.getSymbolicRegisterValue(ctx.registers.xmm0),
        "xmm1":   ctx.getSymbolicRegisterValue(ctx.registers.xmm1),
        "xmm2":   ctx.getSymbolicRegisterValue(ctx.registers.xmm2),
        "xmm3":   ctx.getSymbolicRegisterValue(ctx.registers.xmm3),
        "xmm4":   ctx.getSymbolicRegisterValue(ctx.registers.xmm4),
        "xmm5":   ctx.getSymbolicRegisterValue(ctx.registers.xmm5),
        "xmm6":   ctx.getSymbolicRegisterValue(ctx.registers.xmm6),
        "xmm7":   ctx.getSymbolicRegisterValue(ctx.registers.xmm7),
        "xmm8":   ctx.getSymbolicRegisterValue(ctx.registers.xmm8),
        "xmm9":   ctx.getSymbolicRegisterValue(ctx.registers.xmm9),
        "eflags": ctx.getConcreteRegisterValue(ctx.registers.eflags)
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
        "stack":    bytearray(b"".join([pack('B', 255 - i) for i in range(256)])),
        "heap":     bytearray(b"".join([pack('B', i) for i in range(256)])),
        "eflags":   2, # bit 2 is always 1
        "rax":      0,
        "rbx":      0,
        "rcx":      0,
        "rdx":      0,
        "rsi":      0,
        "rdi":      0,
        "rip":      ADDR,
        "rsp":      STACK,
        "rbp":      STACK,
        "r8":       0,
        "r9":       0,
        "r10":      0,
        "r11":      0,
        "r12":      0,
        "r13":      0,
        "r14":      0,
        "r15":      0,
        "xmm0":     0,
        "xmm1":     0,
        "xmm2":     0,
        "xmm3":     0,
        "xmm4":     0,
        "xmm5":     0,
        "xmm6":     0,
        "xmm7":     0,
        "xmm8":     0,
        "xmm9":     0,
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
