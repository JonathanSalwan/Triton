#!/usr/bin/env python3
## -*- coding: utf-8 -*-

from __future__        import print_function

from triton            import *
from unicorn           import *
from unicorn.x86_const import *
from struct            import pack

import sys

ADDR  = 0x100000
STACK = 0x200000
HEAP  = 0x300000
SIZE  = 5 * 1024 * 1024

CODE = [
    ({"eax": 0xa5a50ffa, "eflags": 0x12}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a5fffa, "eflags": 0x02}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a5ff04, "eflags": 0x12}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),

    ({"eax": 0xa5a50000, "eflags": 0x8c7}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a51239, "eflags": 0x03}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a512f9, "eflags": 0x02}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),

    ({"eax": 0xa5a51204, "eflags": 0x12}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a512f9, "eflags": 0x12}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a512fa, "eflags": 0x02}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),

    ({"eax": 0xa5a50ffa, "eflags": 0x02}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a51204, "eflags": 0x03}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
    ({"eax": 0xa5a5ffff, "eflags": 0x8d7}, [REG.X86.OF, REG.X86.SF, REG.X86.ZF, REG.X86.PF], b"\x37", "aaa"),
]


def emu_with_unicorn(opcode, istate):
    # Initialize emulator in x86 mode
    mu = Uc(UC_ARCH_X86, UC_MODE_32)

    # map memory for this emulation
    mu.mem_map(ADDR, SIZE)

    # write machine code to be emulated to memory
    index = 0
    for _, _, op, _ in CODE:
        mu.mem_write(ADDR+index, op)
        index += len(op)

    mu.mem_write(STACK,             bytes(istate['stack']))
    mu.mem_write(HEAP,              bytes(istate['heap']))
    mu.reg_write(UC_X86_REG_EFLAGS, istate['eflags'])
    mu.reg_write(UC_X86_REG_EAX,    istate['eax'])
    mu.reg_write(UC_X86_REG_EBX,    istate['ebx'])
    mu.reg_write(UC_X86_REG_ECX,    istate['ecx'])
    mu.reg_write(UC_X86_REG_EDX,    istate['edx'])
    mu.reg_write(UC_X86_REG_ESI,    istate['esi'])
    mu.reg_write(UC_X86_REG_EDI,    istate['edi'])
    mu.reg_write(UC_X86_REG_EIP,    istate['eip'])
    mu.reg_write(UC_X86_REG_ESP,    istate['esp'])
    mu.reg_write(UC_X86_REG_EBP,    istate['ebp'])
    mu.reg_write(UC_X86_REG_XMM0,   istate['xmm0'])
    mu.reg_write(UC_X86_REG_XMM1,   istate['xmm1'])
    mu.reg_write(UC_X86_REG_XMM2,   istate['xmm2'])
    mu.reg_write(UC_X86_REG_XMM3,   istate['xmm3'])
    mu.reg_write(UC_X86_REG_XMM4,   istate['xmm4'])
    mu.reg_write(UC_X86_REG_XMM5,   istate['xmm5'])
    mu.reg_write(UC_X86_REG_XMM6,   istate['xmm6'])
    mu.reg_write(UC_X86_REG_XMM7,   istate['xmm7'])
    mu.reg_write(UC_X86_REG_MXCSR,  istate['mxcsr'])
    mu.reg_write(UC_X86_REG_FPCW,   istate['fcw'])
    mu.reg_write(UC_X86_REG_FPSW,   istate['fsw'])
    mu.reg_write(UC_X86_REG_FPTAG,  istate['ftw'])

    # emulate code in infinite time & unlimited instructions
    mu.emu_start(istate['eip'], istate['eip'] + len(opcode))

    ostate = {
        "stack":        mu.mem_read(STACK, 0x200),
        "heap":         mu.mem_read(HEAP, 0x200),
        "eflags":       mu.reg_read(UC_X86_REG_EFLAGS),
        "eax":          mu.reg_read(UC_X86_REG_EAX),
        "ebx":          mu.reg_read(UC_X86_REG_EBX),
        "ecx":          mu.reg_read(UC_X86_REG_ECX),
        "edx":          mu.reg_read(UC_X86_REG_EDX),
        "esi":          mu.reg_read(UC_X86_REG_ESI),
        "edi":          mu.reg_read(UC_X86_REG_EDI),
        "eip":          mu.reg_read(UC_X86_REG_EIP),
        "esp":          mu.reg_read(UC_X86_REG_ESP),
        "ebp":          mu.reg_read(UC_X86_REG_EBP),
        "xmm0":         mu.reg_read(UC_X86_REG_XMM0),
        "xmm1":         mu.reg_read(UC_X86_REG_XMM1),
        "xmm2":         mu.reg_read(UC_X86_REG_XMM2),
        "xmm3":         mu.reg_read(UC_X86_REG_XMM3),
        "xmm4":         mu.reg_read(UC_X86_REG_XMM4),
        "xmm5":         mu.reg_read(UC_X86_REG_XMM5),
        "xmm6":         mu.reg_read(UC_X86_REG_XMM6),
        "xmm7":         mu.reg_read(UC_X86_REG_XMM7),
        "mxcsr":        mu.reg_read(UC_X86_REG_MXCSR),
        "mxcsr_mask":   0xFFBF,  # Unsupported by Unicorn
        "fcw":          mu.reg_read(UC_X86_REG_FPCW),
        "fsw":          mu.reg_read(UC_X86_REG_FPSW),
        "ftw":          mu.reg_read(UC_X86_REG_FPTAG),
    }
    return ostate


def emu_with_triton(opcode, istate):
    ctx = TritonContext()
    ctx.setArchitecture(ARCH.X86)

    inst = Instruction(opcode)
    inst.setAddress(istate['eip'])

    ctx.setConcreteMemoryAreaValue(STACK,                    bytes(istate['stack']))
    ctx.setConcreteMemoryAreaValue(HEAP,                     bytes(istate['heap']))
    ctx.setConcreteRegisterValue(ctx.registers.eflags,       istate['eflags'])
    ctx.setConcreteRegisterValue(ctx.registers.eax,          istate['eax'])
    ctx.setConcreteRegisterValue(ctx.registers.ebx,          istate['ebx'])
    ctx.setConcreteRegisterValue(ctx.registers.ecx,          istate['ecx'])
    ctx.setConcreteRegisterValue(ctx.registers.edx,          istate['edx'])
    ctx.setConcreteRegisterValue(ctx.registers.esi,          istate['esi'])
    ctx.setConcreteRegisterValue(ctx.registers.edi,          istate['edi'])
    ctx.setConcreteRegisterValue(ctx.registers.eip,          istate['eip'])
    ctx.setConcreteRegisterValue(ctx.registers.esp,          istate['esp'])
    ctx.setConcreteRegisterValue(ctx.registers.ebp,          istate['ebp'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm0,         istate['xmm0'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm1,         istate['xmm1'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm2,         istate['xmm2'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm3,         istate['xmm3'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm4,         istate['xmm4'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm5,         istate['xmm5'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm6,         istate['xmm6'])
    ctx.setConcreteRegisterValue(ctx.registers.xmm7,         istate['xmm7'])
    ctx.setConcreteRegisterValue(ctx.registers.mxcsr,        istate['mxcsr'])
    ctx.setConcreteRegisterValue(ctx.registers.mxcsr_mask,   istate['mxcsr_mask'])
    ctx.setConcreteRegisterValue(ctx.registers.fcw,          istate['fcw'])
    ctx.setConcreteRegisterValue(ctx.registers.fsw,          istate['fsw'])
    ctx.setConcreteRegisterValue(ctx.registers.ftw,          istate['ftw'])

    ctx.processing(inst)
    # print(inst)
    # for se in inst.getSymbolicExpressions():
    #    print(se)

    ostate = {
        "stack":       ctx.getConcreteMemoryAreaValue(STACK, 0x200),
        "heap":        ctx.getConcreteMemoryAreaValue(HEAP, 0x200),
        "eflags":      ctx.getConcreteRegisterValue(ctx.registers.eflags),
        "eax":         ctx.getSymbolicRegisterValue(ctx.registers.eax),
        "ebx":         ctx.getSymbolicRegisterValue(ctx.registers.ebx),
        "ecx":         ctx.getSymbolicRegisterValue(ctx.registers.ecx),
        "edx":         ctx.getSymbolicRegisterValue(ctx.registers.edx),
        "esi":         ctx.getSymbolicRegisterValue(ctx.registers.esi),
        "edi":         ctx.getSymbolicRegisterValue(ctx.registers.edi),
        "eip":         ctx.getSymbolicRegisterValue(ctx.registers.eip),
        "esp":         ctx.getSymbolicRegisterValue(ctx.registers.esp),
        "ebp":         ctx.getSymbolicRegisterValue(ctx.registers.ebp),
        "xmm0":        ctx.getSymbolicRegisterValue(ctx.registers.xmm0),
        "xmm1":        ctx.getSymbolicRegisterValue(ctx.registers.xmm1),
        "xmm2":        ctx.getSymbolicRegisterValue(ctx.registers.xmm2),
        "xmm3":        ctx.getSymbolicRegisterValue(ctx.registers.xmm3),
        "xmm4":        ctx.getSymbolicRegisterValue(ctx.registers.xmm4),
        "xmm5":        ctx.getSymbolicRegisterValue(ctx.registers.xmm5),
        "xmm6":        ctx.getSymbolicRegisterValue(ctx.registers.xmm6),
        "xmm7":        ctx.getSymbolicRegisterValue(ctx.registers.xmm7),
        "mxcsr":       ctx.getSymbolicRegisterValue(ctx.registers.mxcsr),
        "mxcsr_mask":  ctx.getSymbolicRegisterValue(ctx.registers.mxcsr_mask),
        "fcw":         ctx.getSymbolicRegisterValue(ctx.registers.fcw),
        "fsw":         ctx.getSymbolicRegisterValue(ctx.registers.fsw),
        "ftw":         ctx.getSymbolicRegisterValue(ctx.registers.ftw),
    }
    return ostate


def diff_state(state1, state2):
    for k, v in list(state1.items()):
        if (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: (UC) != (TT)' %(k))
        elif not (k == 'heap' or k == 'stack') and v != state2[k]:
            print('\t%s: %#x (UC) != %#x (TT)' %(k, v, state2[k]))
    return


def dump_state(state):
    # Stack dump (16-byte boundary)
    print("stack:")
    for i, b in enumerate(state['stack']):
        if (i % 16) == 0:
            print("")
        print("%02X " % b, end='')
    print("\n")
    # Heap dump (16-byte boundary)
    print("heap:")
    for i, b in enumerate(state['heap']):
        if (i % 16) == 0:
            print("")
        print("%02X " % b, end='')
    print("\n")
    # EFLAGS register
    print("eflags: 0x%X" % state['eflags'])
    # GP registers
    print("eax: 0x%X" % state['eax'])
    print("ebx: 0x%X" % state['ebx'])
    print("ecx: 0x%X" % state['ecx'])
    print("edx: 0x%X" % state['edx'])
    print("esi: 0x%X" % state['esi'])
    print("edi: 0x%X" % state['edi'])
    print("eip: 0x%X" % state['eip'])
    print("esp: 0x%X" % state['esp'])
    print("ebp: 0x%X" % state['ebp'])
    # XMM registers
    print("xmm0: 0x%X" % state['xmm0'])
    print("xmm1: 0x%X" % state['xmm1'])
    print("xmm2: 0x%X" % state['xmm2'])
    print("xmm3: 0x%X" % state['xmm3'])
    print("xmm4: 0x%X" % state['xmm4'])
    print("xmm5: 0x%X" % state['xmm5'])
    print("xmm6: 0x%X" % state['xmm6'])
    print("xmm7: 0x%X" % state['xmm7'])
    # SSE and x87 FPU registers
    print("mxcsr: 0x%X" % state['mxcsr'])
    print("mxcsr_mask: 0x%X" % state['mxcsr_mask'])
    print("fcw: 0x%X" % state['fcw'])
    print("fsw: 0x%X" % state['fsw'])
    print("ftw: 0x%X" % state['ftw'])


if __name__ == '__main__':
    # initial state
    state = {
        "stack":      bytearray(b"".join([pack('B', 0) for i in range(512)])),
        "heap":       bytearray(b"".join([pack('B', i) for i in range(256)])),
        "eflags":     2,        # Bit 1 is always 1
        "eax":        0,
        "ebx":        0,
        "ecx":        0,
        "edx":        0,
        "esi":        0,
        "edi":        0,
        "eip":        ADDR,
        "esp":        STACK,
        "ebp":        STACK,
        "xmm0":       0x0,
        "xmm1":       0x0,
        "xmm2":       0x0,
        "xmm3":       0x0,
        "xmm4":       0x0,
        "xmm5":       0x0,
        "xmm6":       0x0,
        "xmm7":       0x0,
        "mxcsr":      0x1F80,   # Default value at program start
        "mxcsr_mask": 0xFFBF,   # Default value at program start
        "fcw":        0x027F,   # Default value at program start
        "fsw":        0x0000,   # Default value at program start
        "ftw":        0x5555    # Default value at program start
    }

    for st, undef, opcode, disassembly in CODE:
        if st is not None:
            state.update(st)
        try:
            #print("> Unicorn emulation: %s" % disassembly)
            uc_state = emu_with_unicorn(opcode, state)
            #print("> Triton emulation: %s" % disassembly)
            tt_state = emu_with_triton(opcode, state)
            #print("> Emulation done")
        except Exception as e:
            print('[KO] %s' %(disassembly))
            print('\t%s' %(e))
            sys.exit(-1)

        # We ignore flags that are tagged as undef.
        # To do that we set them in both TT and UC state.
        for reg in undef:
            if reg == REG.X86.OF:
                mask = 0x0800
            elif reg == REG.X86.SF:
                mask = 0x0080
            elif reg == REG.X86.ZF:
                mask = 0x0040
            elif reg == REG.X86.PF:
                mask = 0x0004
            else:
                raise ValueError('Unsupported undefined flag: %s' % reg)
            uc_state['eflags'] = uc_state['eflags'] | mask
            tt_state['eflags'] = tt_state['eflags'] | mask

        if uc_state != tt_state:
            print('[KO] %s' %(disassembly))
            #dump_state(uc_state)
            #dump_state(tt_state)
            diff_state(uc_state, tt_state)
            sys.exit(-1)

        print('[OK] %s' %(disassembly))
        state = tt_state

    sys.exit(0)
