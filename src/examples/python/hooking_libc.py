#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ python ./src/examples/python/hooking_libc.py
##  [+] Loading 0x400040 - 0x400270
##  [+] Loading 0x400270 - 0x40028c
##  [+] Loading 0x400000 - 0x4007a4
##  [+] Loading 0x600e10 - 0x601048
##  [+] Loading 0x600e28 - 0x600ff8
##  [+] Loading 0x40028c - 0x4002ac
##  [+] Loading 0x400678 - 0x4006ac
##  [+] Loading 0x000000 - 0x000000
##  [+] Loading 0x600e10 - 0x601000
##  [+] Loading 0x000000 - 0x000000
##  [+] Hooking strlen
##  [+] Hooking printf
##  [+] Hooking __libc_start_main
##  [+] Starting emulation.
##  4004a0: xor ebp, ebp
##  4004a2: mov r9, rdx
##  4004a5: pop rsi
##  4004a6: mov rdx, rsp
##  4004a9: and rsp, 0xfffffffffffffff0
##  4004ad: push rax
##  4004ae: push rsp
##  4004af: mov r8, 0x400650
##  4004b6: mov rcx, 0x4005e0
##  4004bd: mov rdi, 0x400596
##  4004c4: call 0x400480
##  400480: jmp qword ptr [rip + 0x200ba2]
##  [+] __libc_start_main hooked
##  400596: push rbp
##  400597: mov rbp, rsp
##  40059a: sub rsp, 0x10
##  40059e: mov dword ptr [rbp - 4], edi
##  4005a1: mov qword ptr [rbp - 0x10], rsi
##  4005a5: cmp dword ptr [rbp - 4], 2
##  4005a9: je 0x4005b2
##  4005b2: mov rax, qword ptr [rbp - 0x10]
##  4005b6: add rax, 8
##  4005ba: mov rax, qword ptr [rax]
##  4005bd: mov rdi, rax
##  4005c0: call 0x400460
##  400460: jmp qword ptr [rip + 0x200bb2]
##  [+] Strlen hooked
##  4005c5: mov rsi, rax
##  4005c8: mov edi, 0x400664
##  4005cd: mov eax, 0
##  4005d2: call 0x400470
##  400470: jmp qword ptr [rip + 0x200baa]
##  [+] printf hooked
##  Input size = 12
##  4005d7: mov eax, 0
##  4005dc: leave
##  4005dd: ret
##  4004c9: hlt
##  [+] Emulation done
##

import os
import sys
import string

from triton import TritonContext, ARCH, CPUSIZE, MemoryAccess, OPCODE, Instruction

Triton = TritonContext()


def getMemoryString(addr):
    s = str()
    index = 0

    while Triton.getConcreteMemoryValue(addr+index):
        c = chr(Triton.getConcreteMemoryValue(addr+index))
        if c not in string.printable: c = ""
        s += c
        index  += 1

    return s


def getFormatString(addr):
    return getMemoryString(addr)                                                    \
           .replace("%s", "{}").replace("%d", "{:d}").replace("%#02x", "{:#02x}")   \
           .replace("%#x", "{:#x}").replace("%x", "{:x}").replace("%02X", "{:02x}") \
           .replace("%c", "{:c}").replace("%02x", "{:02x}").replace("%ld", "{:d}")  \
           .replace("%*s", "").replace("%lX", "{:x}").replace("%08x", "{:08x}")     \
           .replace("%u", "{:d}")                                                   \


# Simulate the strlen() function
def strlenHandler():
    print '[+] Strlen hooked'

    # Get arguments
    arg1 = getMemoryString(Triton.getConcreteRegisterValue(Triton.registers.rdi))

    # Return value
    return len(arg1)


# Simulate the printf() function
def printfHandler():
    print '[+] printf hooked'

    # Get arguments
    arg1   = getFormatString(Triton.getConcreteRegisterValue(Triton.registers.rdi))
    arg2   = Triton.getConcreteRegisterValue(Triton.registers.rsi)
    arg3   = Triton.getConcreteRegisterValue(Triton.registers.rdx)
    arg4   = Triton.getConcreteRegisterValue(Triton.registers.rcx)
    arg5   = Triton.getConcreteRegisterValue(Triton.registers.r8)
    arg6   = Triton.getConcreteRegisterValue(Triton.registers.r9)
    nbArgs = arg1.count("{")
    args   = [arg2, arg3, arg4, arg5, arg6][:nbArgs]
    s      = arg1.format(*args)

    sys.stdout.write(s)

    # Return value
    return len(s)


def libcMainHandler():
    print '[+] __libc_start_main hooked'

    # Get arguments
    main = Triton.getConcreteRegisterValue(Triton.registers.rdi)

    # Push the return value to jump into the main() function
    Triton.concretizeRegister(Triton.registers.rsp)
    Triton.setConcreteRegisterValue(Triton.registers.rsp, Triton.getConcreteRegisterValue(Triton.registers.rsp)-CPUSIZE.QWORD)

    ret2main = MemoryAccess(Triton.getConcreteRegisterValue(Triton.registers.rsp), CPUSIZE.QWORD)
    Triton.concretizeMemory(ret2main)
    Triton.setConcreteMemoryValue(ret2main, main)

    # Setup argc / argv
    Triton.concretizeRegister(Triton.registers.rdi)
    Triton.concretizeRegister(Triton.registers.rsi)

    argvs = [
        "sample_1",      # argv[0]
        "my_first_arg",  # argv[1]
    ]

    # Define argc / argv
    base  = 0x20000000
    addrs = list()

    for argv in argvs:
        addrs.append(base)
        Triton.setConcreteMemoryAreaValue(base, argv+'\x00')
        base += len(argv)+1

    argc = len(argvs)
    argv = base
    for addr in addrs:
        Triton.setConcreteMemoryValue(MemoryAccess(base, CPUSIZE.QWORD), addr)
        base += CPUSIZE.QWORD

    Triton.setConcreteRegisterValue(Triton.registers.rdi, argc)
    Triton.setConcreteRegisterValue(Triton.registers.rsi, argv)

    return 0


customRelocation = [
    ('strlen',            strlenHandler,   0x10000000),
    ('printf',            printfHandler,   0x10000001),
    ('__libc_start_main', libcMainHandler, 0x10000002),
]


def hookingHandler():
    pc = Triton.getConcreteRegisterValue(Triton.registers.rip)
    for rel in customRelocation:
        if rel[2] == pc:
            # Emulate the routine and the return value
            ret_value = rel[1]()
            Triton.concretizeRegister(Triton.registers.rax)
            Triton.setConcreteRegisterValue(Triton.registers.rax, ret_value)

            # Get the return address
            ret_addr = Triton.getConcreteMemoryValue(MemoryAccess(Triton.getConcreteRegisterValue(Triton.registers.rsp), CPUSIZE.QWORD))

            # Hijack RIP to skip the call
            Triton.concretizeRegister(Triton.registers.rip)
            Triton.setConcreteRegisterValue(Triton.registers.rip, ret_addr)

            # Restore RSP (simulate the ret)
            Triton.concretizeRegister(Triton.registers.rsp)
            Triton.setConcreteRegisterValue(Triton.registers.rsp, Triton.getConcreteRegisterValue(Triton.registers.rsp)+CPUSIZE.QWORD)
    return


# Emulate the CheckSolution() function.
def emulate(pc):
    print '[+] Starting emulation.'

    while pc:
        # Fetch opcode
        opcode = Triton.getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcode(opcode)
        instruction.setAddress(pc)

        # Process
        Triton.processing(instruction)
        print instruction

        if instruction.getType() == OPCODE.HLT:
            break

        # Simulate routines
        hookingHandler()

        # Next
        pc = Triton.getConcreteRegisterValue(Triton.registers.rip)

    print '[+] Emulation done.'
    return


def loadBinary(path):
    import lief
    binary = lief.parse(path)
    phdrs  = binary.segments
    for phdr in phdrs:
        size   = phdr.physical_size
        vaddr  = phdr.virtual_address
        print '[+] Loading 0x%06x - 0x%06x' %(vaddr, vaddr+size)
        Triton.setConcreteMemoryAreaValue(vaddr, phdr.content)
    return binary


def makeRelocation(binary):
    # Perform our own relocations
    for rel in binary.pltgot_relocations:
        symbolName = rel.symbol.name
        symbolRelo = rel.address
        for crel in customRelocation:
            if symbolName == crel[0]:
                print '[+] Hooking %s' %(symbolName)
                Triton.setConcreteMemoryValue(MemoryAccess(symbolRelo, CPUSIZE.QWORD), crel[2])
    return


if __name__ == '__main__':
    # Set the architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Load the binary
    binary = loadBinary(os.path.join(os.path.dirname(__file__), 'samples', 'sample_1'))

    # Perform our own relocations
    makeRelocation(binary)

    # Define a fake stack
    Triton.setConcreteRegisterValue(Triton.registers.rbp, 0x7fffffff)
    Triton.setConcreteRegisterValue(Triton.registers.rsp, 0x6fffffff)

    # Let's emulate the binary from the entry point
    emulate(binary.entrypoint)

    sys.exit(0)

