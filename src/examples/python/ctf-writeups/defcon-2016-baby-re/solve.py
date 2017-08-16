#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Jonathan Salwan - 2016-08-01
##
##  Description: Solution of the baby-re challenge from the Defcon Quals 2016.
##  In this solution, we fully emulate the CheckSolution() function and we solve
##  each branch to go through the good path. The emulation start from a memory
##  dump (baby-re.dump) which has been done via peda-gdb (see gdb-peda-fulldump.patch)
##  at the CheckSolution() prologue.
##
##  Output:
##
##   $ python ./solve.py
##   [...]
##   [+] Win
##   [+] Emulation done.
##   [+] Final solution:
##   [+] Symbolic variable 0 = 4d (M)
##   [+] Symbolic variable 1 = 61 (a)
##   [+] Symbolic variable 2 = 74 (t)
##   [+] Symbolic variable 3 = 68 (h)
##   [+] Symbolic variable 4 = 20 ( )
##   [+] Symbolic variable 5 = 69 (i)
##   [+] Symbolic variable 6 = 73 (s)
##   [+] Symbolic variable 7 = 20 ( )
##   [+] Symbolic variable 8 = 68 (h)
##   [+] Symbolic variable 9 = 61 (a)
##   [+] Symbolic variable 10 = 72 (r)
##   [+] Symbolic variable 11 = 64 (d)
##   [+] Symbolic variable 12 = 21 (!)
##

import os
import sys
from triton import ARCH, TritonContext, MemoryAccess, CPUSIZE, Instruction, MODE, CALLBACK

# Symbolic variables with random inputs at the first iteration.
variables = {
    0x00: 61,
    0x01: 61,
    0x02: 61,
    0x03: 61,
    0x04: 61,
    0x05: 61,
    0x06: 61,
    0x07: 61,
    0x08: 61,
    0x09: 61,
    0x0a: 61,
    0x0b: 61,
    0x0c: 61,
}

# Good values at specific points to take good branches.
goodBranches = {
    0x40168C: 0x01468753,
    0x4017D4: 0x00162F30,
    0x401920: 0xFFB2939C,
    0x401A6B: 0xFFAC90E3,
    0x401BB7: 0x0076D288,
    0x401D06: 0xFF78BF99,
    0x401E52: 0xFFF496E3,
    0x401FA0: 0xFF525E90,
    0x4020E8: 0xFFFD7704,
    0x402234: 0x00897CBB,
    0x402378: 0xFFC05F9F,
    0x402499: 0x003E4761,
    0x4025BA: 0x001B4945,
}

# Memory caching on the fly to speed up the dump loading.
memoryCache = list()



def load_dump(Triton, path):
    global memoryCache

    # Open the dump
    fd = open(path)
    data = eval(fd.read())
    fd.close()

    # Extract registers and memory
    regs = data[0]
    mems = data[1]

    # Load registers and memory into the libTriton
    print '[+] Define registers'
    Triton.setConcreteRegisterValue(Triton.registers.rax,    regs['rax'])
    Triton.setConcreteRegisterValue(Triton.registers.rbx,    regs['rbx'])
    Triton.setConcreteRegisterValue(Triton.registers.rcx,    regs['rcx'])
    Triton.setConcreteRegisterValue(Triton.registers.rdx,    regs['rdx'])
    Triton.setConcreteRegisterValue(Triton.registers.rdi,    regs['rdi'])
    Triton.setConcreteRegisterValue(Triton.registers.rsi,    regs['rsi'])
    Triton.setConcreteRegisterValue(Triton.registers.rbp,    regs['rbp'])
    Triton.setConcreteRegisterValue(Triton.registers.rsp,    regs['rsp'])
    Triton.setConcreteRegisterValue(Triton.registers.rip,    regs['rip'])
    Triton.setConcreteRegisterValue(Triton.registers.r8,     regs['r8'])
    Triton.setConcreteRegisterValue(Triton.registers.r9,     regs['r9'])
    Triton.setConcreteRegisterValue(Triton.registers.r10,    regs['r10'])
    Triton.setConcreteRegisterValue(Triton.registers.r11,    regs['r11'])
    Triton.setConcreteRegisterValue(Triton.registers.r12,    regs['r12'])
    Triton.setConcreteRegisterValue(Triton.registers.r13,    regs['r13'])
    Triton.setConcreteRegisterValue(Triton.registers.r14,    regs['r14'])
    Triton.setConcreteRegisterValue(Triton.registers.eflags, regs['eflags'])

    print '[+] Define memory areas'
    for mem in mems:
        start = mem['start']
        end   = mem['end']
        print '[+] Memory caching %x-%x' %(start, end)
        if mem['memory']:
            memoryCache.append({
                'start':  start,
                'size':   end - start,
                'memory': mem['memory'],
            })

    return


def symbolizeInputs(Triton):
    global variables

    # First argument of the CheckSolution() function.
    user_input = Triton.getConcreteRegisterValue(Triton.registers.rdi)

    # Inject concrete models into the memory
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+0,  CPUSIZE.DWORD), variables[0x00])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+4,  CPUSIZE.DWORD), variables[0x01])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+8,  CPUSIZE.DWORD), variables[0x02])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+12, CPUSIZE.DWORD), variables[0x03])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+16, CPUSIZE.DWORD), variables[0x04])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+20, CPUSIZE.DWORD), variables[0x05])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+24, CPUSIZE.DWORD), variables[0x06])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+28, CPUSIZE.DWORD), variables[0x07])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+32, CPUSIZE.DWORD), variables[0x08])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+36, CPUSIZE.DWORD), variables[0x09])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+40, CPUSIZE.DWORD), variables[0x0a])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+44, CPUSIZE.DWORD), variables[0x0b])
    Triton.setConcreteMemoryValue(MemoryAccess(user_input+48, CPUSIZE.DWORD), variables[0x0c])

    # Create symbolic variables.
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+0,  CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+4,  CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+8,  CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+12, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+16, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+20, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+24, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+28, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+32, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+36, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+40, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+44, CPUSIZE.DWORD))
    Triton.convertMemoryToSymbolicVariable(MemoryAccess(user_input+48, CPUSIZE.DWORD))

    return


# Print the final solution.
def solution():
    global variables
    print '[+] Final solution:'
    for k, v in variables.items():
        print '[+] Symbolic variable %d = %02x (%c)' %(k, v, chr(v))
    return


# Emulate the CheckSolution() function.
def emulate(Triton, pc):
    global variables
    global goodBranches

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

        # End of the CheckSolution() function
        if pc == 0x4025E6:
            break

        if pc == 0x4025CC:
            print '[+] Win'
            break

        if pc in goodBranches:

            astCtxt = Triton.getAstContext()

            # Slice expressions
            rax   = Triton.getSymbolicExpressionFromId(Triton.getSymbolicRegisterId(Triton.registers.rax))
            eax   = astCtxt.extract(31, 0, rax.getAst())

            # Define constraint
            cstr  = astCtxt.land([
                        Triton.getPathConstraintsAst(),
                        astCtxt.equal(eax, astCtxt.bv(goodBranches[pc], 32))
                    ])

            print '[+] Asking for a model, please wait...'
            model = Triton.getModel(cstr)

            # Save new state
            for k, v in model.items():
                print '[+]', v
                variables[k] = v.getValue()

            # Go deeper
            del goodBranches[pc]

            # Restart emulation with a good input.
            Triton = initialize()

        # Next
        pc = Triton.getConcreteRegisterValue(Triton.registers.rip)

    print '[+] Emulation done.'
    return


# Memory caching on the fly to speed up the dump loading.
def memoryCaching(Triton, mem):
    global memoryCache

    addr = mem.getAddress()
    size = mem.getSize()
    for index in range(size):
        if not Triton.isMemoryMapped(addr+index):
            for r in memoryCache:
                if addr+index >= r['start'] and addr+index < r['start'] + r['size']:
                    value = ord(r['memory'][((addr+index)-r['start'])])
                    Triton.setConcreteMemoryValue(addr+index, value)
                    return

    return


# Constant folding simplification.
def constantFolding(Triton, node):
    if node.isSymbolized():
        return node
    return Triton.getAstContext().bv(node.evaluate(), node.getBitvectorSize())


def initialize():

    Triton = TritonContext()
    # Define the target architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Define symbolic optimizations
    Triton.enableMode(MODE.ALIGNED_MEMORY, True)
    Triton.enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Define internal callbacks.
    Triton.addCallback(memoryCaching,   CALLBACK.GET_CONCRETE_MEMORY_VALUE)
    Triton.addCallback(constantFolding, CALLBACK.SYMBOLIC_SIMPLIFICATION)

    # Load the meory dump
    load_dump(Triton, os.path.join(os.path.dirname(__file__), "baby-re.dump"))

    # Symbolize user inputs
    symbolizeInputs(Triton)

    return Triton


if __name__ == '__main__':
    # Initialize symbolic emulation
    Triton = initialize()

    # Emulate from the dump
    emulate(Triton, Triton.getConcreteRegisterValue(Triton.registers.rip))

    # Print the final solution
    solution()

    sys.exit(0)
