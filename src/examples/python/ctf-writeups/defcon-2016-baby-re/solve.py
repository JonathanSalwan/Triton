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

import sys
from triton import *

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



def load_dump(path):
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
    setConcreteRegisterValue(Register(REG.RAX,    regs['rax']))
    setConcreteRegisterValue(Register(REG.RBX,    regs['rbx']))
    setConcreteRegisterValue(Register(REG.RCX,    regs['rcx']))
    setConcreteRegisterValue(Register(REG.RDX,    regs['rdx']))
    setConcreteRegisterValue(Register(REG.RDI,    regs['rdi']))
    setConcreteRegisterValue(Register(REG.RSI,    regs['rsi']))
    setConcreteRegisterValue(Register(REG.RBP,    regs['rbp']))
    setConcreteRegisterValue(Register(REG.RSP,    regs['rsp']))
    setConcreteRegisterValue(Register(REG.RIP,    regs['rip']))
    setConcreteRegisterValue(Register(REG.R8,     regs['r8']))
    setConcreteRegisterValue(Register(REG.R9,     regs['r9']))
    setConcreteRegisterValue(Register(REG.R10,    regs['r10']))
    setConcreteRegisterValue(Register(REG.R11,    regs['r11']))
    setConcreteRegisterValue(Register(REG.R12,    regs['r12']))
    setConcreteRegisterValue(Register(REG.R13,    regs['r13']))
    setConcreteRegisterValue(Register(REG.R14,    regs['r14']))
    setConcreteRegisterValue(Register(REG.EFLAGS, regs['eflags']))

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


def symbolizeInputs():
    global variables

    # First argument of the CheckSolution() function.
    user_input = getConcreteRegisterValue(REG.RDI)

    # Inject concrete models into the memory
    setConcreteMemoryValue(MemoryAccess(user_input+0,  CPUSIZE.DWORD, variables[0x00]))
    setConcreteMemoryValue(MemoryAccess(user_input+4,  CPUSIZE.DWORD, variables[0x01]))
    setConcreteMemoryValue(MemoryAccess(user_input+8,  CPUSIZE.DWORD, variables[0x02]))
    setConcreteMemoryValue(MemoryAccess(user_input+12, CPUSIZE.DWORD, variables[0x03]))
    setConcreteMemoryValue(MemoryAccess(user_input+16, CPUSIZE.DWORD, variables[0x04]))
    setConcreteMemoryValue(MemoryAccess(user_input+20, CPUSIZE.DWORD, variables[0x05]))
    setConcreteMemoryValue(MemoryAccess(user_input+24, CPUSIZE.DWORD, variables[0x06]))
    setConcreteMemoryValue(MemoryAccess(user_input+28, CPUSIZE.DWORD, variables[0x07]))
    setConcreteMemoryValue(MemoryAccess(user_input+32, CPUSIZE.DWORD, variables[0x08]))
    setConcreteMemoryValue(MemoryAccess(user_input+36, CPUSIZE.DWORD, variables[0x09]))
    setConcreteMemoryValue(MemoryAccess(user_input+40, CPUSIZE.DWORD, variables[0x0a]))
    setConcreteMemoryValue(MemoryAccess(user_input+44, CPUSIZE.DWORD, variables[0x0b]))
    setConcreteMemoryValue(MemoryAccess(user_input+48, CPUSIZE.DWORD, variables[0x0c]))

    # Create symbolic variables.
    var01 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+0,  CPUSIZE.DWORD))
    var02 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+4,  CPUSIZE.DWORD))
    var03 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+8,  CPUSIZE.DWORD))
    var04 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+12, CPUSIZE.DWORD))
    var05 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+16, CPUSIZE.DWORD))
    var06 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+20, CPUSIZE.DWORD))
    var07 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+24, CPUSIZE.DWORD))
    var08 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+28, CPUSIZE.DWORD))
    var09 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+32, CPUSIZE.DWORD))
    var10 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+36, CPUSIZE.DWORD))
    var11 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+40, CPUSIZE.DWORD))
    var12 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+44, CPUSIZE.DWORD))
    var13 = convertMemoryToSymbolicVariable(MemoryAccess(user_input+48, CPUSIZE.DWORD))

    return


# Print the final solution.
def solution():
    global variables
    print '[+] Final solution:'
    for k, v in variables.items():
        print '[+] Symbolic variable %d = %02x (%c)' %(k, v, chr(v))
    return


# Emulate the CheckSolution() function.
def emulate(pc):
    global variables
    global goodBranches

    print '[+] Starting emulation.'
    while pc:
        # Fetch opcodes
        opcodes = getConcreteMemoryAreaValue(pc, 16)

        # Create the Triton instruction
        instruction = Instruction()
        instruction.setOpcodes(opcodes)
        instruction.setAddress(pc)

        # Process
        processing(instruction)
        print instruction

        # End of the CheckSolution() function
        if pc == 0x4025E6:
            break

        if pc == 0x4025CC:
            print '[+] Win'
            break

        if pc in goodBranches:
            # Slice expressions
            rax   = getSymbolicExpressionFromId(getSymbolicRegisterId(REG.RAX))
            eax   = ast.extract(31, 0, rax.getAst())

            # Define constraint
            cstr  = ast.assert_(
                        ast.land(
                            getPathConstraintsAst(),
                            ast.equal(eax, ast.bv(goodBranches[pc], 32))
                        )
                    )

            print '[+] Asking for a model, please wait...'
            model = getModel(cstr)

            # Save new state
            for k, v in model.items():
                print '[+]', v
                variables[k] = v.getValue()

            # Go deeper
            del goodBranches[pc]

            # Restart emulation with a good input.
            initialize()

        # Next
        pc = getConcreteRegisterValue(REG.RIP)

    print '[+] Emulation done.'
    return


# Memory caching on the fly to speed up the dump loading.
def memoryCaching(mem):
    global memoryCache

    addr = mem.getAddress()
    size = mem.getSize()
    for index in range(size):
        if not isMemoryMapped(addr+index):
            for r in memoryCache:
                if addr+index >= r['start'] and addr+index < r['start'] + r['size']:
                    value = ord(r['memory'][((addr+index)-r['start'])])
                    setConcreteMemoryValue(addr+index, value)
                    return

    return


# Constant folding simplification.
def constantFolding(node):
    if node.isSymbolized():
        return node
    return ast.bv(node.evaluate(), node.getBitvectorSize())


def initialize():
    # Define the target architecture
    setArchitecture(ARCH.X86_64)

    # Define symbolic optimizations
    enableMode(MODE.ALIGNED_MEMORY, True)
    enableMode(MODE.ONLY_ON_SYMBOLIZED, True)

    # Define internal callbacks.
    addCallback(memoryCaching,   CALLBACK.GET_CONCRETE_MEMORY_VALUE)
    addCallback(constantFolding, CALLBACK.SYMBOLIC_SIMPLIFICATION)

    # Load the meory dump
    load_dump("./baby-re.dump")

    # Symbolize user inputs
    symbolizeInputs()

    return


if __name__ == '__main__':
    # Initialize symbolic emulation
    initialize()

    # Emulate from the dump
    emulate(getConcreteRegisterValue(REG.RIP))

    # Print the final solution
    solution()

    sys.exit(0)
