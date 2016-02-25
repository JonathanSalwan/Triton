#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  $ ./triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor a
##  [+] 10 bytes tainted from the argv[1] (0x7ffd5dbe060e) pointer
##  loose
##  New path possible path with the input: [SymVar_0 = 65 (e)]
##
##  $ ./triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor e
##  [+] 10 bytes tainted from the argv[1] (0x7ffe20c4d60e) pointer
##  loose
##  New path possible path with the input: [SymVar_0 = 65 (e) and SymVar_1 = 6C (l)]
##
##  $ ./triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor el
##  [+] 10 bytes tainted from the argv[1] (0x7ffd1bc0d60d) pointer
##  loose
##  New path possible path with the input: [SymVar_0 = 65 (e) and SymVar_1 = 6C (l) and SymVar_2 = 69 (i)]
##
##  $ ./triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor eli
##  [+] 10 bytes tainted from the argv[1] (0x7ffc083e960c) pointer
##  loose
##  New path possible path with the input: [SymVar_0 = 65 (e) and SymVar_1 = 6C (l) and SymVar_2 = 69 (i) and SymVar_3 = 74 (t)]
##
##  [...]
##

from triton  import *
from ast     import *
from pintool import *

TAINTING_SIZE = 10



def tainting(threadId):
    rdi = getCurrentRegisterValue(REG.RDI) # argc
    rsi = getCurrentRegisterValue(REG.RSI) # argv

    while rdi > 1:
        argv = getCurrentMemoryValue(rsi + ((rdi-1) * CPUSIZE.REG), CPUSIZE.REG)
        offset = 0
        while offset != TAINTING_SIZE:
            taintMemory(argv + offset)
            convertMemoryToSymbolicVariable(Memory(argv + offset, CPUSIZE.BYTE))
            offset += 1
        print '[+] %02d bytes tainted from the argv[%d] (%#x) pointer' %(offset, rdi-1, argv)
        rdi -= 1

    return


def fini():
    pc = getPathConstraints()
    newInput = list()
    for c in pc:
        models = getModel(assert_(lnot(c)))
        for k, v in models.items():
            newInput.append('%s (%c)' %(str(v), chr(v.getValue())))
    print 'New path possible path with the input: [%s]' %(' and '.join(newInput))
    return


if __name__ == '__main__':
    # Define the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Align the memory
    enableSymbolicOptimization(OPTIMIZATION.ALIGNED_MEMORY, True)

    # Only perform the symbolic execution on the target binary
    setupImageWhitelist(['crackme_xor'])

    # Add callbacks
    addCallback(tainting, CALLBACK.ROUTINE_ENTRY, 'main')
    addCallback(fini,     CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()

