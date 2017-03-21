#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor a
##  [+] 10 bytes tainted from the argv[1] (0x7ffd4a50c60e) pointer
##  loose
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor e
##  [+] 10 bytes tainted from the argv[1] (0x7fff0b23160e) pointer
##  loose
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##  B1: SymVar_1 = 6C (l)  |  B2: SymVar_1 = 0 ()
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor el
##  [+] 10 bytes tainted from the argv[1] (0x7ffda0d4e60d) pointer
##  loose
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##  B1: SymVar_1 = 6C (l)  |  B2: SymVar_1 = 0 ()
##  B1: SymVar_2 = 69 (i)  |  B2: SymVar_2 = 0 ()
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor eli
##  [+] 10 bytes tainted from the argv[1] (0x7ffc18b6f60c) pointer
##  loose
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##  B1: SymVar_1 = 6C (l)  |  B2: SymVar_1 = 0 ()
##  B1: SymVar_2 = 69 (i)  |  B2: SymVar_2 = 0 ()
##  B1: SymVar_3 = 74 (t)  |  B2: SymVar_3 = 0 ()
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor elit
##  [+] 10 bytes tainted from the argv[1] (0x7ffcf797160b) pointer
##  loose
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##  B1: SymVar_1 = 6C (l)  |  B2: SymVar_1 = 0 ()
##  B1: SymVar_2 = 69 (i)  |  B2: SymVar_2 = 0 ()
##  B1: SymVar_3 = 74 (t)  |  B2: SymVar_3 = 0 ()
##  B1: SymVar_4 = 65 (e)  |  B2: SymVar_4 = 0 ()
##
##  $ ./build/triton ./src/examples/pin/path_constraints.py ./src/samples/crackmes/crackme_xor elite
##  [+] 10 bytes tainted from the argv[1] (0x7ffdfa2d260a) pointer
##  Win
##  B1: SymVar_0 = 65 (e)  |  B2: SymVar_0 = 0 ()
##  B1: SymVar_1 = 6C (l)  |  B2: SymVar_1 = 0 ()
##  B1: SymVar_2 = 69 (i)  |  B2: SymVar_2 = 0 ()
##  B1: SymVar_3 = 74 (t)  |  B2: SymVar_3 = 0 ()
##  B1: SymVar_4 = 65 (e)  |  B2: SymVar_4 = 0 ()
##

from triton     import *
from triton.ast import *
from pintool    import *

TAINTING_SIZE = 10



def tainting(threadId):
    rdi = getCurrentRegisterValue(REG.RDI) # argc
    rsi = getCurrentRegisterValue(REG.RSI) # argv

    while rdi > 1:
        argv = getCurrentMemoryValue(rsi + ((rdi-1) * CPUSIZE.QWORD), CPUSIZE.QWORD)
        offset = 0
        while offset != TAINTING_SIZE:
            taintMemory(argv + offset)
            concreteValue = getCurrentMemoryValue(argv + offset)
            convertMemoryToSymbolicVariable(MemoryAccess(argv + offset, CPUSIZE.BYTE, concreteValue))
            offset += 1
        print '[+] %02d bytes tainted from the argv[%d] (%#x) pointer' %(offset, rdi-1, argv)
        rdi -= 1

    return


def fini():
    pco = getPathConstraints()
    for pc in pco:
        if pc.isMultipleBranches():
            b1   =  pc.getBranchConstraints()[0]['constraint']
            b2   =  pc.getBranchConstraints()[1]['constraint']
            print b1
            print b2
            seed = list()

            # Branch 1
            models  = getModel(assert_(b1))
            for k, v in models.items():
                print v
                seed.append(v)

            # Branch 2
            models  = getModel(assert_(b2))
            for k, v in models.items():
                print v
                seed.append(v)

            if seed:
                print 'B1: %s (%c)  |  B2: %s (%c)' %(seed[0], chr(seed[0].getValue()), seed[1], chr(seed[1].getValue()))
    return


if __name__ == '__main__':
    # Define the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Align the memory
    enableMode(MODE.ALIGNED_MEMORY, True)

    # Only perform the symbolic execution on the target binary
    setupImageWhitelist(['crackme_xor'])

    # Add callbacks
    insertCall(tainting, INSERT_POINT.ROUTINE_ENTRY, 'main')
    insertCall(fini,     INSERT_POINT.FINI)

    # Run the instrumentation - Never returns
    runProgram()

