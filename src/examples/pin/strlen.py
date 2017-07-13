#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  $ ./build/triton ./src/examples/pin/strlen.py ./src/samples/others/strlen 1
##  [+] 011 bytes tainted from the argv[1] (0x7ffd0014d61f) pointer
##  Possible solution: ff:ff:ff:ff:ff:ff:00:ff:ff:ff:ff
##  Possible solution: 01:01:01:01:01:01:00
##  Possible solution: 80:09:01:40:01:03:00
##  Possible solution: 80:09:01:40:01:83:00:00
##  Possible solution: 80:09:01:40:01:93:00:00:00
##  Possible solution: 80:09:01:40:01:92:00:00
##  Possible solution: 80:09:01:40:01:96:00:00
##  Possible solution: 80:09:01:40:41:96:00
##  Possible solution: 80:09:01:40:03:96:00:00
##  Possible solution: 80:09:21:40:03:96:00:00
##  Possible solution: 80:09:29:40:03:96:00:00:00
##  Possible solution: 80:09:28:40:03:96:00
##  Possible solution: 80:09:38:40:03:96:00:00
##  Possible solution: 80:09:3a:40:03:96:00:00
##  Possible solution: 80:09:32:40:03:96:00:00
##  Possible solution: 80:09:b2:40:03:96:00:00:00
##  Possible solution: 80:09:f2:40:03:96:00:00:04
##  Possible solution: 80:09:f0:40:03:96:00:00
##  Possible solution: 80:09:d0:40:03:96:00:00
##  Possible solution: 80:09:d4:40:03:96:00:00
##

from triton     import ARCH, MemoryAccess, CPUSIZE
from pintool    import *

# What value you want that strlen must return?
STRLEN_ASSERT_LEN = 6

# What number of possible solutions you want?
SOLUTIONS = 20

Triton = getTritonContext()


def before(instruction):
    if instruction.getAddress() == 0x4005c5:
        rax = Triton.getSymbolicRegisterId(Triton.registers.rax)
        raxAst = Triton.getAstFromId(rax)
        astCtxt = Triton.getAstContext()
        constraint = astCtxt.assert_(astCtxt.equal(raxAst, astCtxt.bv(STRLEN_ASSERT_LEN, raxAst.getBitvectorSize())))
        models = Triton.getModels(constraint, SOLUTIONS)
        for model in models:
            s = str()
            for i in range(STRLEN_ASSERT_LEN+5):
                try:    s += chr(model[i].getValue())
                except: pass
            print "Possible solution:", ":".join("{:02x}".format(ord(c)) for c in s)
    return


def tainting(threadId):

    rdi = getCurrentRegisterValue(Triton.registers.rdi) # argc
    rsi = getCurrentRegisterValue(Triton.registers.rsi) # argv

    while rdi > 1:
        argv = getCurrentMemoryValue(rsi + ((rdi-1) * CPUSIZE.QWORD), CPUSIZE.QWORD)
        offset = 0
        while offset != STRLEN_ASSERT_LEN+5:
            Triton.taintMemory(argv + offset)
            concreteValue = getCurrentMemoryValue(argv + offset)
            Triton.setConcreteMemoryValue(argv + offset, concreteValue)
            Triton.convertMemoryToSymbolicVariable(MemoryAccess(argv + offset, CPUSIZE.BYTE))
            offset += 1
        print '[+] %03d bytes tainted from the argv[%d] (%#x) pointer' %(offset, rdi-1, argv)
        rdi -= 1

    return


if __name__ == '__main__':
    # Define the architecture
    Triton.setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'main' function
    startAnalysisFromSymbol('main')

    # Add callbacks
    insertCall(tainting, INSERT_POINT.ROUTINE_ENTRY, 'main')
    insertCall(before,   INSERT_POINT.BEFORE_SYMPROC)

    # Run the instrumentation - Never returns
    runProgram()

