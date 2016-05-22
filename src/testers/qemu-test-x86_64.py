# $ ./triton ./src/testers/qemu-test-x86_64.py ./src/samples/ir_test_suite/qemu-test-x86_64

from triton  import *
from ast     import *
from pintool import *

import sys
import time


def sbefore(instruction):
    concretizeAllMemory()
    concretizeAllRegister()
    return


def cafter(instruction):

    bad  = list()
    regs = getParentRegisters()

    for reg in regs:

        cvalue = getCurrentRegisterValue(reg)
        seid   = getSymbolicRegisterId(reg)

        if seid == SYMEXPR.UNSET:
            continue

        expr   = getFullAstFromId(seid)
        svalue = expr.evaluate()

        # Check register
        if cvalue != svalue:
            bad.append({
                'reg':    reg.getName(),
                'svalue': svalue,
                'cvalue': cvalue,
                'expr':   expr
            })

    if bad:
        dump = '[KO] %#x: %s (%d register error(s))' %(instruction.getAddress(), instruction.getDisassembly(), len(bad))
        for w in bad:
            dump += '\n     Register       : %s'    %(w['reg'])
            dump += '\n     Symbolic Value : %016x' %(w['svalue'])
            dump += '\n     Concrete Value : %016x' %(w['cvalue'])
            dump += '\n     Expression     : %s'    %(w['expr'])

        print dump
        with open('./semantics_issues', 'a') as fd:
            fd.write(dump+'\n')

    if len(instruction.getSymbolicExpressions()) == 0:
        dump = '[unsupported] %#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
        print dump
        with open('./semantics_issues', 'a') as fd:
            fd.write(dump+'\n')
        return

    # Reset everything
    resetEngines()

    return


if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    setupImageWhitelist(['emu-test-x86_64'])
    startAnalysisFromSymbol('main')
    addCallback(cafter,  CALLBACK.AFTER)
    addCallback(sbefore, CALLBACK.BEFORE_SYMPROC)
    runProgram()

