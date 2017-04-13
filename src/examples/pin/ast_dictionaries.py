#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## $ ./build/triton ./src/examples/pin/ast_dictionaries.py ./src/samples/crackmes/crackme_xor elite
##

from operator   import itemgetter
from pintool    import *
from triton     import ARCH, MODE


def cb_fini():
    l = getTritonContext().getAstDictionariesStats().items()
    l.sort(key=itemgetter(1), reverse=True)
    print '============================================================='
    print 'AST Dictionaries Stats'
    print '============================================================='
    for i in l:
        if i[1] > 0:
            print '%s: %s' %(i[0], '{:,}'.format(i[1]))
    print '============================================================='
    return


if __name__ == '__main__':
    # Set arch
    getTritonContext().setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    # Use AST Dictionaries
    getTritonContext().enableMode(MODE.AST_DICTIONARIES, True)

    # Add callbacks
    insertCall(cb_fini, INSERT_POINT.FINI)

    # Run Program
    runProgram()

