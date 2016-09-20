#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Example to detect opaque predicates. This example is based
## on the Tomislav Zubcic's blog post [0,1] =).
##
## Output:
##
##  $ python proving_opaque_predicates.py
##  xor eax, eax
##  jo 7
##  opaque predicate: never taken
##  ----------------------------------
##  xor eax, eax
##  je 7
##  opaque predicate: always taken
##  ----------------------------------
##  xor eax, ebx
##  je 7
##  not an opaque predicate
##  ----------------------------------
##  and eax, 0x3fffffff
##  and ebx, 0x3fffffff
##  xor ecx, edx
##  xor edx, edi
##  add eax, ebx
##  jo 0x16
##  opaque predicate: never taken
##  ----------------------------------
##  and eax, 0x3fffffff
##  and ebx, 0x3fffffff
##  xor ecx, edx
##  xor edx, edi
##  xor eax, ebx
##  je 0x16
##  not an opaque predicate
##  ----------------------------------
##
## [0] http://zubcic.re/blog/experimenting-with-z3-proving-opaque-predicates
## [1] https://www.reddit.com/r/ReverseEngineering/comments/4yf6tz/experimenting_with_z3_proving_opaque_predicates/
##
## -- jonathan

import sys
from   triton import *

trace_1 = [
    "\x31\xC0",                  # xor eax, eax
    "\x0F\x80\x01\x00\x00\x00",  # jo 7
]

trace_2 = [
    "\x31\xC0",                  # xor eax, eax
    "\x0F\x84\x01\x00\x00\x00",  # je 7
]

trace_3 = [
    "\x31\xD8",                  # xor eax, ebx
    "\x0F\x84\x01\x00\x00\x00",  # je 7
]

trace_4 = [
    "\x25\xff\xff\xff\x3f",      # and eax, 0x3fffffff
    "\x81\xe3\xff\xff\xff\x3f",  # and ebx, 0x3fffffff
    "\x31\xd1",                  # xor ecx, edx
    "\x31\xfa",                  # xor edx, edi
    "\x01\xd8",                  # add eax, ebx
    "\x0f\x80\x10\x00\x00\x00",  # jo 27
]

trace_5 = [
    "\x25\xff\xff\xff\x3f",      # and eax, 0x3fffffff
    "\x81\xe3\xff\xff\xff\x3f",  # and ebx, 0x3fffffff
    "\x31\xd1",                  # xor ecx, edx
    "\x31\xfa",                  # xor edx, edi
    "\x31\xD8",                  # xor eax, ebx
    "\x0F\x84\x10\x00\x00\x00",  # je 16
]


def symbolization_init():
    convertRegisterToSymbolicVariable(REG.EAX)
    convertRegisterToSymbolicVariable(REG.EBX)
    convertRegisterToSymbolicVariable(REG.ECX)
    convertRegisterToSymbolicVariable(REG.EDX)
    return

def test_trace(trace):
    setArchitecture(ARCH.X86)
    symbolization_init()

    for opcodes in trace:
        instruction = Instruction()
        instruction.setOpcodes(opcodes)
        processing(instruction)
        print instruction.getDisassembly()

        if instruction.isBranch():
            # Opaque Predicate AST
            op_ast = getPathConstraintsAst()
            # Try another model
            model = getModel(ast.assert_(ast.lnot(op_ast)))
            if model:
                print "not an opaque predicate"
            else:
                if instruction.isConditionTaken():
                    print "opaque predicate: always taken"
                else:
                    print "opaque predicate: never taken"

    print '----------------------------------'
    return

if __name__ == '__main__':
    test_trace(trace_1)
    test_trace(trace_2)
    test_trace(trace_3)
    test_trace(trace_4)
    test_trace(trace_5)
    sys.exit(0)

