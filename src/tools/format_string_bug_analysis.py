#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Triton tool for format string bug analysis.
##  Jonathan Salwan - 2015-04-29
##
## Description:
## ------------
##
## This tool taints all arguments (*argv[]) and checks when a printf occurs if
## there is some tainted bytes in its first argument (RDI). If RDI points on a
## memory area which contains tainted bytes, that means there is a potential
## vulnerability.
##
##
## Output:
## -------
##
## $ ./triton ./src/tools/format_string_bug_analysis.py ./src/samples/vulns/formatString abcd titutatatoto
## [+] 012 bytes tainted from the argv[2] (0x7fff367da0f9) pointer
## [+] 004 bytes tainted from the argv[1] (0x7fff367da0f4) pointer
## [+] 028 bytes tainted from the argv[0] (0x7fff367da0d7) pointer
## [+] Analyzing the printf prologue argument.
## [+] Possible format string bug found. The first argument contains some tainted bytes.
##          [trace] 0x4005e6: mov byte ptr [rax], 0x0
##          [trace] 0x4005e9: mov rax, qword ptr [rbp-0x8]
##          [trace] 0x4005ed: mov rdi, rax
##          [trace] 0x4005f0: mov eax, 0x0
##          [trace] 0x4005f5: call 0x400460
##          [trace] 0x400460: jmp qword ptr [rip+0x200bb2]
##          [trace] 0x400466: push 0x0
##          [trace] 0x40046b: jmp 0x400450
##          [trace] 0x400450: push qword ptr [rip+0x200bb2]
##          [trace] 0x400456: jmp qword ptr [rip+0x200bb4]
## abcd
## $

import os

from triton  import *
from pintool import *


COUNT           = 0
TRACE           = list()
TRACE_SIZE      = 10


# When a printf occurs, we check if the first argument (RDI)
# contains some tainted byte. If it's true -> possible vulnerability.
def printfAnalysis(threadId):
    print '[+] Analyzing the printf prologue argument.'
    arg = getCurrentRegisterValue(REG.RDI)
    index = 0
    while getCurrentMemoryValue(arg + index) != 0x00:
        if isAddrTainted(arg + index) == True:
            print '[+] Possible format string bug found. The first argument contains some tainted bytes.'
            global TRACE
            for t in TRACE:
                print '\t [trace] %#x: %s' %(t[0], t[1])
            return
        index += 1
    return


# When the main function is called, we taint the *argv[] arguments.
def mainAnalysis(threadId):

    rdi = getCurrentRegisterValue(REG.RDI) # argc
    rsi = getCurrentRegisterValue(REG.RSI) # argv

    while rdi != 0:
        argv = getCurrentMemoryValue(rsi + ((rdi-1) * CPUSIZE.REG), CPUSIZE.REG)
        offset = 0
        while getCurrentMemoryValue(argv + offset) != 0x00:
            taintAddr(argv + offset)
            offset += 1
        print '[+] %03d bytes tainted from the argv[%d] (%#x) pointer' %(offset, rdi-1, argv)
        rdi -= 1

    return


# Only save the last TRACE_SIZE instructions for the trace dump
# when a vulnerability is found.
def trace(instruction):
    global COUNT
    global TRACE

    # Save
    if len(TRACE) < TRACE_SIZE:
        TRACE.append(tuple((instruction.getAddress(), instruction.getDisassembly())))
    else:
        TRACE[COUNT % TRACE_SIZE] = tuple((instruction.getAddress(), instruction.getDisassembly()))

    COUNT += 1
    return


if __name__ == '__main__':

    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the entry point
    startAnalysisFromEntry()

    # Only trace the targeted binary
    setupImageWhitelist(["formatString"])

    # Add a callback.
    addCallback(printfAnalysis, CALLBACK.ROUTINE_ENTRY, 'printf')
    addCallback(mainAnalysis,   CALLBACK.ROUTINE_ENTRY, 'main')
    addCallback(trace,          CALLBACK.AFTER)

    # Run the instrumentation - Never returns
    runProgram()


