#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
##  Triton tool for use-after-free bug analysis and memory leak.
##  Jonathan Salwan - 2015-04-30
##
## Description:
## ------------
##
## This tool maintains a free table (TF) and an allocation table (TA) which
## represent the states of pointers allocated/freed during the execution.
## When a LOAD or STORE instruction occurs, the tool checks if the memory
## access is referenced into TA or TF.
##
## If the memory access is in TF -> use-after-free.
##
## Output:
## -------
##
##  $ ./triton ./src/tools/use_after_free_bug_analysis.py ./src/samples/vulns/testSuite
##  [+] TA <- (0x1bec010, 0x20)
##  [+] TA <- (0x1bec040, 0x20)
##  [+] TA -> (0x1bec010, 0x20)
##  [+] TF <- (0x1bec010, 0x20)
##  [!] Use-after-free (0x1bec020) at 0x4006cb: mov byte ptr [rax], 0x43
##  [+] TF -> (0x1bec010, 0x20)
##  [+] TA <- (0x1bec010, 0x20)
##  [+] TA -> (0x1bec040, 0x20)
##  [+] TF <- (0x1bec040, 0x20)
##
##  Free table:
##          (0x1bec040, 0x20)
##
##  Allocation table:
##          (0x1bec010, 0x20)
##
##  [!] There is 32 bytes of leaked memory
##

from triton  import *
from pintool import *

TA              = list()
TF              = list()
TMP             = None



def mallocEntry(threadId):
    global TMP
    rdi = getCurrentRegisterValue(REG.RDI)
    TMP = rdi
    return



def mallocExit(threadId):

    global TA
    global TF
    global TMP

    rax = getCurrentRegisterValue(REG.RAX)
    if rax != 0:
        for (delta, size) in TF:

            # Same area
            if delta == rax and TMP == size:
                print '[+] TF -> (%#x, %#x)' %(delta, size)
                TF.remove(tuple((delta, size)))
                print '[+] TA <- (%#x, %#x)' %(rax, TMP)
                TA.append(tuple((rax, TMP)))
                return

            # Area splitted
            if delta == rax and TMP != size:
                print '[+] TF -> (%#x, %#x)' %(delta, size)
                TF.remove(tuple((delta, size)))
                if TMP < size:
                    print '[+] TF <- (%#x, %#x)' %(delta + TMP, size - TMP)
                    TF.append(tuple((delta + TMP, size - TMP)))
                print '[+] TA <- (%#x, %#x)' %(rax, TMP)
                TA.append(tuple((rax, TMP)))
                return

        print '[+] TA <- (%#x, %#x)' %(rax, TMP)
        TA.append(tuple((rax, TMP)))

    return



def freeEntry(threadId):

    global TA
    global TF

    rdi = getCurrentRegisterValue(REG.RDI)
    for (delta, size) in TA:
        if delta == rdi:
            print '[+] TA -> (%#x, %#x)' %(delta, size)
            TA.remove(tuple((delta, size)))
            print '[+] TF <- (%#x, %#x)' %(delta, size)
            TF.append(tuple((delta, size)))
            return

    for (delta, size) in TF:
        if delta == rdi:
            print '[!] Double free bug found'
            return

    print '[!] Invalid free bug found with the pointer %#x' %(rdi)
    return



def trace(instruction):
    global TF
    for operand in instruction.getOperands():
        if operand.getType() == OPERAND.MEM:
            memoryAccess     = operand.getAddress()
            memoryAccessSize = operand.getSize()
            for (delta, size) in TF:
                if memoryAccess > delta and memoryAccess < delta+size:
                    print '[!] Use-after-free (%#x) at %#x: %s' %(memoryAccess, instruction.getAddress(), instruction.getDisassembly())
                    return
    return



def fini():
    global TA
    global TF

    print '\nFree table:'
    for (delta, size) in TF:
        print '\t(%#x, %#x)' %(delta, size)

    if len(TF) == 0:
        print '\tEmpty'

    memLeak = 0
    print '\nAllocation table:'
    for (delta, size) in TA:
        print '\t(%#x, %#x)' %(delta, size)
        memLeak += size

    if len(TA) == 0:
        print '\tEmpty'

    if memLeak > 0:
        print '\n[!] There is %d bytes of leaked memory' %(memLeak)

    return


if __name__ == '__main__':

    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the entry point
    startAnalysisFromEntry()

    # Add a callback.
    addCallback(mallocEntry, CALLBACK.ROUTINE_ENTRY, 'malloc')
    addCallback(mallocExit,  CALLBACK.ROUTINE_EXIT, 'malloc')
    addCallback(freeEntry,   CALLBACK.ROUTINE_ENTRY, 'free')
    addCallback(trace,       CALLBACK.AFTER)
    addCallback(fini,        CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()


