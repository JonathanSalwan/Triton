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
## represents the states of pointers allocated/freed during the execution.
## When a LOAD and STORE instruction occurs, the tool checks if the memory
## access is referenced into TA or TF. 
##
## If the memory access is in TF -> use-after-free.
##
## Output:
## -------
##
##  $ ./triton ./tools/use_after_free_bug_analysis.py ./samples/vulns/testSuite
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


from triton import *


ENTRY_POINT     = 0x4004a0
TA              = list()
TF              = list()
TMP             = None




def mallocEntry(threadId):
    global TMP
    rdi = getRegValue(IDREF.REG.RDI)
    TMP = rdi
    return



def mallocExit(threadId):

    global TA
    global TF
    global TMP

    rax = getRegValue(IDREF.REG.RAX)
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

    rdi = getRegValue(IDREF.REG.RDI)
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
        if operand.getType() == IDREF.OPERAND.MEM_W or operand.getType() == IDREF.OPERAND.MEM_R:
            memoryAccess     = operand.getValue()
            memoryAccessSize = operand.getSize()
            for (delta, size) in TF:
                if memoryAccess > delta and memoryAccess < delta+size:
                    print '[!] Use-after-free (%#x) at %#x: %s' %(memoryAccess, instruction.getAddress(), instruction.getDiassembly())
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

    # Start the symbolic analysis from the entry point
    startAnalysisFromAddr(ENTRY_POINT)

    # Add a callback.
    addCallback(mallocEntry, IDREF.CALLBACK.ROUTINE_ENTRY, 'malloc')
    addCallback(mallocExit, IDREF.CALLBACK.ROUTINE_EXIT, 'malloc')
    addCallback(freeEntry, IDREF.CALLBACK.ROUTINE_ENTRY, 'free')
    addCallback(trace, IDREF.CALLBACK.AFTER)
    addCallback(fini, IDREF.CALLBACK.FINI)

    # Run the instrumentation - Never returns
    runProgram()


