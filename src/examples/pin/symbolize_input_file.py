#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## The binary read_from_file opens the file /etc/passwd and checks if it's a binary.
## This script symbolizes the file /etc/passwd and returns a model which satisfies the
## condition "is a binary". Basically, it returns the .ELF magic which must be present
## in the first dword of the binary.
##
## $ ./build/triton ./src/examples/pin/symbolize_input_file.py ./src/samples/others/read_from_file
## [TT] Target name match: /etc/passwd
## [TT] Target fd: 4
## [TT] Symbolizing the input file
## [+] Not an ELF binary
## [TT] Model: {0L: SymVar_0 = 7F, 1L: SymVar_1 = 45, 2L: SymVar_2 = 4C, 3L: SymVar_3 = 46}
## $
##

import string
import sys

from triton  import *
from pintool import *

targetName = "/etc/passwd"
targetFd   = None
isOpen     = False
isRead     = None



def getMemoryString(addr):
    index = 0
    s = str()

    while getCurrentMemoryValue(addr+index):
        c = chr(getCurrentMemoryValue(addr+index))
        s += ("" if c not in string.printable else c)
        index += 1

    return s


def syscallsEntry(threadId, std):
    global isOpen
    global isRead
    global targetFd

    if getSyscallNumber(std) == SYSCALL.OPEN:
        name = getMemoryString(getSyscallArgument(std, 0))
        if name == targetName:
            isOpen = True
            print '[TT] Target name match: %s' %(name)

    elif getSyscallNumber(std) == SYSCALL.READ:
        fd   = getSyscallArgument(std, 0)
        buff = getSyscallArgument(std, 1)
        size = getSyscallArgument(std, 2)
        if fd == targetFd:
            isRead = {'buff': buff, 'size': size}

    return


def syscallsExit(threadId, std):
    global isOpen
    global isRead
    global targetFd

    if isOpen:
        targetFd = getSyscallReturn(std)
        isOpen = False
        print '[TT] Target fd: %d' %(targetFd)

    elif isRead is not None:
        size = isRead['size']
        buff = isRead['buff']
        print '[TT] Symbolizing the input file'
        for index in range(size):
            convertMemoryToSymbolicVariable(MemoryAccess(buff+index, CPUSIZE.BYTE, getCurrentMemoryValue(buff+index)))
        isRead = None

    return


def fini():
    pc = getPathConstraintsAst()
    m = getModel(ast.assert_(ast.lnot(pc)))
    print '[TT] Model:', m
    return


if __name__ == '__main__':
    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    insertCall(syscallsEntry, INSERT_POINT.SYSCALL_ENTRY)
    insertCall(syscallsExit,  INSERT_POINT.SYSCALL_EXIT)
    insertCall(fini,          INSERT_POINT.FINI)

    # Run the instrumentation - Never returns
    runProgram()

