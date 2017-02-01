#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./code_coverage_crackme_xor.py
##  Seed injected: {4096: 1}
##  Seed injected: {4096L: 101L}
##  Seed injected: {4096L: 0L}
##  Seed injected: {4096L: 101L, 4097L: 108L}
##  Seed injected: {4096L: 101L, 4097L: 0L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 105L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 0L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 105L, 4099L: 116L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 105L, 4099L: 0L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 105L, 4099L: 116L, 4100L: 101L}
##  Seed injected: {4096L: 101L, 4097L: 108L, 4098L: 105L, 4099L: 116L, 4100L: 0L}
##

import  sys

from triton     import *
from triton.ast import *


# Isolated function code which must be cover. The source code
# of this function is basically:
#
#     /* Global serial */
#     char *serial = "\x31\x3e\x3d\x26\x31";
#
#     int check(char *ptr)
#     {
#       int i = 0;
#
#       while (i < 5){
#         if (((ptr[i] - 1) ^ 0x55) != serial[i])
#           return 1;
#         i++;
#       }
#       return 0;
#     }
#
# The objective is to cover this function and so return 1.
#
function = {
                                              #   <serial> function
  0x40056d: "\x55",                           #   push    rbp
  0x40056e: "\x48\x89\xe5",                   #   mov     rbp,rsp
  0x400571: "\x48\x89\x7d\xe8",               #   mov     QWORD PTR [rbp-0x18],rdi
  0x400575: "\xc7\x45\xfc\x00\x00\x00\x00",   #   mov     DWORD PTR [rbp-0x4],0x0
  0x40057c: "\xeb\x3f",                       #   jmp     4005bd <check+0x50>
  0x40057e: "\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x400581: "\x48\x63\xd0",                   #   movsxd  rdx,eax
  0x400584: "\x48\x8b\x45\xe8",               #   mov     rax,QWORD PTR [rbp-0x18]
  0x400588: "\x48\x01\xd0",                   #   add     rax,rdx
  0x40058b: "\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x40058e: "\x0f\xbe\xc0",                   #   movsx   eax,al
  0x400591: "\x83\xe8\x01",                   #   sub     eax,0x1
  0x400594: "\x83\xf0\x55",                   #   xor     eax,0x55
  0x400597: "\x89\xc1",                       #   mov     ecx,eax
  0x400599: "\x48\x8b\x15\xa0\x0a\x20\x00",   #   mov     rdx,QWORD PTR [rip+0x200aa0]        # 601040 <serial>
  0x4005a0: "\x8b\x45\xfc",                   #   mov     eax,DWORD PTR [rbp-0x4]
  0x4005a3: "\x48\x98",                       #   cdqe
  0x4005a5: "\x48\x01\xd0",                   #   add     rax,rdx
  0x4005a8: "\x0f\xb6\x00",                   #   movzx   eax,BYTE PTR [rax]
  0x4005ab: "\x0f\xbe\xc0",                   #   movsx   eax,al
  0x4005ae: "\x39\xc1",                       #   cmp     ecx,eax
  0x4005b0: "\x74\x07",                       #   je      4005b9 <check+0x4c>
  0x4005b2: "\xb8\x01\x00\x00\x00",           #   mov     eax,0x1
  0x4005b7: "\xeb\x0f",                       #   jmp     4005c8 <check+0x5b>
  0x4005b9: "\x83\x45\xfc\x01",               #   add     DWORD PTR [rbp-0x4],0x1
  0x4005bd: "\x83\x7d\xfc\x04",               #   cmp     DWORD PTR [rbp-0x4],0x4
  0x4005c1: "\x7e\xbb",                       #   jle     40057e <check+0x11>
  0x4005c3: "\xb8\x00\x00\x00\x00",           #   mov     eax,0x0
  0x4005c8: "\x5d",                           #   pop     rbp
  0x4005c9: "\xc3",                           #   ret
}



# This function emulates the code.
def run(ip):
    while ip in function:
        # Build an instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(function[ip])

        # Setup Address
        inst.setAddress(ip)

        # Process everything
        processing(inst)

        # Display instruction
        #print inst

        # Next instruction
        ip = buildSymbolicRegister(REG.RIP).evaluate()
    return



# This function initializes the context memory.
def initContext():
    # Define the address of the serial pointer. The address of the serial pointer
    # must be the same that the one hardcoded into the targeted function. However,
    # the serial pointer (here 0x900000) is arbitrary.
    setConcreteMemoryValue(0x601040, 0x00)
    setConcreteMemoryValue(0x601041, 0x00)
    setConcreteMemoryValue(0x601042, 0x90)

    # Define the serial context. We store the serial content located on our arbitrary
    # serial pointer (0x900000).
    setConcreteMemoryValue(0x900000, 0x31)
    setConcreteMemoryValue(0x900001, 0x3e)
    setConcreteMemoryValue(0x900002, 0x3d)
    setConcreteMemoryValue(0x900003, 0x26)
    setConcreteMemoryValue(0x900004, 0x31)

    # Point RDI on our buffer. The address of our buffer is arbitrary. We just need
    # to point the RDI register on it as first argument of our targeted function.
    setConcreteRegisterValue(Register(REG.RDI, 0x1000))

    # Setup stack on an abitrary address.
    setConcreteRegisterValue(Register(REG.RSP, 0x7fffffff))
    setConcreteRegisterValue(Register(REG.RBP, 0x7fffffff))
    return



# This function returns a set of new inputs based on the last trace.
def getNewInput():
    # Set of new inputs
    inputs = list()

    # Get path constraints from the last execution
    pco = getPathConstraints()

    # We start with any input. T (Top)
    previousConstraints = equal(bvtrue(), bvtrue())

    # Go through the path constraints
    for pc in pco:
        # If there is a condition
        if pc.isMultipleBranches():
            # Get all branches
            branches = pc.getBranchConstraints()
            for branch in branches:
                # Get the constraint of the branch which has been not taken
                if branch['isTaken'] == False:
                    # Ask for a model
                    models = getModel(assert_(land(previousConstraints, branch['constraint'])))
                    seed   = dict()
                    for k, v in models.items():
                        # Get the symbolic variable assigned to the model
                        symVar = getSymbolicVariableFromId(k)
                        # Save the new input as seed.
                        seed.update({symVar.getKindValue(): v.getValue()})
                    if seed:
                        inputs.append(seed)

        # Update the previous constraints with true branch to keep a good path.
        previousConstraints = land(previousConstraints, pc.getTakenPathConstraintAst())

    # Clear the path constraints to be clean at the next execution.
    clearPathConstraints()

    return inputs


def symbolizeInputs(seed):
    # Clean symbolic state
    concretizeAllRegister()
    concretizeAllMemory()
    for address, value in seed.items():
        convertMemoryToSymbolicVariable(MemoryAccess(address, CPUSIZE.BYTE, value))
        convertMemoryToSymbolicVariable(MemoryAccess(address+1, CPUSIZE.BYTE))
    return


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Symbolic optimization
    enableMode(MODE.ALIGNED_MEMORY, True)

    # Define entry point
    ENTRY = 0x40056d

    # We start the execution with a random value located at 0x1000.
    lastInput = list()
    worklist  = list([{0x1000:1}])

    while worklist:
        # Take the first seed
        seed = worklist[0]

        print 'Seed injected:', seed

        # Symbolize inputs
        symbolizeInputs(seed)

        # Init context memory
        initContext()

        # Emulate
        run(ENTRY)

        lastInput += [dict(seed)]
        del worklist[0]

        newInputs = getNewInput()
        for inputs in newInputs:
            if inputs not in lastInput and inputs not in worklist:
                worklist += [dict(inputs)]

    sys.exit(0)

