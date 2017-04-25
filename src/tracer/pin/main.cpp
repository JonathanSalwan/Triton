//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the BSD License.
*/

#include <csignal>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>

#include <pin.H>

/* libTriton */
#include <triton/api.hpp>
#include <triton/pythonBindings.hpp>

/* Pintool */
#include "bindings.hpp"
#include "context.hpp"
#include "snapshot.hpp"
#include "trigger.hpp"
#include "utils.hpp"



/*! \page Tracer_page Tracer
    \brief [**internal**] All information about how to plug a tracer.
\tableofcontents
\section Tracer_description Description
<hr>

The new design of the Triton library (since the `v0.3`), allows you to plug any kind of tracers. E.g: Pin,
Valgrind and even a database.

<p align="center"><img src="https://triton.quarkslab.com/files/triton_v03_architecture.png"/></p>

To use the `libTriton`, your tracer must provide two kinds of information at each program point:

- The current opcode executed.
- A state context (register and memory).

Based on these two information, Triton will translate the control flow into \ref py_ast_page. As an example, let assume that you have dumped
a trace into a database with all registers state and memory access - these information may come from Valgrind, Pin, Qemu or whatever. The following Python code
uses the Triton's API to build the semantics of each instruction stored in the database.

~~~~~~~~~~~~~{.py}
#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import  sys
import  struct

from triton  import *
from datbase import import Manager

unpack_size = {1: 'B', 2: 'H', 4: 'I', 8: 'Q', 16: 'QQ'}

if __name__ == '__main__':

    # Set the arch
    setArchitecture(ARCH.X86_64)

    # Connect to the database
    db = Manager().connect()

    # inst_id is the instruction id into the database.
    inst_id = 1

    while True:

        # Get opcode (from database)
        opcode = db.get_opcode_from_inst_id(inst_id)
        if opcode is None:
            break

        # Get concrete register value (from database)
        regs = db.get_registers_from_inst_id(inst_id)

        # Build the Triton instruction
        inst = Instruction()

        # Setup opcodes
        inst.setOpcodes(opcode)

        # Setup Address
        inst.setAddress(regs['rip'])

        # Update concrete register state
        setConcreteRegisterValue(Register(REG.RAX,    regs['rax']))
        setConcreteRegisterValue(Register(REG.RBX,    regs['rbx']))
        setConcreteRegisterValue(Register(REG.RCX,    regs['rcx']))
        setConcreteRegisterValue(Register(REG.RDX,    regs['rdx']))
        setConcreteRegisterValue(Register(REG.RDI,    regs['rdi']))
        setConcreteRegisterValue(Register(REG.RSI,    regs['rsi']))
        setConcreteRegisterValue(Register(REG.RBP,    regs['rbp']))
        setConcreteRegisterValue(Register(REG.RSP,    regs['rsp']))
        setConcreteRegisterValue(Register(REG.RIP,    regs['rip']))
        setConcreteRegisterValue(Register(REG.R8,     regs['r8']))
        setConcreteRegisterValue(Register(REG.R9,     regs['r9']))
        setConcreteRegisterValue(Register(REG.R10,    regs['r10']))
        setConcreteRegisterValue(Register(REG.R11,    regs['r11']))
        setConcreteRegisterValue(Register(REG.R12,    regs['r12']))
        setConcreteRegisterValue(Register(REG.R13,    regs['r13']))
        setConcreteRegisterValue(Register(REG.R14,    regs['r14']))
        setConcreteRegisterValue(Register(REG.R15,    regs['r15']))
        setConcreteRegisterValue(Register(REG.EFLAGS, regs['eflags']))
        setConcreteRegisterValue(Register(REG.FS,     regs['fs'])) # The mapped base address
        setConcreteRegisterValue(Register(REG.GS,     regs['gs'])) # The mapped base address

        # Update concrete memory access
        accesses = db.get_memory_access_from_inst_id(inst_id)

        # Update memory access
        for access in accesses:
            if access['kind'] == 'R':
                address = access['addr']
                data    = access['data']
                value   = struct.unpack(unpack_size[len(data)], data)[0]
                setConcreteMemoryValue(MemoryAccess(address, len(data), value))

        # Process everything (build IR, spread taint, perform simplification, ...)
        processing(inst)

        # At this point, all engines inside the Triton library were been synchronized with the concrete state.
        # Display instruction
        print inst

        # Display symbolic expressions
        for expr in inst.getSymbolicExpressions():
            print '\t', expr

        # Next instruction (from the database)
        inst_id += 1

    sys.exit(0)
~~~~~~~~~~~~~

The database connection is a pure example to show you how to interact with the Triton API. As Triton is written in `C++`, you can directly
create your Triton instruction inside a DBI engine (like Pin or Valgrind). According to your tracer, you can refer to the [Python](https://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)
or the [C++](https://triton.quarkslab.com/documentation/doxygen/classtriton_1_1API.html) API.

\section Tracer_pintool The Triton's pintool
<hr>

This project is shippied with a pintool as tracer. Basically, you can add callbacks, get current registers and memory values, inject values into registers and memory,
start and stop analysis at specific points, select what images are jitted or not, interact with the Triton API and many more... All information about the pintool API
is describe at this following page \ref pintool_py_api. Below, some examples.

<hr>
\subsection Tracer_pintool_example_1 Example - Display IR

~~~~~~~~~~~~~{.py}
#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import sys

from pintool import *
from triton  import *


def mycb(inst):
    print inst
    for expr in inst.getSymbolicExpressions():
        print expr
    print
    return


if __name__ == '__main__':
    # Set arch
    setArchitecture(ARCH.X86_64)

    # Start JIT at the entry point
    startAnalysisFromEntry()

    # Add callback
    insertCall(mycb, INSERT_POINT.BEFORE)

    # Run Program
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_2 Example - Runtime Memory Tainting

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *

GREEN = "\033[92m"
ENDC  = "\033[0m"


# 0x40058b: movzx eax, byte ptr [rax]
#
# When the instruction located in 0x40058b is executed,
# we taint the memory that RAX holds.
def cbeforeSymProc(instruction):
    if instruction.getAddress() == 0x40058b:
        rax = getCurrentRegisterValue(REG.RAX)
        taintMemory(rax)


def cafter(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
    for se in instruction.getSymbolicExpressions():
        if se.isTainted() == True:
            print '\t -> %s%s%s' %(GREEN, se.getAst(), ENDC)
        else:
            print '\t -> %s' %(se.getAst())
    print


if __name__ == '__main__':

    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the 'check' function
    startAnalysisFromSymbol('check')

    insertCall(cbeforeSymProc, INSERT_POINT.BEFORE_SYMPROC)
    insertCall(cafter, INSERT_POINT.AFTER)

    # Run the instrumentation - Never returns
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_3 Example - Runtime Register Modification

~~~~~~~~~~~~~{.py}
#!/usr/bin/env python2
## -*- coding: utf-8 -*-
##
## Output:
##
##  $ ./build/triton ./src/examples/pin/runtime_register_modification.py ./src/samples/crackmes/crackme_xor a
##  4005f9: mov dword ptr [rbp - 4], eax
##          ref!180 = ((_ extract 31 24) (_ bv0 32)) ; byte reference - MOV operation
##          ref!181 = ((_ extract 23 16) (_ bv0 32)) ; byte reference - MOV operation
##          ref!182 = ((_ extract 15 8) (_ bv0 32)) ; byte reference - MOV operation
##          ref!183 = ((_ extract 7 0) (_ bv0 32)) ; byte reference - MOV operation
##          ref!184 = (concat ((_ extract 31 24) (_ bv0 32)) ((_ extract 23 16) (_ bv0 32)) ((_ extract 15 8) (_ bv0 32)) ((_ extract 7 0) (_ bv0 32))) ; concat reference - MOV operation
##          ref!185 = (_ bv4195836 64) ; Program Counter
##  Win
##

import sys
from   pintool import *
from   triton  import *


def cb1(inst):
    if inst.getAddress() == 0x4005f9:
        setCurrentRegisterValue(REG.RAX, 0)

def cb2(inst):
    if inst.getAddress() == 0x4005f9:
        print inst
        for expr in inst.getSymbolicExpressions():
            print '\t', expr


if __name__ == '__main__':
    setArchitecture(ARCH.X86_64)
    setupImageWhitelist(['crackme'])
    startAnalysisFromSymbol('main')
    insertCall(cb1, INSERT_POINT.BEFORE_SYMPROC)
    insertCall(cb2, INSERT_POINT.BEFORE)
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_4 Example - Blacklist images

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *


def mycb(instruction):
    print '%#x: %s' %(instruction.getAddress(), instruction.getDisassembly())
    return


if __name__ == '__main__':

    setArchitecture(ARCH.X86_64)

    # libc and ld-linux will be unjited
    setupImageBlacklist(["libc", "ld-linux"])

    startAnalysisFromSymbol('main')
    insertCall(mycb, INSERT_POINT.BEFORE)
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_5 Example - Callback on image

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *

# Output
#
# $ ./build/triton ./src/examples/pin/callback_image.py ./src/samples/ir_test_suite/ir
# ----------
# Image path:  /dir/Triton/samples/ir_test_suite/ir
# Image base:  0x400000L
# Image size:  2101312
# ----------
# Image path:  /lib64/ld-linux-x86-64.so.2
# Image base:  0x7fb9a14d9000L
# Image size:  2236744
# ----------
# Image path:  /lib64/libc.so.6
# Image base:  0x7fb98b739000L
# Image size:  3766680


def image(imagePath, imageBase, imageSize):
    print '----------'
    print 'Image path: ', imagePath
    print 'Image base: ', hex(imageBase)
    print 'Image size: ', imageSize
    return


if __name__ == '__main__':
    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Add a callback.
    insertCall(image, INSERT_POINT.IMAGE_LOAD)

    # Run the instrumentation - Never returns
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_6 Example - Callback on routine

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *

# Output
#
# $ ./build/triton ./src/examples/pin/callback_routine.py  ./src/samples/vulns/testSuite
# -> malloc(0x20)
# <- 0x8fc010
# -> malloc(0x20)
# <- 0x8fc040
# -> malloc(0x20)
# <- 0x8fc010


def mallocEntry(threadId):
    sizeAllocated = getCurrentRegisterValue(REG.RDI)
    print '-> malloc(%#x)' %(sizeAllocated)


def mallocExit(threadId):
    ptrAllocated = getCurrentRegisterValue(REG.RAX)
    print '<- %#x' %(ptrAllocated)


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Add a callback.
    insertCall(mallocEntry, INSERT_POINT.ROUTINE_ENTRY, "malloc")
    insertCall(mallocExit, INSERT_POINT.ROUTINE_EXIT, "malloc")

    # Run the instrumentation - Never returns
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_7 Example - Callback on signals

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *

# Output
#
#  $ ./build/triton ./src/examples/pin/callback_signals.py ./src/samples/others/signals
#  Signal 11 received on thread 0.
#  ========================== DUMP ==========================
#  rax:    0x00000000000000                        ((_ zero_extend 32) (_ bv234 32))
#  rbx:    0x00000000000000                        UNSET
#  rcx:    0x00000000001ba4                        ((_ zero_extend 32) ((_ extract 31 0) ref!81))
#  rdx:    0x0000000000000b                        ((_ sign_extend 32) ((_ extract 31 0) ref!34))
#  rdi:    0x00000000001ba4                        ((_ sign_extend 32) ((_ extract 31 0) ref!83))
#  rsi:    0x00000000001ba4                        ((_ sign_extend 32) ((_ extract 31 0) ref!90))
#  rbp:    0x007fff097e3540                        ((_ extract 63 0) ref!0)
#  rsp:    0x007fff097e3528                        (bvsub ((_ extract 63 0) ref!47) (_ bv8 64))
#  rip:    0x007f3fa0735ea7                        (_ bv139911251582629 64)
#  r8:     0x007f3fa0a94c80                        UNSET
#  r9:     0x007f3fb671b120                        UNSET
#  r10:    0x00000000000000                        UNSET
#  r11:    0x007f3fa0735e70                        UNSET
#  r12:    0x00000000400460                        UNSET
#  r13:    0x007fff097e3620                        UNSET
#  r14:    0x00000000000000                        UNSET
#  r15:    0x00000000000000                        UNSET
#  xmm0:   0x000000ff000000                        UNSET
#  xmm1:   0x2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f2f      UNSET
#  xmm2:   0x00000000000000                        UNSET
#  xmm3:   0x00ff000000ff00                        UNSET
#  xmm4:   0x000000000000ff                        UNSET
#  xmm5:   0x00000000000000                        UNSET
#  xmm6:   0x00000000000000                        UNSET
#  xmm7:   0x00000000000000                        UNSET
#  xmm8:   0x00000000000000                        UNSET
#  xmm9:   0x00000000000000                        UNSET
#  xmm10:  0x00000000000000                        UNSET
#  xmm11:  0x00000000000000                        UNSET
#  xmm12:  0x00000000000000                        UNSET
#  xmm13:  0x00000000000000                        UNSET
#  xmm14:  0x00000000000000                        UNSET
#  xmm15:  0x00000000000000                        UNSET
#  af:     0x00000000000000                        (ite (= (_ bv16 64) (bvand (_ bv16 64) (bvxor ref!12 (bvxor ((_ extract 63 0) ref!0) (_ bv16 64))))) (_ bv1 1) (_ bv0 1))
#  cf:     0x00000000000000                        (_ bv0 1)
#  df:     0x00000000000000                        UNSET
#  if:     0x00000000000001                        UNSET
#  of:     0x00000000000000                        (_ bv0 1)
#  pd:     0x00000000000001                        (ite (= (parity_flag ((_ extract 7 0) ref!73)) (_ bv0 1)) (_ bv1 1) (_ bv0 1))
#  sf:     0x00000000000000                        (ite (= ((_ extract 31 31) ref!73) (_ bv1 1)) (_ bv1 1) (_ bv0 1))
#  tf:     0x00000000000000                        UNSET
#  zf:     0x00000000000001                        (ite (= ref!73 (_ bv0 32)) (_ bv1 1) (_ bv0 1))



def signals(threadId, sig):
    print 'Signal %d received on thread %d.' %(sig, threadId)
    print '========================== DUMP =========================='
    regs = getParentRegisters()
    for reg in regs:
        value  = getCurrentRegisterValue(reg)
        exprId = getSymbolicRegisterId(reg)
        print '%s:\t%#016x\t%s' %(reg.getName(), value, (getSymbolicExpressionFromId(exprId).getAst() if exprId != SYMEXPR.UNSET else 'UNSET'))
    return


if __name__ == '__main__':

    # Set architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    # Add a callback.
    insertCall(signals, INSERT_POINT.SIGNALS)

    # Run the instrumentation - Never returns
    runProgram()
~~~~~~~~~~~~~

<hr>
\subsection Tracer_pintool_example_8 Example - Callback on syscalls

~~~~~~~~~~~~~{.py}
from triton  import *
from pintool import *

# Output
#
# $ ./build/triton examples/callback_syscall.py  ./samples/crackmes/crackme_xor a
# sys_write(1, 7fb7f06e1000, 6)
# loose
#

def my_callback_syscall_entry(threadId, std):
    if getSyscallNumber(std) == SYSCALL.WRITE:
        arg0 = getSyscallArgument(std, 0)
        arg1 = getSyscallArgument(std, 1)
        arg2 = getSyscallArgument(std, 2)
        print 'sys_write(%x, %x, %x)' %(arg0, arg1, arg2)


if __name__ == '__main__':

    # Set the architecture
    setArchitecture(ARCH.X86_64)

    # Start the symbolic analysis from the Entry point
    startAnalysisFromEntry()

    insertCall(my_callback_syscall_entry, INSERT_POINT.SYSCALL_ENTRY)

    # Run the instrumentation - Never returns
    runProgram()
~~~~~~~~~~~~~

*/




namespace tracer {
  namespace pintool {

    //! Pin options: -script
    KNOB<std::string> KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

    //! Lock / Unlock InsertCall
    Trigger analysisTrigger = Trigger();

    //! Snapshot engine
    Snapshot snapshot = Snapshot();



    /* Switch lock */
    static void toggleWrapper(bool flag) {
      PIN_LockClient();
      tracer::pintool::analysisTrigger.update(flag);
      PIN_UnlockClient();
    }


    /* Callback before instruction processing */
    static void callbackBefore(triton::arch::Instruction* tritonInst, triton::uint8* addr, triton::uint32 size, CONTEXT* ctx, THREADID threadId) {
      /* Some configurations must be applied before processing */
      tracer::pintool::callbacks::preProcessing(tritonInst, threadId);

      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Setup Triton information */
      tritonInst->partialReset();
      tritonInst->setOpcodes(addr, size);
      tritonInst->setAddress(reinterpret_cast<triton::__uint>(addr));
      tritonInst->setThreadId(reinterpret_cast<triton::uint32>(threadId));

      /* Disassemble the instruction */
      triton::api.disassembly(*tritonInst);

      /* Execute the Python callback before the IR processing */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::beforeIRProc(tritonInst);
      else
        tracer::pintool::context::mustBeExecuted = false;

      /* Check if we must execute a new context */
      if (tracer::pintool::context::mustBeExecuted == true) {
        tritonInst->reset();
        tracer::pintool::context::executeContext();
      }

      /* Synchronize gliches between Pintool and libTriton */
      tracer::pintool::context::synchronizeContext();

      /* Process the IR and taint */
      triton::api.buildSemantics(*tritonInst);

      /* Execute the Python callback */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::before(tritonInst);

      /* Check if we must restore the snapshot */
      if (tracer::pintool::snapshot.mustBeRestored() == true) {
        tritonInst->reset();
        tracer::pintool::snapshot.restoreSnapshot(ctx);
      }

      /* Some configurations must be applied after processing */
      tracer::pintool::callbacks::postProcessing(tritonInst, threadId);

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Callback after instruction processing */
    static void callbackAfter(triton::arch::Instruction* tritonInst, CONTEXT* ctx, THREADID threadId) {
      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::after(tritonInst);

      /* Some configurations must be applied after processing */
      tracer::pintool::callbacks::postProcessing(tritonInst, threadId);

      /* Clear Instruction information because of the Pin's cache */
      tritonInst->reset();

      /* Check if we must execute a new context */
      if (tracer::pintool::context::mustBeExecuted == true)
        tracer::pintool::context::executeContext();

      /* Check if we must restore the snapshot */
      if (tracer::pintool::snapshot.mustBeRestored() == true)
        tracer::pintool::snapshot.restoreSnapshot(ctx);

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Save the memory access into the Triton instruction */
    static void saveMemoryAccess(triton::arch::Instruction* tritonInst, triton::__uint addr, triton::uint32 size) {
      /* Mutex */
      PIN_LockClient();
      triton::uint512 value = tracer::pintool::context::getCurrentMemoryValue(addr, size);
      triton::api.setConcreteMemoryValue(triton::arch::MemoryAccess(addr, size, value));
      /* Mutex */
      PIN_UnlockClient();
    }


    /* Callback to save bytes for the snapshot engine */
    static void callbackSnapshot(triton::__uint mem, triton::uint32 writeSize) {
      if (!tracer::pintool::analysisTrigger.getState())
      /* Analysis locked */
        return;

      /* If the snapshot is not enable we don't save the memory */
      if (tracer::pintool::snapshot.isLocked())
        return;

      /* Mutex */
      PIN_LockClient();

      for (triton::uint32 i = 0; i < writeSize ; i++)
        tracer::pintool::snapshot.addModification(mem+i, *(reinterpret_cast<triton::uint8*>(mem+i)));

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Callback at a routine entry */
    static void callbackRoutineEntry(CONTEXT* ctx, THREADID threadId, PyObject* callback) {
      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex lock */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::routine(threadId, callback);

      /* Mutex unlock */
      PIN_UnlockClient();
    }


    /* Callback at a routine exit */
    static void callbackRoutineExit(CONTEXT* ctx, THREADID threadId, PyObject* callback) {
      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex lock */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::routine(threadId, callback);

      /* Mutex unlock */
      PIN_UnlockClient();
    }


    /* Callback at the end of the execution */
    static void callbackFini(int, VOID *) {
      /* Execute the Python callback */
      tracer::pintool::callbacks::fini();
    }


    /* Callback at a syscall entry */
    static void callbackSyscallEntry(unsigned int threadId, CONTEXT* ctx, SYSCALL_STANDARD std, void* v) {
      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::syscallEntry(threadId, std);

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Callback at the syscall exit */
    static void callbackSyscallExit(unsigned int threadId, CONTEXT* ctx, SYSCALL_STANDARD std, void* v) {
      if (!tracer::pintool::analysisTrigger.getState() || threadId != tracer::pintool::options::targetThreadId)
      /* Analysis locked */
        return;

      /* Mutex */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::syscallExit(threadId, std);

      /* Mutex */
      PIN_UnlockClient();
    }


    /*
     * Callback when an image is loaded.
     * This callback must be called even outside the range analysis.
     */
    static void callbackImageLoad(IMG img) {
      /* Mutex */
      PIN_LockClient();

      /* Collect image information */
      std::string imagePath     = IMG_Name(img);
      triton::__uint imageBase  = IMG_LowAddress(img);
      triton::__uint imageSize  = (IMG_HighAddress(img) + 1) - imageBase;

      /* Execute the Python callback */
      tracer::pintool::callbacks::imageLoad(imagePath, imageBase, imageSize);

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Callback when a signals occurs */
    static bool callbackSignals(unsigned int threadId, int sig, CONTEXT* ctx, bool hasHandler, const EXCEPTION_INFO* pExceptInfo, void* v) {
      /* Mutex */
      PIN_LockClient();

      /* Update CTX */
      tracer::pintool::context::lastContext = ctx;

      /* Execute the Python callback */
      tracer::pintool::callbacks::signals(threadId, sig);

      /* Mutex */
      PIN_UnlockClient();

      /*
       * We must exit. If you don't want to exit,
       * you must use the restoreSnapshot() function.
       */
      exit(0);

      return true;
    }


    /* Image instrumentation */
    static void IMG_Instrumentation(IMG img, void *v) {
      /* Lock / Unlock the Analysis from a Entry point */
      if (tracer::pintool::options::startAnalysisFromEntry) {
        tracer::pintool::options::startAnalysisFromEntry = false;
        /* IMG_LoadOffset(img) + IMG_Entry(img) for PIE binaries (see #524) */
        tracer::pintool::options::startAnalysisFromAddress.insert(IMG_LoadOffset(img) + IMG_Entry(img));
      }

      /* Lock / Unlock the Analysis from a symbol */
      if (tracer::pintool::options::startAnalysisFromSymbol != nullptr){

        RTN targetRTN = RTN_FindByName(img, tracer::pintool::options::startAnalysisFromSymbol);
        if (RTN_Valid(targetRTN)) {
          RTN_Open(targetRTN);

          RTN_InsertCall(targetRTN,
              IPOINT_BEFORE,
              (AFUNPTR) toggleWrapper,
              IARG_BOOL, true,
              IARG_END);

          RTN_InsertCall(targetRTN,
              IPOINT_AFTER,
              (AFUNPTR) toggleWrapper,
              IARG_BOOL, false,
              IARG_END);

          RTN_Close(targetRTN);
        }
      }

      /* Callback on routine entry */
      std::map<const char *, PyObject *>::iterator it;
      for (it = tracer::pintool::options::callbackRoutineEntry.begin(); it != tracer::pintool::options::callbackRoutineEntry.end(); it++) {
        RTN targetRTN = RTN_FindByName(img, it->first);
        if (RTN_Valid(targetRTN)){
          RTN_Open(targetRTN);
          RTN_InsertCall(targetRTN, IPOINT_BEFORE, (AFUNPTR)callbackRoutineEntry, IARG_CONTEXT, IARG_THREAD_ID, IARG_PTR, it->second, IARG_END);
          RTN_Close(targetRTN);
        }
      }

      /* Callback on routine exit */
      for (it = tracer::pintool::options::callbackRoutineExit.begin(); it != tracer::pintool::options::callbackRoutineExit.end(); it++) {
        RTN targetRTN = RTN_FindByName(img, it->first);
        if (RTN_Valid(targetRTN)){
          RTN_Open(targetRTN);
          RTN_InsertCall(targetRTN, IPOINT_AFTER, (AFUNPTR)callbackRoutineExit, IARG_CONTEXT, IARG_THREAD_ID, IARG_PTR, it->second, IARG_END);
          RTN_Close(targetRTN);
        }
      }

      /*
       * Callback when a new image is loaded.
       * This callback must be called even outside the range analysis.
       */
      if (IMG_Valid(img))
        tracer::pintool::callbackImageLoad(img);
    }


    /* Check if the analysis must be unlocked */
    static bool checkUnlockAnalysis(triton::__uint address) {
      if (tracer::pintool::options::targetThreadId != -1)
        return false;

      /* Unlock the analysis at the entry point from symbol */
      if (tracer::pintool::options::startAnalysisFromSymbol != nullptr) {
        if ((RTN_FindNameByAddress(address) == tracer::pintool::options::startAnalysisFromSymbol)) {
          tracer::pintool::options::targetThreadId = PIN_ThreadId();
          tracer::pintool::toggleWrapper(true);
          return true;
        }
      }

      /* Unlock the analysis at the entry point from address */
      else if (tracer::pintool::options::startAnalysisFromAddress.find(address) != tracer::pintool::options::startAnalysisFromAddress.end()) {
          tracer::pintool::options::targetThreadId = PIN_ThreadId();
          tracer::pintool::toggleWrapper(true);
          return true;
      }

      /* Unlock the analysis at the entry point from offset */
      else if (tracer::pintool::options::startAnalysisFromOffset.find(tracer::pintool::getInsOffset(address)) != tracer::pintool::options::startAnalysisFromOffset.end()) {
          tracer::pintool::options::targetThreadId = PIN_ThreadId();
          tracer::pintool::toggleWrapper(true);
          return true;
      }
      return false;
    }


    /* Check if the instruction is blacklisted */
    static bool instructionBlacklisted(triton::__uint address) {
      std::list<const char *>::iterator it;
      for (it = tracer::pintool::options::imageBlacklist.begin(); it != tracer::pintool::options::imageBlacklist.end(); it++) {
        if (strstr(tracer::pintool::getImageName(address).c_str(), *it))
          return true;
      }
      return false;
    }


    /* Check if the instruction is whitelisted */
    static bool instructionWhitelisted(triton::__uint address) {
      std::list<const char *>::iterator it;

      /* If there is no whitelist -> jit everything */
      if (tracer::pintool::options::imageWhitelist.empty())
        return true;

      for (it = tracer::pintool::options::imageWhitelist.begin(); it != tracer::pintool::options::imageWhitelist.end(); it++) {
        if (strstr(tracer::pintool::getImageName(address).c_str(), *it))
          return true;
      }

      return false;
    }


    /* Trace instrumentation */
    static void TRACE_Instrumentation(TRACE trace, VOID *v) {

      for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)) {
        for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {

          /* Check if the analysis me be unlocked */
          tracer::pintool::checkUnlockAnalysis(INS_Address(ins));

          if (!tracer::pintool::analysisTrigger.getState())
          /* Analysis locked */
            continue;

          if (tracer::pintool::instructionBlacklisted(INS_Address(ins)) == true || tracer::pintool::instructionWhitelisted(INS_Address(ins)) == false)
          /* Insruction blacklisted */
            continue;

          /* Prepare the Triton's instruction */
          triton::arch::Instruction* tritonInst = new triton::arch::Instruction();

          /* Save memory read1 informations */
          if (INS_IsMemoryRead(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)saveMemoryAccess,
              IARG_PTR, tritonInst,
              IARG_MEMORYREAD_EA,
              IARG_MEMORYREAD_SIZE,
              IARG_END);
          }

          /* Save memory read2 informations */
          if (INS_HasMemoryRead2(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)saveMemoryAccess,
              IARG_PTR, tritonInst,
              IARG_MEMORYREAD2_EA,
              IARG_MEMORYREAD_SIZE,
              IARG_END);
          }

          /* Callback before */
          INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)callbackBefore,
            IARG_PTR, tritonInst,
            IARG_INST_PTR,
            IARG_UINT32, INS_Size(ins),
            IARG_CONTEXT,
            IARG_THREAD_ID,
            IARG_END);

          /* Callback after */
          /* Syscall after context must be catcher with INSERT_POINT.SYSCALL_EXIT */
          if (INS_IsSyscall(ins) == false) {
            IPOINT where = IPOINT_AFTER;
            if (INS_HasFallThrough(ins) == false)
              where = IPOINT_TAKEN_BRANCH;
            INS_InsertCall(ins, where, (AFUNPTR)callbackAfter, IARG_PTR, tritonInst, IARG_CONTEXT, IARG_THREAD_ID, IARG_END);
          }

          /* I/O memory monitoring for snapshot */
          if (INS_OperandCount(ins) > 1 && INS_MemoryOperandIsWritten(ins, 0)) {
            INS_InsertCall(
              ins, IPOINT_BEFORE, (AFUNPTR)callbackSnapshot,
              IARG_MEMORYOP_EA, 0,
              IARG_UINT32, INS_MemoryWriteSize(ins),
              IARG_END);
          }

        }
      }
    }


    /* Usage function */
    static triton::sint32 Usage() {
      std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;
      return -1;
    }


    /* The pintool's entry point */
    int main(int argc, char *argv[]) {
      PIN_InitSymbols();
      PIN_SetSyntaxIntel();
      if(PIN_Init(argc, argv))
          return Usage();

      /* Init the Triton module */
      triton::bindings::python::inittriton();

      /* Image callback */
      IMG_AddInstrumentFunction(IMG_Instrumentation, nullptr);

      /* Instruction callback */
      TRACE_AddInstrumentFunction(TRACE_Instrumentation, nullptr);

      /* End instrumentation callback */
      PIN_AddFiniFunction(callbackFini, nullptr);

      /* Syscall entry callback */
      PIN_AddSyscallEntryFunction(callbackSyscallEntry, nullptr);

      /* Syscall exit callback */
      PIN_AddSyscallExitFunction(callbackSyscallExit, nullptr);

      ///* Signals callback */
      PIN_InterceptSignal(SIGHUP,  callbackSignals, nullptr);
      PIN_InterceptSignal(SIGINT,  callbackSignals, nullptr);
      PIN_InterceptSignal(SIGQUIT, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGILL,  callbackSignals, nullptr);
      PIN_InterceptSignal(SIGABRT, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGFPE,  callbackSignals, nullptr);
      PIN_InterceptSignal(SIGKILL, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGSEGV, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGPIPE, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGALRM, callbackSignals, nullptr);
      PIN_InterceptSignal(SIGTERM, callbackSignals, nullptr);

      /* Exec the Pin's python bindings */
      tracer::pintool::initBindings();
      tracer::pintool::execScript(KnobPythonModule.Value().c_str());

      return 0;
    }

  };
};


/* namespace trampoline */
int main(int argc, char *argv[]) {
  return tracer::pintool::main(argc, argv);
}

