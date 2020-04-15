//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the Apache License 2.0.
*/

/* libTriton */
#include <triton/pythonBindings.hpp>
#include <triton/api.hpp>

#include <csignal>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>

#include <pin.H>

/* Pintool */
#include "api.hpp"
#include "bindings.hpp"
#include "context.hpp"
#include "snapshot.hpp"
#include "trigger.hpp"
#include "utils.hpp"



/*! \page Tracer_page Pintool tracer
    \brief [**internal**] All information about how to plug a tracer.
\tableofcontents
\section Tracer_description Description
<hr>

<p align="center"><img src="https://triton.quarkslab.com/files/triton_v06_architecture.png"/></p>

The Triton library allows you to plug any kind of tracers. E.g: Pin, Valgrind and even a database.
To use the `libTriton`, your tracer must provide two kinds of information at each program point:

- The current opcode executed.
- A state context (register and memory).

Based on these two information, Triton will translate the control flow into \ref py_AstNode_page. As an example, let assume that you have dumped
a trace into a database with all registers state and memory access - these information may come from Valgrind, Pin, Qemu or whatever. The following Python code
uses the Triton's API to build the semantics of each instruction stored in the database.

~~~~~~~~~~~~~{.py}
#!/usr/bin/env python2
## -*- coding: utf-8 -*-

import  sys
import  struct

from triton  import ARCH, Instruction, MemoryAccess
from database import Manager

unpack_size = {1: 'B', 2: 'H', 4: 'I', 8: 'Q', 16: 'QQ'}

if __name__ == '__main__':
    # Get the current Triton context
    ctxt = getTritonContext()

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

        # Setup opcode
        inst.setOpcode(opcode)

        # Setup Address
        inst.setAddress(regs['rip'])

        # Update concrete register state
        ctxt.setConcreteRegisterValue(ctxt.registers.rax,    regs['rax'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rbx,    regs['rbx'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rcx,    regs['rcx'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rdx,    regs['rdx'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rdi,    regs['rdi'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rsi,    regs['rsi'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rbp,    regs['rbp'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rsp,    regs['rsp'])
        ctxt.setConcreteRegisterValue(ctxt.registers.rip,    regs['rip'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r8,     regs['r8'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r9,     regs['r9'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r10,    regs['r10'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r11,    regs['r11'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r12,    regs['r12'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r13,    regs['r13'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r14,    regs['r14'])
        ctxt.setConcreteRegisterValue(ctxt.registers.r15,    regs['r15'])
        ctxt.setConcreteRegisterValue(ctxt.registers.eflags, regs['eflags'])
        ctxt.setConcreteRegisterValue(ctxt.registers.fs,     regs['fs']) # The mapped base address
        ctxt.setConcreteRegisterValue(ctxt.registers.gs,     regs['gs']) # The mapped base address

        # Update concrete memory access
        accesses = db.get_memory_access_from_inst_id(inst_id)

        # Update memory access
        for access in accesses:
            if access['kind'] == 'R':
                address = access['addr']
                data    = access['data']
                value   = struct.unpack(unpack_size[len(data)], data)[0]
                ctxt.setConcreteMemoryValue(MemoryAccess(address, len(data), value))

        # Process everything (build IR, spread taint, perform simplification, ...)
        ctxt.processing(inst)

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

The database connection is a pure example to show how to interact with the Triton API. As Triton is written in `C++`, you can directly
create your Triton instruction inside a DBI engine (like Pin or Valgrind). According to your tracer, you can refer to the [Python](https://triton.quarkslab.com/documentation/doxygen/py_triton_page.html)
or the [C++](https://triton.quarkslab.com/documentation/doxygen/classtriton_1_1API.html) API.

\section Tracer_pintool The Triton's pintool
<hr>

This project is shippied with a pintool as tracer. Basically, you can add callbacks, get current registers and memory values, inject values into registers and memory,
start and stop analysis at specific points, select what images are jitted or not, interact with the Triton API and many more... All information about the pintool API
is describe at this following page \ref pintool_py_api. Below, some examples.

<hr>
\subsection Tracer_pintool_example_1 Example - Display IR

\include pin/ir.py

<hr>
\subsection Tracer_pintool_example_2 Example - Runtime Memory Tainting

\include pin/runtime_memory_tainting.py

<hr>
\subsection Tracer_pintool_example_3 Example - Runtime Register Modification

\include pin/runtime_register_modification.py

<hr>
\subsection Tracer_pintool_example_4 Example - Blacklist images

\include pin/blacklist.py

<hr>
\subsection Tracer_pintool_example_5 Example - Callback on image

\include pin/callback_image.py

<hr>
\subsection Tracer_pintool_example_6 Example - Callback on routine

\include pin/callback_routine.py

<hr>
\subsection Tracer_pintool_example_7 Example - Callback on signals

\include pin/callback_signals.py

<hr>
\subsection Tracer_pintool_example_8 Example - Callback on syscalls

\include pin/callback_syscall.py

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
      tritonInst->clear();
      tritonInst->setOpcode(addr, size);
      tritonInst->setAddress(reinterpret_cast<triton::__uint>(addr));
      tritonInst->setThreadId(reinterpret_cast<triton::uint32>(threadId));

      /* Disassemble the instruction */
      tracer::pintool::api.disassembly(*tritonInst);

      /* Execute the Python callback before the IR processing */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::beforeIRProc(tritonInst);
      else
        tracer::pintool::context::mustBeExecuted = false;

      /* Check if we must execute a new context */
      if (tracer::pintool::context::mustBeExecuted == true) {
        tritonInst->clear();
        tracer::pintool::context::executeContext();
      }

      /* Synchronize gliches between Pintool and libTriton */
      tracer::pintool::context::synchronizeContext();

      /* Process the IR and spread taint only if one of both engines are enabled */
      if (tracer::pintool::api.isTaintEngineEnabled() || tracer::pintool::api.isSymbolicEngineEnabled())
        tracer::pintool::api.buildSemantics(*tritonInst);

      /* Execute the Python callback */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::before(tritonInst);

      /* Check if we must restore the snapshot */
      if (tracer::pintool::snapshot.mustBeRestored() == true) {
        tritonInst->clear();
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
      tritonInst->clear();

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

      auto mem   = triton::arch::MemoryAccess(addr, size);
      auto value = tracer::pintool::context::getCurrentMemoryValue(addr, size);

      tracer::pintool::api.getCpuInstance()->setConcreteMemoryValue(mem, value);

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
      for (const char* name: tracer::pintool::options::imageBlacklist) {
        if (strstr(tracer::pintool::getImageName(address).c_str(), name))
          return true;
      }
      return false;
    }


    /* Check if the instruction is whitelisted */
    static bool instructionWhitelisted(triton::__uint address) {
      /* If there is no whitelist -> jit everything */
      if (tracer::pintool::options::imageWhitelist.empty())
        return true;

      for (const char* name: tracer::pintool::options::imageWhitelist) {
        if (strstr(tracer::pintool::getImageName(address).c_str(), name))
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


    //! The pintool's entry point
    int main(int argc, char* argv[]) {
      PIN_InitSymbols();
      PIN_SetSyntaxIntel();
      if(PIN_Init(argc, argv))
        return Usage();

      /* Define Triton architecure */
      if (sizeof(void*) == triton::size::qword)
        tracer::pintool::api.setArchitecture(triton::arch::ARCH_X86_64);
      else
        tracer::pintool::api.setArchitecture(triton::arch::ARCH_X86);

      /* During the execution provide concrete values only if Triton needs them - cf #376, #632 and #645 */
      tracer::pintool::api.addCallback(tracer::pintool::context::needConcreteMemoryValue);

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

      /* Signals callback */
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
      PIN_InterceptSignal(SIGBUS,  callbackSignals, nullptr);

      /* Init the triton and pintool python module */
      PyImport_AppendInittab("pintool", tracer::pintool::initpintool);
      #if IS_PY3
      PyImport_AppendInittab("triton",  triton::bindings::python::PyInit_triton);
      #else
      PyImport_AppendInittab("triton",  triton::bindings::python::inittriton);
      #endif

      /* Init python */
      Py_Initialize();

      /* Init the pintool python arguments */
      tracer::pintool::initPythonArgs(argc, argv);

      /* Exec the Pin's python bindings */
      tracer::pintool::execScript(KnobPythonModule.Value().c_str());

      return 0;
    }

  };
};


//! namespace trampoline
int main(int argc, char *argv[]) {
  return tracer::pintool::main(argc, argv);
}
