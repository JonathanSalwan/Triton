//! \file
/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <csignal>
#include <cstring>
#include <iostream>
#include <stdexcept>
#include <string>

#include <pin.H>

/* libTriton */
#include <api.hpp>
#include <pythonBindings.hpp>

/* Pintool */
#include "bindings.hpp"
#include "context.hpp"
#include "trigger.hpp"
#include "utils.hpp"



namespace tracer {
  namespace pintool {

    //! Pin options: -script
    KNOB<std::string> KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

    //! Lock / Unlock InsertCall
    Trigger analysisTrigger = Trigger();


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
      tritonInst->setOpcodes(addr, size);
      tritonInst->setAddress(reinterpret_cast<triton::__uint>(addr));
      tritonInst->setThreadId(reinterpret_cast<triton::uint32>(threadId));

      /* Setup the concrete context */
      tracer::pintool::setupContextRegister(tritonInst, ctx);

      /* Trust operands */
      for (auto op = tritonInst->operands.begin(); op != tritonInst->operands.end(); op++)
        op->setTrust(true);

      /* Execute the Python callback */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::beforeIRProc(tritonInst);
      else
        tracer::pintool::context::mustBeExecuted = false;

      /* Process the Triton instruction */
      triton::api.processing(*tritonInst);

      /* Execute the Python callback */
      if (tracer::pintool::context::mustBeExecuted == false)
        tracer::pintool::callbacks::before(tritonInst);
      else
        tracer::pintool::context::mustBeExecuted = false;

      /* Some configurations must be applied after processing */
      tracer::pintool::callbacks::postProcessing(tritonInst, threadId);

      /* Check if we must execute a new context */
      if (tracer::pintool::context::mustBeExecuted == true)
        tracer::pintool::context::executeContext();

      /* Untrust operands */
      for (auto op = tritonInst->operands.begin(); op != tritonInst->operands.end(); op++)
        op->setTrust(false);

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

      /* Check if we must execute a new context */
      if (tracer::pintool::context::mustBeExecuted == true)
        tracer::pintool::context::executeContext();

      /* Mutex */
      PIN_UnlockClient();
    }


    /* Save the memory access into the Triton instruction */
    static void saveMemoryAccess(triton::arch::Instruction* tritonInst, triton::__uint addr, triton::uint32 size) {
      switch (size) {
        case 1:  tritonInst->updateContext(triton::arch::MemoryOperand(addr, size, *((triton::uint8 *)addr))); break;
        case 2:  tritonInst->updateContext(triton::arch::MemoryOperand(addr, size, *((triton::uint16 *)addr))); break;
        case 4:  tritonInst->updateContext(triton::arch::MemoryOperand(addr, size, *((triton::uint32 *)addr))); break;
        case 8:  tritonInst->updateContext(triton::arch::MemoryOperand(addr, size, *((triton::uint64 *)addr))); break;
        case 16: tritonInst->updateContext(triton::arch::MemoryOperand(addr, size, *((triton::uint128 *)addr))); break;
      }
    }


    /* Callback to save bytes for the snapshot engine */
    static void callbackSnapshot(triton::__uint mem, triton::uint32 writeSize) {
      if (!tracer::pintool::analysisTrigger.getState())
      /* Analysis locked */
        return;

      /* If the snapshot is not enable we don't save the memory */
      //if (ap.isSnapshotLocked())
      //  return;

      /* Mutex */
      PIN_LockClient();

      //triton::uint32 i = 0;
      //for (; i < writeSize ; i++)
      //  ap.addSnapshotModification(mem+i, *(reinterpret_cast<uint8*>(mem+i)));

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

      /* Collect image's informations */
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
        tracer::pintool::options::startAnalysisFromAddr.insert(IMG_Entry(img));
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
      else if (tracer::pintool::options::startAnalysisFromAddr.find(address) != tracer::pintool::options::startAnalysisFromAddr.end()) {
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

          /* Save memory write informations */
          if (INS_IsMemoryWrite(ins)) {
            INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)saveMemoryAccess,
              IARG_PTR, tritonInst,
              IARG_MEMORYWRITE_EA,
              IARG_MEMORYWRITE_SIZE,
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
          /* Syscall after context must be catcher with CALLBACK.SYSCALL_EXIT */
          if (INS_IsSyscall(ins) == false) {
            IPOINT where = IPOINT_AFTER;
            if (INS_HasFallThrough(ins) == false)
              where = IPOINT_TAKEN_BRANCH;
            INS_InsertCall(ins, where, (AFUNPTR)callbackAfter, IARG_PTR, tritonInst, IARG_CONTEXT, IARG_THREAD_ID, IARG_END);
          }

          ///* I/O memory monitoring for snapshot */
          //if (INS_OperandCount(ins) > 1 && INS_MemoryOperandIsWritten(ins, 0)) {
          //  INS_InsertCall(
          //    ins, IPOINT_BEFORE, (AFUNPTR)callbackSnapshot,
          //    IARG_MEMORYOP_EA, 0,
          //    IARG_UINT32, INS_MemoryWriteSize(ins),
          //    IARG_END);
          //}

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
      if (!tracer::pintool::execScript(KnobPythonModule.Value().c_str()))
        throw std::runtime_error("tracer::pintool::main(): Script file can't be found.");

      return 0;
    }

  };
};


/* namespace trampoline */
int main(int argc, char *argv[]) {
  return tracer::pintool::main(argc, argv);
}

