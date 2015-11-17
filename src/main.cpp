/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <csignal>
#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <vector>

#include <pin.H>

#include <AnalysisProcessor.h>
#include <IRBuilder.h>
#include <IRBuilderFactory.h>
#include <Inst.h>
#include <PINContextHandler.h>
#include <ProcessingPyConf.h>
#include <Trigger.h>

/* Pin options: -script */
KNOB<std::string>   KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

AnalysisProcessor   ap;
Trigger             analysisTrigger = Trigger();
ProcessingPyConf    processingPyConf(&ap, &analysisTrigger);



static void toggleWrapper(bool flag) {
  ap.lock();
  analysisTrigger.update(flag);
  ap.unlock();
}


/* Callback before instruction processing */
static void callbackBefore(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea, BOOL isBranchTaken, ADDRINT branchTargetAddress, THREADID threadId) {
  /* Some configurations must be applied before processing */
  processingPyConf.applyConfBeforeProcessing(irb);

  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex */
  ap.lock();

  if (hasEA)
    irb->setup(ea);

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Setup Information into Irb */
  irb->setThreadID(ap.getThreadID());
  irb->setBranchTaken(isBranchTaken);
  irb->setBranchTargetAddress(branchTargetAddress);

  /* Python callback before IR processing */
  processingPyConf.callbackBeforeIRProc(irb, &ap);

  Inst *inst = irb->process(ap);
  ap.addInstructionToTrace(inst);

  /* Export some information from Irb to Inst */
  inst->setNextAddress(irb->getNextAddress());
  inst->setOpcode(irb->getOpcode());
  inst->setOpcodeCategory(irb->getOpcodeCategory());
  inst->setOperands(irb->getOperands());
  inst->setBranchTaken(irb->isBranchTaken());
  inst->setBranchTargetAddress(irb->getBranchTargetAddress());

  /* Python callback before instruction processing */
  processingPyConf.callbackBefore(inst, &ap);

  /* Some configurations must be applied after processing */
  processingPyConf.applyConfAfterProcessing(irb);

  /* Mutex */
  ap.unlock();
}


/* Callback after instruction processing */
static void callbackAfter(CONTEXT *ctx, THREADID threadId) {
  Inst *inst;

  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Get the last instruction */
  inst = ap.getLastInstruction();

  /* Update statistics */
  #ifndef LIGHT_VERSION
  ap.incNumberOfBranchesTaken(inst->isBranch());
  #endif

  /* Python callback after instruction processing */
  processingPyConf.callbackAfter(inst, &ap);

  /* Some configurations must be applied after processing */
  processingPyConf.applyConfAfterProcessing(inst);

  /* Free unused instructions */
  ap.clearTrace();

  /* Mutex */
  ap.unlock();
}


/* Callback to save bytes for the snapshot engine */
static void callbackSnapshot(reg_size mem, uint32 writeSize) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  #ifndef LIGHT_VERSION

  /* If the snapshot is not enable we don't save the memory */
  if (ap.isSnapshotLocked())
    return;

  /* Mutex */
  ap.lock();

  uint32 i = 0;
  for (; i < writeSize ; i++)
    ap.addSnapshotModification(mem+i, *(reinterpret_cast<uint8*>(mem+i)));

  /* Mutex */
  ap.unlock();

  #endif /* LIGHT_VERSION */
}


/* Callback at a routine entry */
static void callbackRoutineEntry(CONTEXT *ctx, THREADID threadId, PyObject *callback) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex lock */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  processingPyConf.callbackRoutine(threadId, callback);

  /* Mutex unlock */
  ap.unlock();
}


/* Callback at a routine exit */
static void callbackRoutineExit(CONTEXT *ctx, THREADID threadId, PyObject *callback) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex lock */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  processingPyConf.callbackRoutine(threadId, callback);

  /* Mutex unlock */
  ap.unlock();
}


/* Callback at the end of the execution */
static void callbackFini(INT32, VOID *) {
  /* Python callback at the end of execution */
  processingPyConf.callbackFini();

  /* End of Python */
  Py_Finalize();
}


/* Callback at a syscall entry */
static void callbackSyscallEntry(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Python callback at the end of execution */
  processingPyConf.callbackSyscallEntry(threadId, std);

  /* Mutex */
  ap.unlock();
}


/* Callback at the syscall exit */
static void callbackSyscallExit(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  /* Mutex */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Python callback at the end of execution */
  processingPyConf.callbackSyscallExit(threadId, std);

  /* Mutex */
  ap.unlock();
}


/*
 * Callback when an image is loaded.
 * This callback must be called even outside the range analysis.
 */
static void callbackImageLoad(IMG img) {
  /* Mutex */
  ap.lock();

  /* Collect image's informations */
  string imagePath = IMG_Name(img);
  reg_size imageBase = IMG_LowAddress(img);
  reg_size imageSize = (IMG_HighAddress(img) + 1) - imageBase;

  /* Python callback for image loading */
  processingPyConf.callbackImageLoad(imagePath, imageBase, imageSize);

  /* Mutex */
  ap.unlock();
}


/* Callback when a signals occurs */
static bool callbackSignals(THREADID threadId, sint32 sig, CONTEXT *ctx, bool hasHandler, const EXCEPTION_INFO *pExceptInfo, void *v) {
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return false;

  /* Mutex */
  ap.lock();

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Python callback at the end of execution */
  processingPyConf.callbackSignals(threadId, sig);

  /* Mutex */
  ap.unlock();

  /*
   * We must exit. If you don't want to exit,
   * you must use the restoreSnapshot() function.
   */
  exit(0);

  return true;
}


/* Callback when a thread is created */
static void callbackThreadEntry(THREADID threadId, CONTEXT *ctx, sint32 flags, void *v) {
  /* Mutex */
  ap.lock();

  // TODO #30: Create a map entry of (thread -> {taintEngine, symEngine}).

  /* Mutex */
  ap.unlock();
}


/* Callback when a thread is destroyed */
static void callbackThreadExit(THREADID threadId, const CONTEXT *ctx, sint32 flags, void *v) {
  /* Mutex */
  ap.lock();

  // TODO #30: Destroy the map entry corresponding to the threadId.

  /* Mutex */
  ap.unlock();
}


/* Image instrumentation */
static void IMG_Instrumentation(IMG img, VOID *v) {
  /* Lock / Unlock the Analysis from a symbol */
  if (PyTritonOptions::startAnalysisFromSymbol != nullptr){

    RTN targetRTN = RTN_FindByName(img, PyTritonOptions::startAnalysisFromSymbol);
    if (RTN_Valid(targetRTN)){
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
  for (it = PyTritonOptions::callbackRoutineEntry.begin(); it != PyTritonOptions::callbackRoutineEntry.end(); it++) {
    RTN targetRTN = RTN_FindByName(img, it->first);
    if (RTN_Valid(targetRTN)){
      RTN_Open(targetRTN);
      RTN_InsertCall(targetRTN, IPOINT_BEFORE, (AFUNPTR)callbackRoutineEntry, IARG_CONTEXT, IARG_THREAD_ID, IARG_PTR, it->second, IARG_END);
      RTN_Close(targetRTN);
    }
  }

  /* Callback on routine exit */
  for (it = PyTritonOptions::callbackRoutineExit.begin(); it != PyTritonOptions::callbackRoutineExit.end(); it++) {
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
    callbackImageLoad(img);
}


/* Returns the base address of the instruction */
static reg_size getBaseAddress(reg_size address) {
  RTN rtn;
  SEC sec;
  IMG img;
  rtn = RTN_FindByAddress(address);
  if (RTN_Valid(rtn)) {
    sec = RTN_Sec(rtn);
    if (SEC_Valid(sec)) {
      img = SEC_Img(sec);
      if (IMG_Valid(img)) {
        return IMG_LowAddress(img);
      }
    }
  }
  return 0;
}


/* Returns the offset of the instruction */
static reg_size getInsOffset(reg_size address) {
  reg_size base = getBaseAddress(address);
  if (base == 0)
    return 0;
  return address - base;
}


/* Check if the analysis must be unlocked */
static bool checkUnlockAnalysis(reg_size address) {
  /* Unlock the analysis at the entry point from symbol */
  if (PyTritonOptions::startAnalysisFromSymbol != nullptr) {
    if ((RTN_FindNameByAddress(address) == PyTritonOptions::startAnalysisFromSymbol)) {
      toggleWrapper(true);
      return true;
    }
  }

  /* Unlock the analysis at the entry point from address */
  else if (PyTritonOptions::startAnalysisFromAddr.find(address) != PyTritonOptions::startAnalysisFromAddr.end()) {
      toggleWrapper(true);
      return true;
  }

  /* Unlock the analysis at the entry point from offset */
  else if (PyTritonOptions::startAnalysisFromOffset.find(getInsOffset(address)) != PyTritonOptions::startAnalysisFromOffset.end()) {
      toggleWrapper(true);
      return true;
  }
  return false;
}


/* Trace instrumentation */
static void TRACE_Instrumentation(TRACE trace, VOID *v) {

  std::list<IRBuilder *> irbList;

  for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)) {
    for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {

      /* Check if the analysis me be unlocked */
      checkUnlockAnalysis(INS_Address(ins));

      if (!analysisTrigger.getState())
      /* Analysis locked */
        continue;

      /* Prepare the IR builder */
      IRBuilder *irb = createIRBuilder(ins);

      /* Save irb from Pin cache */
      irbList.push_back(irb);

      /* Callback before */
      if (INS_MemoryOperandCount(ins) > 0)
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callbackBefore,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, true,
            IARG_MEMORYOP_EA, 0,
            IARG_BRANCH_TAKEN,
            IARG_BRANCH_TARGET_ADDR,
            IARG_THREAD_ID,
            IARG_END);
      else
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callbackBefore,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, false,
            IARG_ADDRINT, 0,
            IARG_BRANCH_TAKEN,
            IARG_BRANCH_TARGET_ADDR,
            IARG_THREAD_ID,
            IARG_END);

      /* Callback after */
      /* Syscall after context must be catcher with IDREF.CALLBACK.SYSCALL_EXIT */
      if (INS_IsSyscall(ins) == false) {
        IPOINT where = IPOINT_AFTER;
        if (INS_HasFallThrough(ins) == false)
          where = IPOINT_TAKEN_BRANCH;
        INS_InsertCall(ins, where, (AFUNPTR)callbackAfter, IARG_CONTEXT, IARG_THREAD_ID, IARG_END);
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
  /* Free unused irb */
  irbList.clear();
}


/*
 * Usage function if Pin fail to start.
 * Display the help message.
 */
static sint32 Usage() {
  std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;
  return -1;
}


int main(int argc, char *argv[]) {
  PIN_InitSymbols();
  PIN_SetSyntaxIntel();
  if(PIN_Init(argc, argv))
      return Usage();

  /* Init Python Bindings */
  initBindings();

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

  /* Threads callbacks */
  PIN_AddThreadStartFunction(callbackThreadEntry, nullptr);
  PIN_AddThreadFiniFunction(callbackThreadExit, nullptr);

  /* Exec the python bindings file */
  if (!execBindings(KnobPythonModule.Value().c_str())) {
    std::cerr << "Error: Script file can't be found!" << std::endl;
    exit(1);
  }

  return 0;
}

