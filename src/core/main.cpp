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
#include <boost/filesystem.hpp>

using boost::filesystem::absolute;
using boost::filesystem::path;

/* Pin options: -script */
KNOB<std::string>   KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

AnalysisProcessor   ap;
Trigger             analysisTrigger = Trigger();
ProcessingPyConf    processingPyConf(&ap, &analysisTrigger);



static void callbackBefore(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea, THREADID threadId)
{
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

  /* Python callback before IR processing */
  processingPyConf.callbackBeforeIRProc(irb, &ap);

  Inst *inst = irb->process(ap);
  ap.addInstructionToTrace(inst);

  /* Export some information from Irb to Inst */
  inst->setOpcode(irb->getOpcode());
  inst->setOpcodeCategory(irb->getOpcodeCategory());
  inst->setOperands(irb->getOperands());

  /* Python callback before instruction processing */
  processingPyConf.callbackBefore(inst, &ap);

  /* Mutex */
  ap.unlock();
}


static void callbackAfter(CONTEXT *ctx, THREADID threadId)
{
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
  ap.incNumberOfBranchesTaken(inst->isBranch());

  /* Python callback after instruction processing */
  processingPyConf.callbackAfter(inst, &ap);

  /* Mutex */
  ap.unlock();
}


static void callbackSnapshot(uint64 mem, uint32 writeSize)
{
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

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
}


static void TRACE_Instrumentation(TRACE trace, VOID *programName)
{
  boost::filesystem::path pname(reinterpret_cast<char*>(programName));

  for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)){
    for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {

      /* ---- Speed up process ---- */
      IMG currentImgName = IMG_FindByAddress(INS_Address(ins));
      if (!IMG_Valid(currentImgName))
        continue;

      boost::filesystem::path pcurrent(IMG_Name(currentImgName));
      if (!analysisTrigger.getState() && strcmp(pname.leaf().c_str(), pcurrent.leaf().c_str()))
        continue;
      /* ---- End of speed up process ---- */

      IRBuilder *irb = createIRBuilder(ins);

      /* Callback before */
      if (INS_MemoryOperandCount(ins) > 0)
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callbackBefore,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, true,
            IARG_MEMORYOP_EA, 0,
            IARG_THREAD_ID,
            IARG_END);
      else
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callbackBefore,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, false,
            IARG_ADDRINT, 0,
            IARG_THREAD_ID,
            IARG_END);

      /* Callback after */
      /* Syscall after context must be catcher with IDREF.CALLBACK.SYSCALL_EXIT */
      if (INS_IsSyscall(ins) == false){
        IPOINT where = IPOINT_AFTER;
        if (INS_HasFallThrough(ins) == false)
          where = IPOINT_TAKEN_BRANCH;
        INS_InsertCall(ins, where, (AFUNPTR)callbackAfter, IARG_CONTEXT, IARG_THREAD_ID, IARG_END);
      }

      /* I/O memory monitoring for snapshot */
      if (INS_OperandCount(ins) > 1 && INS_MemoryOperandIsWritten(ins, 0))
        INS_InsertCall(
          ins, IPOINT_BEFORE, (AFUNPTR)callbackSnapshot,
          IARG_MEMORYOP_EA, 0,
          IARG_UINT32, INS_MemoryWriteSize(ins),
          IARG_END);

    }
  }
}


static void toggleWrapper(bool flag)
{
  ap.lock();
  analysisTrigger.update(flag);
  ap.unlock();
}


static void callbackRoutineEntry(THREADID threadId, PyObject *callback)
{
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  ap.lock();
  processingPyConf.callbackRoutine(threadId, callback);
  ap.unlock();
}


static void callbackRoutineExit(THREADID threadId, PyObject *callback)
{
  if (!analysisTrigger.getState())
  /* Analysis locked */
    return;

  ap.lock();
  processingPyConf.callbackRoutine(threadId, callback);
  ap.unlock();
}


static void IMG_Instrumentation(IMG img, VOID *)
{
  /* Lock / Unlock the Analysis */
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
  for (it = PyTritonOptions::callbackRoutineEntry.begin(); it != PyTritonOptions::callbackRoutineEntry.end(); it++){
    RTN targetRTN = RTN_FindByName(img, it->first);
    if (RTN_Valid(targetRTN)){
      RTN_Open(targetRTN);
      RTN_InsertCall(targetRTN, IPOINT_BEFORE, (AFUNPTR)callbackRoutineEntry, IARG_THREAD_ID, IARG_PTR, it->second, IARG_END);
      RTN_Close(targetRTN);
    }
  }

  /* Callback on routine exit */
  for (it = PyTritonOptions::callbackRoutineExit.begin(); it != PyTritonOptions::callbackRoutineExit.end(); it++){
    RTN targetRTN = RTN_FindByName(img, it->first);
    if (RTN_Valid(targetRTN)){
      RTN_Open(targetRTN);
      RTN_InsertCall(targetRTN, IPOINT_AFTER, (AFUNPTR)callbackRoutineExit, IARG_THREAD_ID, IARG_PTR, it->second, IARG_END);
      RTN_Close(targetRTN);
    }
  }
}


/* Callback at the end of the execution */
static void Fini(INT32, VOID *)
{
  /* Python callback at the end of execution */
  processingPyConf.callbackFini();

  /* End of Python */
  Py_Finalize();
}


/* Callback at the syscall entry */
static void callbackSyscallEntry(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v)
{
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
static void callbackSyscallExit(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, VOID *v)
{
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


/* Callback when a signals occurs */
static bool callbackSignals(THREADID threadId, sint32 sig, CONTEXT *ctx, bool hasHandler, const EXCEPTION_INFO *pExceptInfo, void *v)
{
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
static void callbackThreadEntry(THREADID threadId, CONTEXT *ctx, sint32 flags, void *v)
{
  /* Mutex */
  ap.lock();

  // TODO #30: Create a map entry of (thread -> {taintEngine, symEngine}).

  /* Mutex */
  ap.unlock();
}


/* Callback when a thread is destroyed */
static void callbackThreadExit(THREADID threadId, const CONTEXT *ctx, sint32 flags, void *v)
{
  /* Mutex */
  ap.lock();

  // TODO #30: Destroy the map entry corresponding to the threadId.

  /* Mutex */
  ap.unlock();
}


/*
 * Usage function if Pin fail to start.
 * Display the help message.
 */
static sint32 Usage()
{
  std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;
  return -1;
}


/* Get the name of the target binary */
static char *getProgramName(char *argv[])
{
  uint64 offset;
  for (offset = 0; argv[offset]; offset++){
    if (!strcmp(argv[offset], "--") && argv[offset+1])
      return argv[offset+1];
  }
  return nullptr;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  PIN_SetSyntaxIntel();
  if(PIN_Init(argc, argv))
      return Usage();

  /* Init Python Bindings */
  initBindings();

  /* Image callback */
  IMG_AddInstrumentFunction(IMG_Instrumentation, nullptr);

  /* Instruction callback */
  TRACE_AddInstrumentFunction(TRACE_Instrumentation, getProgramName(argv));

  /* End instrumentation callback */
  PIN_AddFiniFunction(Fini, nullptr);

  /* Syscall entry callback */
  PIN_AddSyscallEntryFunction(callbackSyscallEntry, nullptr);

  /* Syscall exit callback */
  PIN_AddSyscallExitFunction(callbackSyscallExit, nullptr);

  /* Signals callback */
  PIN_InterceptSignal(SIGFPE,  callbackSignals, nullptr); /* Floating point exception */
  PIN_InterceptSignal(SIGILL,  callbackSignals, nullptr); /* Illegal Instruction */
  PIN_InterceptSignal(SIGKILL, callbackSignals, nullptr); /* Kill signal */
  PIN_InterceptSignal(SIGPIPE, callbackSignals, nullptr); /* Broken pipe: write to pipe with no readers */
  PIN_InterceptSignal(SIGSEGV, callbackSignals, nullptr); /* Invalid memory reference */

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

