#include <iostream>
#include <memory>
#include <sstream>
#include <stdexcept>
#include <vector>

#include "pin.H"

#include "AnalysisProcessor.h"
#include "IRBuilder.h"
#include "IRBuilderFactory.h"
#include "Inst.h"
#include "PINContextHandler.h"
#include "ProcessingPyConf.h"
#include "Trigger.h"


/* Pin options: -script */
KNOB<std::string>   KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

AnalysisProcessor   ap;
Trigger             analysisTrigger = Trigger();
ProcessingPyConf    processingPyConf(&ap, &analysisTrigger);



VOID callback(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea, THREADID threadId)
{
  /* Some configurations must be applied before processing */
  processingPyConf.applyConfBeforeProcessing(irb);

  if (!analysisTrigger.getState())
  // Analysis locked
    return;

  if (hasEA)
    irb->setup(ea);

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Setup Information into Irb */
  irb->setThreadID(ap.getThreadID());

  /* Python callback before instruction processing */
  processingPyConf.callbackBefore(irb, &ap);

  Inst *inst = irb->process(ap);
  ap.addInstructionToTrace(inst);

  /* Export some information from Irb to Inst */
  inst->setOpcode(irb->getOpcode());
  inst->setOpcodeCategory(irb->getOpcodeCategory());
  inst->setOperands(irb->getOperands());

  /* Update statistics */
  ap.incNumberOfBranchesTaken(inst->isBranch());

  /* Python callback after instruction processing */
  processingPyConf.callbackAfter(inst, &ap);
}


VOID TRACE_Instrumentation(TRACE trace, VOID *v)
{
  for (BBL bbl = TRACE_BblHead(trace); BBL_Valid(bbl); bbl = BBL_Next(bbl)){
    for (INS ins = BBL_InsHead(bbl); INS_Valid(ins); ins = INS_Next(ins)) {
      IRBuilder *irb = createIRBuilder(ins);

      if (INS_MemoryOperandCount(ins) > 0)
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callback,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, true,
            IARG_MEMORYOP_EA, 0,
            IARG_THREAD_ID,
            IARG_END);
      else
        INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR) callback,
            IARG_PTR, irb,
            IARG_CONTEXT,
            IARG_BOOL, false,
            IARG_ADDRINT, 0,
            IARG_THREAD_ID,
            IARG_END);
    }
  }
}


void toggleWrapper(bool flag)
{
  analysisTrigger.update(flag);
}


VOID IMG_Instrumentation(IMG img, VOID *)
{
  /* This callback is used to lock and target the analysis */
  /* Mainly used to target an area */
  if (PyTritonOptions::startAnalysisFromSymbol == NULL)
    return;
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


VOID Fini(INT32, VOID *)
{
  /* Python callback at the end of execution */
  processingPyConf.callbackFini();

  /* End of Python */
  Py_Finalize();
}


VOID callbackSyscallEntry(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, void *v)
{
  if (!analysisTrigger.getState())
  // Analysis locked
    return;

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Python callback at the end of execution */
  processingPyConf.callbackSyscallEntry(threadId, std);
}


VOID callbackSyscallExit(THREADID threadId, CONTEXT *ctx, SYSCALL_STANDARD std, void *v)
{
  if (!analysisTrigger.getState())
  // Analysis locked
    return;

  /* Update the current context handler */
  ap.updateCurrentCtxH(new PINContextHandler(ctx, threadId));

  /* Python callback at the end of execution */
  processingPyConf.callbackSyscallExit(threadId, std);
}


// Usage function if Pin fail to start.
// Display the help message.
INT32 Usage()
{
  std::cerr << KNOB_BASE::StringKnobSummary() << std::endl;
  return -1;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  PIN_SetSyntaxIntel();
  if(PIN_Init(argc, argv))
      return Usage();

  // Init Python Bindings
  initBindings();

  // Image callback
  IMG_AddInstrumentFunction(IMG_Instrumentation, NULL);

  // Instruction callback
  TRACE_AddInstrumentFunction(TRACE_Instrumentation, NULL);

  // End instrumentation callback
  PIN_AddFiniFunction(Fini, NULL);

  // Syscall entry callback
  PIN_AddSyscallEntryFunction(callbackSyscallEntry, 0);

  // Syscall exit callback
  PIN_AddSyscallExitFunction(callbackSyscallExit, 0);

  // Exec the python bindings file
  if (!execBindings(KnobPythonModule.Value().c_str())) {
    std::cerr << "Error: Script file can't be found!" << std::endl;
    exit(1);
  }

  return 0;
}

