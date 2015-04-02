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
#include "PythonBindings.h"
#include "Trace.h"
#include "Trigger.h"


/* Pin options: -script */
KNOB<std::string>   KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");

AnalysisProcessor   ap;
Trace               trace;
Trigger             analysisTrigger = Trigger();


VOID callback(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea, THREADID threadId)
{
  // Check if the DSE must be start at this address
  if (PyTritonOptions::startAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::startAnalysisFromAddr.end())
    analysisTrigger.update(true);

  // Check if the DSE must be stop at this address
  if (PyTritonOptions::stopAnalysisFromAddr.find(irb->getAddress()) != PyTritonOptions::stopAnalysisFromAddr.end())
    analysisTrigger.update(false);

  if (!analysisTrigger.getState())
  // Analysis locked
    return;

  PINContextHandler ctxH(ctx, threadId);

  if (hasEA)
    irb->setup(ea);

  trace.addInstruction(irb->process(ctxH, ap));
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
  if (PyTritonOptions::dumpTrace == true)
    trace.display();

  if (PyTritonOptions::dumpStats == true)
    ap.displayStats();

  Py_Finalize();
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
  Py_Initialize();

  PIN_InitSymbols();
  PIN_SetSyntaxIntel();
  if(PIN_Init(argc, argv))
      return Usage();

  // Init Python Bindings
  PyObject* tritonModule = Py_InitModule("triton", pythonCallbacks);
  if (tritonModule == NULL) {
    printf("Failed to initialize Triton bindings\n");
    PyErr_Print();
    exit(1);
  }

  // Image callback
  IMG_AddInstrumentFunction(IMG_Instrumentation, NULL);

  // Instruction callback
  TRACE_AddInstrumentFunction(TRACE_Instrumentation, NULL);

  // End instrumentation callback
  PIN_AddFiniFunction(Fini, NULL);

  // Exec the python bindings file
  const char* filename = KnobPythonModule.Value().c_str();
  FILE* pyScript = fopen(filename, "r");
  if (pyScript == NULL) {
    perror("fopen");
    exit(1);
  }
  PyRun_SimpleFile(pyScript, filename);
  fclose(pyScript);

  return 0;
}

