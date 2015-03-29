#include <iostream>
#include <memory>
#include <python2.7/Python.h>
#include <sstream>
#include <stdexcept>
#include <vector>

#include "pin.H"

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "IRBuilderFactory.h"
#include "PINContextHandler.h"
#include "Trace.h"
#include "Trigger.h"


/* Pin options: -startAnalysis */
KNOB<std::string>  KnobPythonModule(KNOB_MODE_WRITEONCE, "pintool", "script", "", "Python script");


AnalysisProcessor   ap;
Trace               trace;
Trigger             analysisTrigger  = Trigger();
static char         *startAnalysis_g = NULL;
static bool         dumpStats_g      = false;
static bool         dumpTrace_g      = false;


VOID callback(IRBuilder *irb, CONTEXT *ctx, BOOL hasEA, ADDRINT ea, THREADID threadId)
{
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


void toggleWrapper()
{
  analysisTrigger.toggle();
}


VOID IMG_Instrumentation(IMG img, VOID *)
{
  /* This callback is used to lock and target the analysis */
  /* Mainly used to target an area */
  if (startAnalysis_g == NULL)
    return;
  RTN targetRTN = RTN_FindByName(img, startAnalysis_g);
  if (RTN_Valid(targetRTN)){
    RTN_Open(targetRTN);
    RTN_InsertCall(targetRTN,
        IPOINT_BEFORE,
        (AFUNPTR) toggleWrapper,
        IARG_END);

    RTN_InsertCall(targetRTN,
        IPOINT_AFTER,
        (AFUNPTR) toggleWrapper,
        IARG_END);

    RTN_Close(targetRTN);
  }
}


VOID Fini(INT32, VOID *)
{
  if (dumpTrace_g == true)
    trace.display();
  if (dumpStats_g == true)
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


static char Triton_runProgram_doc[] = "Start the Pin instrumentation";
static PyObject* Triton_runProgram(PyObject* self, PyObject* noarg)
{
  // Never returns - Rock 'n roll baby \o/
  PIN_StartProgram();
  return Py_None;
}


static char Triton_startAnalysis_doc[] = "Start the symbolic execution from a specific";
static PyObject* Triton_startAnalysis(PyObject* self, PyObject* name)
{
  startAnalysis_g = PyString_AsString(name);
  return Py_None;
}


static char Triton_dumpTrace_doc[] = "Dump the trace at the end of the execution";
static PyObject* Triton_dumpTrace(PyObject* self, PyObject* flag)
{
  if (PyBool_Check(flag))
    dumpTrace_g = (flag == Py_True);
  return Py_None;
}


static char Triton_dumpStats_doc[] = "Dump statistics at the end of the execution";
static PyObject* Triton_dumpStats(PyObject* self, PyObject* flag)
{
  if (PyBool_Check(flag))
    dumpStats_g = (flag == Py_True);
  return Py_None;
}


static PyMethodDef pythonCallbacks[] = {
  {"runProgram",    Triton_runProgram,    METH_NOARGS, Triton_runProgram_doc},
  {"startAnalysis", Triton_startAnalysis, METH_O,      Triton_startAnalysis_doc},
  {"dumpTrace",     Triton_dumpTrace,     METH_O,      Triton_dumpTrace_doc},
  {"dumpStats",     Triton_dumpStats,     METH_O,      Triton_dumpStats_doc},
  {NULL, NULL, 0, NULL}
};


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

