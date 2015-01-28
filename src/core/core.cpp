
#include "pin.H"
#include "Triton.h"


/* Pin options: -startAnalysis */
KNOB<std::string>  KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool", "startAnalysis", "none", "Start/end the analysis from a scope function");

/* Pin options: -detectFormatString */
KNOB<bool>  KnobDetectFormatString(KNOB_MODE_WRITEONCE, "pintool", "detectFormatString", "0", "Enable the format string detection analysis");

/* flag Lock / Unlock instrumentation */
UINT32 _analysisStatus = LOCKED;

/* Snapshot Engine */
SnapshotEngine *snapshotEngine = new SnapshotEngine;

/* Taint Engine */
TaintEngine *taintEngine = new TaintEngine;

/* Symbolic Engine */
SymbolicEngine *symbolicEngine = new SymbolicEngine;



/* Usage function if Pin fail to start */
INT32 Usage()
{
    std::cerr << "Triton analyzer: " << std::endl << std::endl;
    std::cerr << " -startAnalysis <function name>       Start/end the analysis from a scope function" << std::endl;
    std::cerr << " -detectFormatString                  Enable the format string detection analysis" << std::endl;
    return -1;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  if(PIN_Init(argc, argv)){
      return Usage();
  }
 
  /* We first need a target function */
  if (KnobStartAnalysis.Value().empty())
    return Usage();

  /* Enable Intel syntax */
  PIN_SetSyntaxIntel();

  /* Add Image callback */
  IMG_AddInstrumentFunction(Image, 0);

  /* Add Instructions callback */
  INS_AddInstrumentFunction(Instruction, 0);

  /* Rock 'n roll baby */
  PIN_StartProgram();

  return 0;
}


