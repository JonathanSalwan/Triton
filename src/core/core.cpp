
#include "pin.H"
#include "Triton.h"


/* Pin options */
KNOB<std::string>  KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool", "startAnalysis", "none", "Start analysis from a function name");

/* flag Lock / Unlock instrumentation */
UINT32 _analysisStatus = LOCKED;

/* Snapshot Engine */
SnapshotEngine *snapshotEngine = new SnapshotEngine;

/* Taint Engine */
TaintEngine *taintEngine = new TaintEngine;

/* Symbolic Engine */
SymbolicEngine *symbolicEngine = new SymbolicEngine;




INT32 Usage()
{
    cerr << KNOB_BASE::StringKnobSummary() << endl;
    return -1;
}


int main(int argc, char *argv[])
{
  PIN_InitSymbols();
  if(PIN_Init(argc, argv)){
      return Usage();
  }
 
  if (KnobStartAnalysis.Value().empty())
    return Usage();

  PIN_SetSyntaxIntel();
  IMG_AddInstrumentFunction(Image, 0);
  INS_AddInstrumentFunction(Instruction, 0);
  PIN_StartProgram();

  return 0;
}

