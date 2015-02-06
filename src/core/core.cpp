
#include <csignal>

#include "pin.H"
#include "Triton.h"

/* Pin options: -startAnalysis */
KNOB<std::string>  KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool", "startAnalysis", "none", "Start/end the analysis from a scope function");

/* Pin options: -detectFormatString */
KNOB<bool>  KnobDetectFormatString(KNOB_MODE_WRITEONCE, "pintool", "detectFormatString", "0", "Enable the format string detection analysis");

/* flag Lock / Unlock instrumentation */
UINT32 _analysisStatus = LOCKED;



/* Trace object */
Trace *trace = new Trace;



/* Usage function if Pin fail to start */
INT32 Usage()
{
    std::cerr << "Triton analyzer: " << std::endl << std::endl;
    std::cerr << " -startAnalysis <function name>       Start/end the analysis from a scope function" << std::endl;
    std::cerr << " -detectFormatString                  Enable the format string detection analysis" << std::endl;
    return -1;
}


VOID Fini(INT32, VOID *)
{

//  /* Currently used to test if all going good */
//  std::cout << std::endl << std::endl << "[DEBUG] ---------------------------" << std::endl;
//  std::list<Tritinst *>::iterator i;
//  for(i = trace->getInstructions().begin(); i != trace->getInstructions().end(); i++){
//    std::cout << (*i)->getAddress() << " " << (*i)->numberOfElements() << " " << (*i)->getDisassembly() << std::endl;
//  }

  /* Delete the trace */
  delete trace;
  return;
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
  IMG_AddInstrumentFunction(Image, NULL);

  /* Add Instructions callback */
  INS_AddInstrumentFunction(Instruction, NULL);

  /* Add callback call after the instrumentation */
  PIN_AddFiniFunction(Fini, NULL);

  /* Catch SIGSEGV */
  PIN_InterceptSignal(SIGSEGV, catchSignal, NULL);

  /* Rock 'n roll baby */
  PIN_StartProgram();

  return 0;
}


