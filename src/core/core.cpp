#include "Triton.h"

#include <iostream>

#include <csignal>
#include <cstdlib>

#include "pin.H"

using namespace std;

/* Pin options: -startAnalysis */
KNOB<string> KnobStartAnalysis(KNOB_MODE_WRITEONCE, "pintool",
			       "startAnalysis", "none",
			       "Start/end the analysis from a scope function");

/* Pin options: -detectFormatString */
KNOB<bool> KnobDetectFormatString(KNOB_MODE_WRITEONCE, "pintool",
				  "detectFormatString", "0",
				  "Enable the format string detection analysis");

/* flag Lock / Unlock instrumentation */
UINT32 _analysisStatus = LOCKED;

/* Trace object */
Trace * trace = new Trace;


/* Usage function if Pin fail to start */
INT32 Usage()
{
  cout << "Triton binary analyzer usage: triton MODE [ARGS] EXEC" << endl;
  cout << endl;
  cout << "Available modes are:" << endl;
  cout << " -startAnalysis <func name>  Start/end the analysis from the function scope" << endl; 
  cout << " -detectFormatString         Enable the format string detection analysis" << endl;

  return EXIT_SUCCESS;
}


/* Final callback */
VOID Fini (INT32, VOID *)
{
//  /* Currently used to test if all going good */
//  cout << endl << endl << "[DEBUG] ---------------------------" << endl;
//  list<Tritinst *>::iterator i;
//  for(i = trace->getInstructions().begin(); i != trace->getInstructions().end(); i++){
//    cout << (*i)->getAddress() << " " << (*i)->numberOfElements() << " " << (*i)->getDisassembly() << endl;
//  }

  /* Clean-up the trace */
  delete trace;
}


int
main (int argc, char *argv[])
{
  PIN_InitSymbols ();
  if (PIN_Init (argc, argv))
    {
      return Usage ();
    }

  /* We first need a target function */
  if (KnobStartAnalysis.Value ().empty ())
    return Usage ();

  /* Enable Intel syntax */
  PIN_SetSyntaxIntel ();

  /* Add Image callback */
  IMG_AddInstrumentFunction (Image, NULL);

  /* Add Instructions callback */
  INS_AddInstrumentFunction (Instruction, NULL);

  /* Final callback after the instrumentation */
  PIN_AddFiniFunction (Fini, NULL);

  /* Catch SIGSEGV */
  PIN_InterceptSignal (SIGSEGV, catchSignal, NULL);

  /* Rock 'n roll baby */
  PIN_StartProgram ();

  return EXIT_SUCCESS;
}
