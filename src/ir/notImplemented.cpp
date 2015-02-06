
#include "pin.H"
#include "Triton.h"


VOID notImplemented(std::string insDis, ADDRINT insAddr)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  /* Craft the Tritinst without element */
  Tritinst *inst = new Tritinst(insAddr, insDis);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  displayTrace(insAddr, insDis, "n/a", !TAINTED);
}

