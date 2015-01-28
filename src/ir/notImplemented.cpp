
#include "pin.H"
#include "Triton.h"


VOID notImplemented(std::string insDis, ADDRINT insAddr)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  displayTrace(insAddr, insDis, "n/a", !TAINTED);
}

