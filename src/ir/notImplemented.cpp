
#include "pin.H"
#include "Triton.h"


VOID notImplemented(std::string insDis, ADDRINT insAddr)
{
  if (_analysisStatus == LOCKED)
    return;

  displayTrace(insAddr, insDis, "n/a", !TAINTED);
}

