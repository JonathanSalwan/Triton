
#include "pin.H"
#include "Triton.h"


VOID notImplemented(std::string insDis, ADDRINT insAddr)
{
  if (_analysisStatus == LOCKED)
    return;

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % "n/a" % "n/a (Not Implemented)";
}

