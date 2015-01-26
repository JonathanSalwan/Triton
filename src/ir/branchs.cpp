
#include "pin.H"
#include "triton.h"



VOID branchs(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  SolverEngine se(symbolicEngine);
  se.solveFromID(symbolicEngine->symbolicReg[ID_ZF]);

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % se.getFormula() % "";

  std::cout << "----- Model -----" << std::endl << se.getModel() << std::endl << "-----------------" << std::endl;
}


