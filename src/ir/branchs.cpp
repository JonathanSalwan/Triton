
#include "pin.H"
#include "Triton.h"



VOID branchs(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT32 opcode)
{
  if (_analysisStatus == LOCKED)
    return;

  SolverEngine se(symbolicEngine);
  se.solveFromID(symbolicEngine->symbolicReg[ID_ZF]);

  displayTrace(insAddr, insDis, se.getFormula(), !TAINTED);

  std::cout << "----- Model -----" << std::endl << se.getModel() << std::endl << "-----------------" << std::endl;
}


