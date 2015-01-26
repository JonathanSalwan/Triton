
#include "pin.H"
#include "triton.h"



static VOID setMem(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  UINT64 i = 0;
  std::stringstream expr, taint;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (symbolicEngine->isMemoryReference(mem) != -1)
    expr << "#" << std::dec << symbolicEngine->isMemoryReference(mem);
  else
    expr << "0x" << std::hex << derefMem(mem, readSize);
    
  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  taintEngine->untaintReg(reg1_ID);
  elem->isTainted = !TAINTED;

  /* Check if the source addr is tainted */
  for (i = 0 ; i < readSize ; i++){
    if (taintEngine->isMemoryTainted(mem + i)){
      taintEngine->taintReg(reg1_ID);
      elem->isTainted = TAINTED;
      break;
    }
  }

  if (elem->isTainted)
    taint << "#" << symbolicEngine->symbolicReg[reg1_ID] << " is controllable";

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % elem->getExpression() % taint.str();
}


static VOID alignStack(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 mem)
{
  std::stringstream expr, taint;

  /* Sub RSP */
  if (symbolicEngine->symbolicReg[ID_RSP] != (UINT64)-1)
    expr << "(+ #" << std::dec << symbolicEngine->symbolicReg[ID_RSP] << " 8)";
  else
    expr << "(+ 0x" << std::hex << PIN_GetContextReg(ctx, REG_RSP) << " 8)";

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Memory reference */
  symbolicEngine->addMemoryReference(mem, elem->getID());

  std::cout << boost::format(outputInstruction) % "" % "" % elem->getExpression() % taint.str();

  return;
}


VOID popReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED)
    return;

  setMem(insDis, insAddr, ctx, reg1, mem, readSize);
  alignStack(insDis, insAddr, ctx, mem);

  return;
}

