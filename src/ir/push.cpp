
#include "pin.H"
#include "triton.h"



static VOID alignStack(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 mem)
{
  std::stringstream expr, taint;

  /* Sub RSP */
  if (symbolicEngine->symbolicReg[ID_RSP] != (UINT64)-1)
    expr << "(- #" << std::dec << symbolicEngine->symbolicReg[ID_RSP] << " 8)";
  else
    expr << "(- 0x" << std::hex << PIN_GetContextReg(ctx, REG_RSP) << " 8)";

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Memory reference */
  symbolicEngine->addMemoryReference(mem, elem->getID());

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % elem->getExpression() % taint.str();

  return;
}


static VOID setMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize)
{
  /* Push in memory */
  UINT64 reg1_ID = translatePinRegToID(reg1);

  std::stringstream expr, taint;

  if (symbolicEngine->symbolicReg[reg1_ID] != (UINT64)-1)
    expr << "#" << std::dec << symbolicEngine->symbolicReg[reg1_ID];
  else
    expr << "0x" << std::hex << PIN_GetContextReg(ctx, getHighReg(reg1));

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    taintEngine->removeAddress(mem+offset);
  }

  /* Then, we taint if the reg is tainted */
  if (taintEngine->isRegTainted(reg1_ID)){
    for (offset = 0; offset < writeSize ; offset++){
      taintEngine->addAddress(mem+offset);
    }
  }

  /* Memory reference */
  symbolicEngine->addMemoryReference(mem, elem->getID());

  std::cout << boost::format(outputInstruction) % "" % "" % elem->getExpression() % taint.str();
}


static VOID setMemImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize)
{
  std::stringstream expr, taint;

  expr << "0x" << std::hex << imm;

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    taintEngine->removeAddress(mem+offset);
  }

  /* Memory reference */
  symbolicEngine->addMemoryReference(mem, elem->getID());

  std::cout << boost::format(outputInstruction) % boost::io::group(hex, showbase, insAddr) % insDis % elem->getExpression() % taint.str();
}


VOID pushReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED)
    return;

  alignStack(insDis, insAddr, ctx, mem);
  setMemReg(insDis, insAddr, ctx, reg1, mem, writeSize);

  return;
}


VOID pushImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED)
    return;
 
  alignStack(insDis, insAddr, ctx, mem);
  setMemImm(insDis, insAddr, ctx, imm, mem, writeSize);

  return;
}

