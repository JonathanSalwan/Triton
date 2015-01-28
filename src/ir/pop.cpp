
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg <- done
 *
 * mem <- todo
 *
 * */

static VOID setMem(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  UINT64 i = 0;
  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (symbolicEngine->isMemoryReference(mem) != -1)
    expr << "#" << std::dec << symbolicEngine->isMemoryReference(mem);
  else
    expr << smt2lib_bv(derefMem(mem, readSize), readSize);
    
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

  displayTrace(insAddr, insDis, elem);
}


static VOID alignStack(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 mem)
{
  std::stringstream expr;

  /* Add RSP */
  if (symbolicEngine->symbolicReg[ID_RSP] != (UINT64)-1)
    expr << "(+ #" << std::dec << symbolicEngine->symbolicReg[ID_RSP] << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";
  else
    expr << "(+ " << smt2lib_bv(PIN_GetContextReg(ctx, REG_RSP), REG_Size(REG_RSP)) << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Memory reference */
  symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(0, "", elem);

  return;
}


VOID popReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  setMem(insDis, insAddr, ctx, reg1, mem, readSize);
  alignStack(insDis, insAddr, ctx, mem);

  return;
}

