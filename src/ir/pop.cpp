
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

  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET)
    expr << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem);
  else
    expr << smt2lib_bv(derefMem(mem, readSize), readSize);
    
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  trace->taintEngine->untaintReg(reg1_ID);
  elem->isTainted = !TAINTED;

  /* Check if the source addr is tainted */
  for (i = 0 ; i < readSize ; i++){
    if (trace->taintEngine->isMemoryTainted(mem + i)){
      trace->taintEngine->taintReg(reg1_ID);
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
  if (trace->symbolicEngine->symbolicReg[ID_RSP] != UNSET)
    expr << "(+ #" << std::dec << trace->symbolicEngine->symbolicReg[ID_RSP] << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";
  else
    expr << "(+ " << smt2lib_bv(PIN_GetContextReg(ctx, REG_RSP), REG_Size(REG_RSP)) << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Memory reference */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

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

