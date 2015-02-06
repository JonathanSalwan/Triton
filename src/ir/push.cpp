
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg <- done
 * imm <- done
 *
 * mem <- todo
 *
 * */


static VOID setMemReg(CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize, Tritinst *inst)
{
  /* Push in memory */
  UINT64 reg1_ID = translatePinRegToID(reg1);

  std::stringstream expr;

  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    expr << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else
    expr << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), writeSize);

  /* Craft symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);

  inst->addElement(elem);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    trace->taintEngine->untaintAddress(mem+offset);
  }

  /* Then, we taint if the reg is tainted */
  if (trace->taintEngine->isRegTainted(reg1_ID)){
    for (offset = 0; offset < writeSize ; offset++){
      trace->taintEngine->taintAddress(mem+offset);
    }
  }

  /* Memory reference */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(0, "", elem);
}


static VOID setMemImm(CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize, Tritinst *inst)
{
  std::stringstream expr;

  expr << smt2lib_bv(imm, writeSize);

  /* Craft symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);

  inst->addElement(elem);

  /* We remove the taint by default */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    trace->taintEngine->untaintAddress(mem+offset);
  }

  /* Memory reference */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(0, "", elem);
}


VOID pushReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  /* Sub RSP */
  if (trace->symbolicEngine->symbolicReg[ID_RSP] != UNSET)
    expr << "(bvsub #" << std::dec << trace->symbolicEngine->symbolicReg[ID_RSP] << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";
  else
    expr << "(bvsub " << smt2lib_bv(PIN_GetContextReg(ctx, REG_RSP), REG_Size(REG_RSP)) << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";

  /* Craft symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Memory reference */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  setMemReg(ctx, reg1, mem, writeSize, inst);

  return;
}


VOID pushImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, UINT64 imm, UINT64 mem, UINT32 writeSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;
 
  std::stringstream expr;

  /* Sub RSP */
  if (trace->symbolicEngine->symbolicReg[ID_RSP] != UNSET)
    expr << "(bvsub #" << std::dec << trace->symbolicEngine->symbolicReg[ID_RSP] << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";
  else
    expr << "(bvsub " << smt2lib_bv(PIN_GetContextReg(ctx, REG_RSP), REG_Size(REG_RSP)) << " " << smt2lib_bv(8, REG_Size(REG_RSP)) << ")";

  /* Craft symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_RSP] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Memory reference */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  setMemImm(ctx, imm, mem, writeSize, inst);

  return;
}

