
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg, imm <- done
 * reg, reg <- done
 *
 * mem, imm <- todo
 * mem, reg <- todo
 * reg, mem <- todo
 *
 * ZF <- done
 *
 * OF <- todo
 * SF <- todo
 * AF <- todo
 * CF <- todo
 * PF <- todo
 *
 * */

static VOID setZF(UINT64 id)
{
  std::stringstream expr;

  expr << "(assert (= #" << std::dec << id << " 0))";
    
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  displayTrace(0, "", elem);
}


VOID addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    expr << "(+ #" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID] << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";
  else 
    expr << "(+ " << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1)) << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";
    
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  elem->isTainted = trace->taintEngine->getRegStatus(reg1_ID);

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID());

  return;
}


VOID addRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr, vr1, vr2;

  UINT64 reg1_ID = translatePinRegToID(reg1);
  UINT64 reg2_ID = translatePinRegToID(reg2);

  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    vr1 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else
    vr1 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
    
  if (trace->symbolicEngine->symbolicReg[reg2_ID] != UNSET)
    vr2 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg2_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg1));

  expr << "(+ " << vr1.str() << " " << vr2.str() << ")";

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();

  if (trace->taintEngine->isRegTainted(reg2_ID))
    trace->taintEngine->taintReg(reg1_ID);

  elem->isTainted = trace->taintEngine->getRegStatus(reg1_ID);

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID());

  return;
}


