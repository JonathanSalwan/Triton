
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg, imm <- done
 * reg, reg <- done
 * mem, imm <- done
 *
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

VOID cmpRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  /* Build smt */
  expr << "(assert (= (" << smt2lib_extract(REG_Size(reg1));
  if (symbolicEngine->symbolicReg[reg1_ID] != (UINT64)-1)
    expr << "#" << std::dec << symbolicEngine->symbolicReg[reg1_ID];
  else 
    expr << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
  expr << ") " << smt2lib_bv(imm, REG_Size(reg1)) << "))";
    
  /* Add sym elem */
  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Check if reg1 is tainted */
  if (taintEngine->isRegTainted(reg1_ID))
    elem->isTainted = TAINTED;

  /* Display trace */
  displayTrace(insAddr, insDis, elem);

  return;
}


VOID cmpRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream expr, vr1, vr2;

  UINT64 reg1_ID = translatePinRegToID(reg1);
  UINT64 reg2_ID = translatePinRegToID(reg2);

  /* Build smt reg 1 */
  vr1 << "(" << smt2lib_extract(REG_Size(reg1));
  if (symbolicEngine->symbolicReg[reg1_ID] != (UINT64)-1)
    vr1 << "#" << std::dec << symbolicEngine->symbolicReg[reg1_ID];
  else
    vr1 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
  vr1 << ")";
    
  /* Build smt reg 2 */
  vr2 << "(" << smt2lib_extract(REG_Size(reg2));
  if (symbolicEngine->symbolicReg[reg2_ID] != (UINT64)-1)
    vr2 << "#" << std::dec << symbolicEngine->symbolicReg[reg2_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg2));
  vr2 << ")";

  /* Build smt compare with smt_reg1 smt_reg2 */
  expr << "(assert (= " << vr1.str() << " " << vr2.str() << "))";

  /* Add sym elem */
  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Check if reg1 or reg2 is tainted */
  if (taintEngine->isRegTainted(reg1_ID) || taintEngine->isRegTainted(reg2_ID))
    elem->isTainted = TAINTED;

  /* Display trace */
  displayTrace(insAddr, insDis, elem);

  return;
}


VOID cmpMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED)
    return;

  std::stringstream expr, vr1, vr2;

  expr << "(assert (= ";
  if (symbolicEngine->isMemoryReference(mem) != -1)
    expr << "(" << smt2lib_extract(readSize) << "#" << std::dec << symbolicEngine->isMemoryReference(mem) << ") " << smt2lib_bv(imm, readSize);
  else
    expr << smt2lib_bv(derefMem(mem, readSize), readSize) << " " << smt2lib_bv(imm, readSize);
  expr << "))";

  symbolicElement *elem = symbolicEngine->newSymbolicElement(expr);
  symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  if (taintEngine->isMemoryTainted(mem))
    elem->isTainted = TAINTED;
  
  displayTrace(insAddr, insDis, elem);

  return ;
}


