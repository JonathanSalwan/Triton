
#include "pin.H"
#include "Triton.h"


/*
 * TODO :
 *
 * reg, imm <- done
 * reg, reg <- done
 * mem, imm <- done
 * mem, reg <- done
 *
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
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  /* Build smt */
  expr << "(assert (= (" << smt2lib_extract(REG_Size(reg1));
  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    expr << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else 
    expr << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
  expr << ") " << smt2lib_bv(imm, REG_Size(reg1)) << "))";
    
  /* Add sym elem */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Check if reg1 is tainted */
  if (trace->taintEngine->isRegTainted(reg1_ID))
    elem->isTainted = TAINTED;

  /* Display trace */
  displayTrace(insAddr, insDis, elem);

  return;
}


VOID cmpRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr, vr1, vr2;

  UINT64 reg1_ID = translatePinRegToID(reg1);
  UINT64 reg2_ID = translatePinRegToID(reg2);

  /* Build smt reg 1 */
  vr1 << "(" << smt2lib_extract(REG_Size(reg1));
  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    vr1 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else
    vr1 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1));
  vr1 << ")";
    
  /* Build smt reg 2 */
  vr2 << "(" << smt2lib_extract(REG_Size(reg2));
  if (trace->symbolicEngine->symbolicReg[reg2_ID] != UNSET)
    vr2 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg2_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg2));
  vr2 << ")";

  /* Build smt compare with smt_reg1 smt_reg2 */
  expr << "(assert (= " << vr1.str() << " " << vr2.str() << "))";

  /* Add sym elem */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Check if reg1 or reg2 is tainted */
  if (trace->taintEngine->isRegTainted(reg1_ID) || trace->taintEngine->isRegTainted(reg2_ID))
    elem->isTainted = TAINTED;

  /* Display trace */
  displayTrace(insAddr, insDis, elem);

  return;
}


VOID cmpMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  expr << "(assert (= ";
  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET)
    expr << "(" << smt2lib_extract(readSize) << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ") " << smt2lib_bv(imm, readSize);
  else
    expr << smt2lib_bv(derefMem(mem, readSize), readSize) << " " << smt2lib_bv(imm, readSize);
  expr << "))";

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  if (trace->taintEngine->isMemoryTainted(mem))
    elem->isTainted = TAINTED;
  
  displayTrace(insAddr, insDis, elem);

  return ;
}


VOID cmpMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 readSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr, vr1, vr2;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  /* Operand 1 - mem */
  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET)
    vr1 << "(" << smt2lib_extract(readSize) << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ")";
  else
    vr1 << smt2lib_bv(derefMem(mem, readSize), readSize);

  /* Operand 1 - reg */
  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    vr2 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), readSize);

  /* expression op1 op2 */
  expr << "(assert (= " << vr1.str() << " " << vr2.str() << "))";

  /* Craft the symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Apply taint */
  if (trace->taintEngine->isMemoryTainted(mem) || trace->taintEngine->isRegTainted(reg1_ID))
    elem->isTainted = TAINTED;

  displayTrace(insAddr, insDis, elem);

  return ;
}

