
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

static VOID setZF(UINT64 id, Tritinst *inst)
{
  std::stringstream expr;

  expr << "(assert (= #" << std::dec << id << " 0))";
  
  /* Craft the symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  inst->addElement(elem);

  displayTrace(0, "", elem);
}


VOID addRegImm(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 imm)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    expr << "(bvadd #" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID] << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";
  else 
    expr << "(bvadd " << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), REG_Size(reg1)) << " " << smt2lib_bv(imm, REG_Size(reg1)) << ")";

  /* Craft the symbolic element */   
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  elem->isTainted = trace->taintEngine->getRegStatus(reg1_ID);

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID(), inst);

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

  expr << "(bvadd " << vr1.str() << " " << vr2.str() << ")";

  /* Craft the symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Apply taint */
  if (trace->taintEngine->isRegTainted(reg2_ID))
    trace->taintEngine->taintReg(reg1_ID);

  elem->isTainted = trace->taintEngine->getRegStatus(reg1_ID);

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID(), inst);

  return;
}


VOID addMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT64 writeSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  expr << "(bvadd ";
  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET)
    expr << "(" << smt2lib_extract(writeSize) << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ") " << smt2lib_bv(imm, writeSize);
  else
    expr << smt2lib_bv(derefMem(mem, writeSize), writeSize) << " " << smt2lib_bv(imm, writeSize);
  expr << ")";

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  if (trace->taintEngine->isMemoryTainted(mem))
    elem->isTainted = TAINTED;

  /* Link the memory reference to the symbolic expression */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID(), inst);

  return ;
}


VOID addMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT64 writeSize)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr, vr1, vr2;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  /* Operand 1 - mem */
  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET)
    vr1 << "(" << smt2lib_extract(writeSize) << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ")";
  else
    vr1 << smt2lib_bv(derefMem(mem, writeSize), writeSize); 

  /* Operand 1 - reg */
  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    vr2 << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg1_ID];
  else
    vr2 << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), writeSize);

  /* expression op1 op2 */
  expr << "(bvadd " << vr1.str() << " " << vr2.str() << ")";

  /* Craft the symbolic element */
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[ID_ZF] = elem->getID();

  /* Craft the Tritinst */
  Tritinst *inst = new Tritinst(insAddr, insDis);
  inst->addElement(elem);

  /* Add the Tritinst in the trace */
  trace->addInstruction(inst);

  /* Apply taint */
  if (trace->taintEngine->isMemoryTainted(mem))
    elem->isTainted = TAINTED;

  /* If expr reg is tainted, we taint the memory area */
  if (trace->taintEngine->isRegTainted(reg1_ID)){
    unsigned int offset = 0;
    for (; offset < writeSize ; offset++){
      if (trace->taintEngine->isMemoryTainted(mem+offset) == false)
        trace->taintEngine->taintAddress(mem+offset);
    }
    elem->isTainted = TAINTED;
  }

  /* Link the memory reference to the symbolic expression */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  setZF(elem->getID(), inst);

  return ;
}

