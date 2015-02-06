
#include "pin.H"
#include "Triton.h"

/*
 * reg, imm <- done
 * reg, reg <- done
 * reg, mem <- done
 * mem, imm <- done
 * mem, reg <- done
 *
 * */

VOID movRegReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, REG reg2, INT32 opcode)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  UINT64 reg1_ID  = translatePinRegToID(reg1);
  UINT64 reg2_ID  = translatePinRegToID(reg2);
  UINT64 size     = (REG_Size(reg1) * 8) - (REG_Size(reg2) * 8);

  if (trace->symbolicEngine->symbolicReg[reg2_ID] != UNSET){
    switch(opcode){
      case XED_ICLASS_MOV:
        expr << "#" << std::dec << trace->symbolicEngine->symbolicReg[reg2_ID];
        break;
      case XED_ICLASS_MOVSX:
        expr << "((_ sign_extend " << std::dec << size << ") #" << trace->symbolicEngine->symbolicReg[reg2_ID] << ")";
        break;
      case XED_ICLASS_MOVZX:
        expr << "((_ zero_extend " << std::dec << size << ") #" << trace->symbolicEngine->symbolicReg[reg2_ID] << ")";
        break;
    }
  }
  else{
    switch(opcode){
      case XED_ICLASS_MOV:
        expr << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg1));
        break;
      case XED_ICLASS_MOVSX:
        expr << "((_ sign_extend " << std::dec << size << ") " << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg2)) << ")";
        break;
      case XED_ICLASS_MOVZX:
        expr << "((_ zero_extend " << std::dec << size << ") " << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg2)), REG_Size(reg2)) << ")";
        break;
    }
  }

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();

  if (trace->taintEngine->isRegTainted(reg2_ID))
    trace->taintEngine->taintReg(reg1_ID);
  else
    trace->taintEngine->untaintReg(reg1_ID);

  elem->isTainted = trace->taintEngine->getRegStatus(reg1_ID);

  displayTrace(insAddr, insDis, elem);

  return;
}


VOID movRegImm(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 imm, INT32 opcode)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  expr << smt2lib_bv(imm, REG_Size(reg1));
   
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();

  trace->taintEngine->untaintReg(reg1_ID);

  displayTrace(insAddr, insDis, elem);

  return;
}


VOID movRegMem(std::string insDis, ADDRINT insAddr, REG reg1, UINT64 mem, UINT32 readSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream expr;

  UINT64 reg1_ID  = translatePinRegToID(reg1);
  UINT64 size     = (REG_Size(reg1) * 8) - (readSize * 8);

  if (trace->symbolicEngine->isMemoryReference(mem) != UNSET){
    switch(opcode){
      case XED_ICLASS_MOV:
        expr << "#" << std::dec << trace->symbolicEngine->isMemoryReference(mem);
        break;
      case XED_ICLASS_MOVSX:
        expr << "((_ sign_extend " << std::dec << size << ") #" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ")";
        break;
      case XED_ICLASS_MOVZX:
        expr << "((_ zero_extend " << std::dec << size << ") #" << std::dec << trace->symbolicEngine->isMemoryReference(mem) << ")";
        break;
    }
  }
  else{

    if (trace->taintEngine->isMemoryTainted(mem)){
      UINT64 symVarID = trace->symbolicEngine->getUniqueSymVarID();
      switch(opcode){
        case XED_ICLASS_MOV:
          expr << "SymVar_" << std::dec << symVarID;
          break;
        case XED_ICLASS_MOVSX:
          expr << "((_ sign_extend " << std::dec << size << ") " << "SymVar_" << std::dec << symVarID << ")";
          break;
        case XED_ICLASS_MOVZX:
          expr << "((_ zero_extend " << std::dec << size << ") " << "SymVar_" << std::dec << symVarID << ")";
          break;
      } 
      trace->symbolicEngine->addSmt2LibVarDecl(symVarID, readSize);
      trace->symbolicEngine->addSymVarMemoryReference(mem, symVarID);
    }
    else {
      switch(opcode){
        case XED_ICLASS_MOV:
          expr << smt2lib_bv(derefMem(mem, readSize), readSize);
          break;
        case XED_ICLASS_MOVSX:
          expr << "((_ sign_extend " << std::dec << size << ") " << smt2lib_bv(derefMem(mem, readSize), readSize) << ")";
          break;
        case XED_ICLASS_MOVZX:
          expr << "((_ zero_extend " << std::dec << size << ") " << smt2lib_bv(derefMem(mem, readSize), readSize) << ")";
          break;
      }
    }
  }
    
  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  trace->symbolicEngine->symbolicReg[reg1_ID] = elem->getID();
  elem->isTainted = !TAINTED;
  trace->taintEngine->untaintReg(reg1_ID);

  /* Check if the source addr is tainted */
  if (trace->taintEngine->isMemoryTainted(mem)){
      trace->taintEngine->taintReg(reg1_ID);
      elem->isTainted = TAINTED;
  }

  displayTrace(insAddr, insDis, elem);

  return;
}


VOID movMemReg(std::string insDis, ADDRINT insAddr, CONTEXT *ctx, REG reg1, UINT64 mem, UINT32 writeSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream expr;

  UINT64 reg1_ID = translatePinRegToID(reg1);

  if (trace->symbolicEngine->symbolicReg[reg1_ID] != UNSET)
    expr << "#" << trace->symbolicEngine->symbolicReg[reg1_ID];
  else 
    expr << smt2lib_bv(PIN_GetContextReg(ctx, getHighReg(reg1)), writeSize);

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  elem->isTainted = !TAINTED;

  /* If expr reg is tainted, we taint the memory area */
  if (trace->taintEngine->isRegTainted(reg1_ID)){
    unsigned int offset = 0;
    for (; offset < writeSize ; offset++){
      if (trace->taintEngine->isMemoryTainted(mem+offset) == false)
        trace->taintEngine->taintAddress(mem+offset);
    }
    elem->isTainted = TAINTED;
  }

  /* If expr reg is not tainted, we untaint the memory area */
  if (trace->taintEngine->isRegTainted(reg1_ID) == false){
    unsigned int offset = 0;
    for (; offset < writeSize ; offset++){
      trace->taintEngine->untaintAddress(mem+offset);
    }
    elem->isTainted = !TAINTED;
  }

  /* Link the memory reference to the symbolic expression */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  return;
}


VOID movMemImm(std::string insDis, ADDRINT insAddr, UINT64 imm, UINT64 mem, UINT32 writeSize, INT32 opcode)
{
  if (_analysisStatus == LOCKED || insAddr > LIB_MAPING_MEMORY)
    return;

  std::list<UINT64>::iterator i;
  std::stringstream expr;

  expr << smt2lib_bv(imm, writeSize);

  SymbolicElement *elem = trace->symbolicEngine->newSymbolicElement(expr);
  elem->isTainted = !TAINTED;

  /* We remove the taint if the memory area is tainted */
  unsigned int offset = 0;
  for (; offset < writeSize ; offset++){
    trace->taintEngine->untaintAddress(mem+offset);
  }

  /* Link the memory reference to the symbolic expression */
  trace->symbolicEngine->addMemoryReference(mem, elem->getID());

  displayTrace(insAddr, insDis, elem);

  return;
}


