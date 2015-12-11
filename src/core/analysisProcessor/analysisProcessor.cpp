/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <AnalysisProcessor.h>
#include <PINContextHandler.h>


AnalysisProcessor::AnalysisProcessor():
  #ifndef LIGHT_VERSION
  symEngine(),
  solverEngine(&this->symEngine),
  taintEngine(),
  snapshotEngine(),
  stats(),
  #endif
  trace() {
  this->currentCtxH = nullptr;
}


// Context Facade
// --------------

void AnalysisProcessor::updateCurrentCtxH(ContextHandler *ctxtHandler) {
  delete this->currentCtxH;
  this->currentCtxH = ctxtHandler;
}


ContextHandler *AnalysisProcessor::getCurrentCtxH(void) {
  return this->currentCtxH;
}


void AnalysisProcessor::lock(void) {
  PIN_LockClient();
}


void AnalysisProcessor::unlock(void) {
  PIN_UnlockClient();
}


/* Returns the thread id  */
uint32 AnalysisProcessor::getThreadID(void) {
  if (!this->currentCtxH)
    return -1;
  return this->currentCtxH->getThreadID();
}


/* There is no verification on the validity of the ID. */
__uint AnalysisProcessor::getRegisterValue(RegisterOperand &reg) {
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getRegisterValue(reg.getTritonRegId());
}


__uint AnalysisProcessor::getFlagValue(RegisterOperand &flag) {
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getFlagValue(flag.getTritonRegId());
}


uint128 AnalysisProcessor::getSSERegisterValue(RegisterOperand &reg) {
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getSSERegisterValue(reg.getTritonRegId());
}


/* There is no verification on the validity of the ID. */
void AnalysisProcessor::setRegisterValue(RegisterOperand &reg, __uint value) {
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setRegisterValue(reg.getTritonRegId(), value);
}


void AnalysisProcessor::setSSERegisterValue(RegisterOperand &reg, uint128 value) {
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setSSERegisterValue(reg.getTritonRegId(), value);
}


uint128 AnalysisProcessor::getMemValue(MemoryOperand &mem, uint32 readSize) {
  return this->currentCtxH->getMemValue(mem.getAddress(), readSize);
}


uint128 AnalysisProcessor::getMemValue(__uint mem, uint32 readSize) {
  return this->currentCtxH->getMemValue(mem, readSize);
}


void AnalysisProcessor::setMemValue(MemoryOperand &mem, uint32 writeSize, uint128 value) {
  this->currentCtxH->setMemValue(mem.getAddress(), writeSize, value);
}


bool AnalysisProcessor::isContextMustBeExecuted(void) {
  return this->currentCtxH->isMustBeExecuted();
}


void AnalysisProcessor::executeContext(void) {
  this->currentCtxH->executeContext();
}


// Trace Facade
// ------------

Trace &AnalysisProcessor::getTrace(void) {
  return this->trace;
}


void AnalysisProcessor::addInstructionToTrace(Inst *instruction) {
  this->trace.addInstruction(instruction);
}


Inst *AnalysisProcessor::getLastInstruction(void) {
  return this->trace.getLastInstruction();
}


void AnalysisProcessor::clearTrace(void) {
  std::list<Inst *> instructions = this->getTrace().getInstructions();
  while(!instructions.empty()) delete instructions.front(), instructions.pop_front();
}


#ifndef LIGHT_VERSION

// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void) {
  return this->symEngine;
}


SymbolicExpression *AnalysisProcessor::createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment) {
  SymbolicExpression *se = this->createSE(expr, comment);
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createSE(smt2lib::smtAstAbstractNode *expr, std::string comment) {
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, SymExpr::UNDEF, comment);
  return se;
}



SymbolicExpression *AnalysisProcessor::createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment) {
  __uint flagId = flag.getTritonRegId();
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, SymExpr::REG, comment);
  this->assignSEToReg(se, flagId);
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, std::string comment) {
  return this->createRegSE(inst, expr, reg, reg.getSize(), comment);
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, __uint regSize, std::string comment) {
  __uint regId = reg.getTritonRegId();
  smt2lib::smtAstAbstractNode *finalExpr = nullptr, *origReg = nullptr;

  origReg = this->buildSymbolicRegOperand(reg, (REG_SIZE_BIT - 1), 0);

  switch (regSize) {
    case BYTE_SIZE:
      if (reg.getLow() == 0) {
        finalExpr = smt2lib::concat(smt2lib::extract((REG_SIZE_BIT - 1), BYTE_SIZE_BIT, origReg), expr);
      }
      else {
        finalExpr = smt2lib::concat(
                      smt2lib::extract((REG_SIZE_BIT - 1), WORD_SIZE_BIT, origReg),
                      smt2lib::concat(expr, smt2lib::extract((BYTE_SIZE_BIT - 1), 0, origReg))
                    );
      }
      break;

    case WORD_SIZE:
      finalExpr = smt2lib::concat(smt2lib::extract((REG_SIZE_BIT - 1), WORD_SIZE_BIT, origReg), expr);
      break;

    case DWORD_SIZE:
      #if defined(__x86_64__) || defined(_M_X64)
      /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
      finalExpr = smt2lib::zx(DWORD_SIZE_BIT, expr);
      break;
      #endif

    case QWORD_SIZE:
    case DQWORD_SIZE:
      finalExpr = expr;
      break;
  }

  SymbolicExpression *se = this->symEngine.newSymbolicExpression(finalExpr, SymExpr::REG, comment);
  this->assignSEToReg(se, regId);
  inst.addExpression(se);

  return se;
}


SymbolicExpression *AnalysisProcessor::createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, __uint writeSize, std::string comment) {
  smt2lib::smtAstAbstractNode *tmp;
  std::list<smt2lib::smtAstAbstractNode *> ret;
  SymbolicExpression *se = nullptr;
  __uint address = mem.getAddress();

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize) {
    /* Extract each byte of the memory */
    tmp = smt2lib::extract(((writeSize * BYTE_SIZE_BIT) - 1), ((writeSize * BYTE_SIZE_BIT) - BYTE_SIZE_BIT), expr);
    se  = symEngine.newSymbolicExpression(tmp, SymExpr::MEM, "byte reference");
    ret.push_back(tmp);
    inst.addExpression(se);
    /* Assign memory with little endian */
    this->symEngine.addMemoryReference((address + writeSize) - 1, se->getID());
    writeSize--;
  }

  /* If there is only one reference, we return the symbolic expression */
  if (ret.size() == 1)
    return se;

  /* Otherwise, we return the concatenation of all symbolic expressions */
  return symEngine.newSymbolicExpression(smt2lib::concat(ret), SymExpr::MEM, "concat reference");
}


/* Assign a symbolic expression to a register */
bool AnalysisProcessor::assignSEToReg(SymbolicExpression *se, __uint regId) {
  if (regId > ID_INVALID && regId < ID_LAST_ITEM) {
    se->setKind(SymExpr::REG);
    this->symEngine.symbolicReg[regId] = se->getID();
    return true;
  }
  return false;
}


__uint AnalysisProcessor::getRegSymbolicID(RegisterOperand &reg) {
  return this->symEngine.getRegSymbolicID(reg.getTritonRegId());
}


__uint AnalysisProcessor::getMemSymbolicID(MemoryOperand &mem) {
  return this->symEngine.getMemSymbolicID(mem.getAddress());
}


__uint AnalysisProcessor::getMemSymbolicID(__uint address) {
  return this->symEngine.getMemSymbolicID(address);
}


SymbolicVariable *AnalysisProcessor::getSymVar(__uint symVarId) {
  return this->symEngine.getSymVar(symVarId);
}


SymbolicVariable *AnalysisProcessor::getSymVar(std::string symVarName) {
  return this->symEngine.getSymVar(symVarName);
}


std::vector<SymbolicVariable *> AnalysisProcessor::getSymVars(void) {
  return this->symEngine.getSymVars();
}


SymbolicExpression *AnalysisProcessor::getExpressionFromId(__uint id) {
  return this->symEngine.getExpressionFromId(id);
}


std::vector<SymbolicExpression *> AnalysisProcessor::getExpressions(void) {
  return this->symEngine.getExpressions();
}


std::list<SymbolicExpression *> AnalysisProcessor::getTaintedExpressions(void) {
  return this->symEngine.getTaintedExpressions();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::getFullExpression(smt2lib::smtAstAbstractNode *node) {
  return this->symEngine.getFullExpression(node);
}


SymbolicVariable *AnalysisProcessor::convertExprToSymVar(__uint exprId, __uint symVarSize, std::string symVarComment) {
  SymbolicVariable *symVar = this->symEngine.convertExprToSymVar(exprId, symVarSize, symVarComment);
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertMemToSymVar(MemoryOperand &mem, __uint symVarSize, std::string symVarComment) {
  __uint address = mem.getAddress();
  SymbolicVariable *symVar = this->symEngine.convertMemToSymVar(address, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(this->getMemValue(address, symVarSize));
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertRegToSymVar(RegisterOperand &reg, __uint symVarSize, std::string symVarComment) {
  __uint regId     = reg.getTritonRegId();
  uint128 mask     = 1;
  mask             = (mask << symVarSize) - 1;
  uint128 regValue = this->getRegisterValue(reg) & mask;

  SymbolicVariable *symVar = this->symEngine.convertRegToSymVar(regId, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(regValue);
  return symVar;
}


void AnalysisProcessor::addPathConstraint(__uint exprId) {
  this->symEngine.addPathConstraint(exprId);
}


std::list<__uint> AnalysisProcessor::getPathConstraints(void) {
  return this->symEngine.getPathConstraints();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg) {
  return this->buildSymbolicRegOperand(reg, reg.getHigh(), reg.getLow());
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, __uint regSize) {
  __uint low  = reg.getLow();
  __uint high = !low ? (regSize * BYTE_SIZE_BIT) - 1 : reg.getHigh(); // TMP fix for #170
  return this->buildSymbolicRegOperand(reg, high, low);
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, __uint highExtract, __uint lowExtract) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  __uint regId  = reg.getTritonRegId();
  __uint symReg = this->getRegSymbolicID(reg);

  if (symReg != UNSET)
    op = smt2lib::extract(highExtract, lowExtract, smt2lib::reference(symReg));
  else {
    if (isSSERegId(regId))
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getSSERegisterValue(reg), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getRegisterValue(reg), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicMemOperand(MemoryOperand &mem, __uint memSize) {
  std::list<smt2lib::smtAstAbstractNode *> opVec;
  smt2lib::smtAstAbstractNode *tmp = nullptr;
  __uint address = mem.getAddress();
  __uint symMem;

  while (memSize) {
    symMem = this->getMemSymbolicID(address + memSize - 1);
    if (symMem != UNSET) {
      tmp = smt2lib::reference(symMem);
      opVec.push_back(smt2lib::extract((BYTE_SIZE_BIT - 1), 0, tmp));
    }
    else {
      tmp = smt2lib::bv(this->getMemValue(address + memSize - 1, 1), BYTE_SIZE_BIT);
      opVec.push_back(smt2lib::extract((BYTE_SIZE_BIT - 1), 0, tmp));
    }
    memSize--;
  }

  switch (opVec.size()) {
    case DQWORD_SIZE:
    case QWORD_SIZE:
    case DWORD_SIZE:
    case WORD_SIZE:
      tmp = smt2lib::concat(opVec);
      break;
    case BYTE_SIZE:
      tmp = opVec.front();
      break;
  }

  return tmp;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag, __uint size) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  __uint symFlag = this->getRegSymbolicID(flag);

  if (symFlag != UNSET)
    op = smt2lib::zx((size * BYTE_SIZE_BIT) - 1, smt2lib::reference(symFlag));
  else
    op = smt2lib::bv(this->getFlagValue(flag), size * BYTE_SIZE_BIT);

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  __uint symFlag = this->getRegSymbolicID(flag);

  if (symFlag != UNSET)
    op = smt2lib::extract(0, 0, smt2lib::reference(symFlag));
  else
    op = smt2lib::bv(this->getFlagValue(flag), 1);

  return op;
}


void AnalysisProcessor::concretizeAllReg(void) {
  this->symEngine.concretizeAllReg();
}


void AnalysisProcessor::concretizeAllMem(void) {
  this->symEngine.concretizeAllMem();
}


void AnalysisProcessor::concretizeReg(RegisterOperand &reg) {
  this->symEngine.concretizeReg(reg.getTritonRegId());
}


void AnalysisProcessor::concretizeMem(MemoryOperand &mem) {
  this->symEngine.concretizeMem(mem.getAddress());
}


bool AnalysisProcessor::isSymEngineEnabled(void) {
  return this->symEngine.isEnabled();
}


void AnalysisProcessor::enableSymEngine(void) {
  this->symEngine.enable();
}


void AnalysisProcessor::disableSymEngine(void) {
  this->symEngine.disable();
}


// Taint Engine Facade
// -------------------

TaintEngine &AnalysisProcessor::getTaintEngine(void) {
  return this->taintEngine;
}


void AnalysisProcessor::assignmentSpreadTaintExprMem(SymbolicExpression *se, MemoryOperand &mem, uint32 readSize) {
  __uint memAddrSrc = mem.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprMem(memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprReg(SymbolicExpression *se, RegisterOperand &reg) {
  __uint regIdSrc = reg.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprReg(regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegMem(SymbolicExpression *se, RegisterOperand &regSrc, MemoryOperand &memSrc, uint32 readSize) {
  __uint regIdSrc = regSrc.getTritonRegId();
  __uint memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegMem(regIdSrc, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegReg(SymbolicExpression *se, RegisterOperand &regSrc1, RegisterOperand &regSrc2) {
  __uint regIdSrc1 = regSrc1.getTritonRegId();
  __uint regIdSrc2 = regSrc2.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegReg(regIdSrc1, regIdSrc2);
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  __uint regIdDst = regDst.getTritonRegId();
  __uint regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst) {
  __uint regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  __uint regIdDst = regDst.getTritonRegId();
  __uint memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint memAddrDst = memDst.getAddress();
  __uint memAddrSrc = memSrc.getAddress();

  /* Taint parent se */
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memAddrDst, memAddrSrc, readSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != readSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = this->taintEngine.isMemTainted(memAddrSrc + i);
  }
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, __uint writeSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint memAddrDst = memDst.getAddress();

  /* Taint parent se */
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memAddrDst, writeSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != writeSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = se->isTainted;
  }
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, __uint writeSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint              memAddrDst = memDst.getAddress();
  __uint              regIdSrc = regSrc.getTritonRegId();

  /* Taint parent se */
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemReg(memAddrDst, regIdSrc, writeSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != writeSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = se->isTainted;
  }
}


bool AnalysisProcessor::isRegTainted(RegisterOperand &reg) {
  return this->taintEngine.isRegTainted(reg.getTritonRegId());
}


bool AnalysisProcessor::isMemTainted(MemoryOperand &addr) {
  return this->taintEngine.isMemTainted(addr.getAddress(), addr.getSize());
}


void AnalysisProcessor::taintReg(RegisterOperand &reg) {
  this->taintEngine.taintReg(reg.getTritonRegId());
}


void AnalysisProcessor::setTaintMem(SymbolicExpression *se, MemoryOperand &mem, __uint flag) {
  this->taintEngine.setTaintMem(mem.getAddress(), flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicExpression *se, RegisterOperand &reg, __uint flag) {
  this->taintEngine.setTaintReg(reg.getTritonRegId(), flag);
  se->isTainted = flag;
}


void AnalysisProcessor::untaintReg(RegisterOperand &reg) {
  this->taintEngine.untaintReg(reg.getTritonRegId());
}


void AnalysisProcessor::taintMem(MemoryOperand &mem) {
  this->taintEngine.taintMem(mem.getAddress());
}


void AnalysisProcessor::untaintMem(MemoryOperand &mem) {
  this->taintEngine.untaintMem(mem.getAddress());
}


void AnalysisProcessor::aluSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst) {
  __uint regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  __uint regIdDst = regDst.getTritonRegId();
  __uint regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 writeSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint memAddrDst = memDst.getAddress();
  __uint memAddrSrc = memSrc.getAddress();

  /* Taint parent se */
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memAddrDst, memAddrSrc, writeSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != writeSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = this->taintEngine.isMemTainted(memAddrDst + i) | this->taintEngine.isMemTainted(memAddrSrc + i);
  }
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  __uint regIdDst = regDst.getTritonRegId();
  __uint memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint32 writeSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint memAddrDst = memDst.getAddress();

  /* Taint parent se */
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memAddrDst, writeSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != writeSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = se->isTainted;
  }
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint32 writeSize) {
  SymbolicExpression  *byte;
  __uint              byteId;
  __uint memAddrDst = memDst.getAddress();
  __uint regIdSrc = regSrc.getTritonRegId();

  /* Taint parent se */
  se->isTainted = this->taintEngine.aluSpreadTaintMemReg(memAddrDst, regIdSrc, writeSize);

  /* Taint each byte of reference expression */
  for (__uint i = 0; i != writeSize; i++) {
    byteId = this->symEngine.getMemSymbolicID(memAddrDst + i);
    if (byteId == UNSET)
      continue;
    byte = this->symEngine.getExpressionFromId(byteId);
    byte->isTainted = se->isTainted;
  }
}


// SolverEngine Facade
// -------------------

SolverEngine &AnalysisProcessor::getSolverEngine(void) {
  return this->solverEngine;
}


std::list<Smodel> AnalysisProcessor::getModel(smt2lib::smtAstAbstractNode *node) {
  return this->solverEngine.getModel(node);
}


std::vector<std::list<Smodel>> AnalysisProcessor::getModels(smt2lib::smtAstAbstractNode *node, __uint limit) {
  return this->solverEngine.getModels(node, limit);
}


// Statistics Facade
// -----------------

Stats &AnalysisProcessor::getStats(void) {
  return this->stats;
}


void AnalysisProcessor::incNumberOfExpressions(void) {
  this->stats.incNumberOfExpressions();
}


void AnalysisProcessor::incNumberOfExpressions(__uint val) {
  this->stats.incNumberOfExpressions(val);
}


void AnalysisProcessor::incNumberOfUnknownInstruction(void) {
  this->stats.incNumberOfUnknownInstruction();
}


void AnalysisProcessor::incNumberOfBranchesTaken(void) {
  this->stats.incNumberOfBranchesTaken();
}


void AnalysisProcessor::incNumberOfBranchesTaken(bool isBranch) {
  if (isBranch)
    this->stats.incNumberOfBranchesTaken();
}


__uint AnalysisProcessor::getNumberOfBranchesTaken(void) {
  return this->stats.getNumberOfBranchesTaken();
}


__uint AnalysisProcessor::getNumberOfExpressions(void) {
  return this->stats.getNumberOfExpressions();
}


__uint AnalysisProcessor::getNumberOfUnknownInstruction(void) {
  return this->stats.getNumberOfUnknownInstruction();
}


__uint AnalysisProcessor::getTimeOfExecution(void) {
  return this->stats.getTimeOfExecution();
}


// Snapshot Engine Facade
// ----------------------

SnapshotEngine &AnalysisProcessor::getSnapshotEngine(void) {
  return this->snapshotEngine;
}


bool AnalysisProcessor::isSnapshotLocked(void) {
  return this->snapshotEngine.isLocked();
}


void AnalysisProcessor::addSnapshotModification(__uint addr, char byte) {
  this->snapshotEngine.addModification(addr, byte);
}


void AnalysisProcessor::takeSnapshot(void) {
  CONTEXT *ctx = static_cast<CONTEXT*>(this->getCurrentCtxH()->getCtx());
  this->snapshotEngine.takeSnapshot(this->symEngine, this->taintEngine, ctx);
}


void AnalysisProcessor::restoreSnapshot(void) {
  CONTEXT *ctx = static_cast<CONTEXT*>(this->getCurrentCtxH()->getCtx());
  this->updateCurrentCtxH(new PINContextHandler(this->snapshotEngine.getCtx(), this->getThreadID()));
  this->snapshotEngine.restoreSnapshot(&this->symEngine, &this->taintEngine, ctx);
}


void AnalysisProcessor::disableSnapshot(void) {
  this->snapshotEngine.disableSnapshot();
}


bool AnalysisProcessor::isSnapshotEnabled(void) {
  if (this->snapshotEngine.isLocked())
    return false;
  return true;
}


bool AnalysisProcessor::isSnapshotMustBeRestored(void) {
  return this->snapshotEngine.isMustBeRestored();
}


void AnalysisProcessor::setSnapshotRestoreFlag(bool flag) {
  this->snapshotEngine.setRestore(flag);
}


// Evaluator Facade
// ----------------

uint512 AnalysisProcessor::evaluateAST(smt2lib::smtAstAbstractNode *node) {
  Z3ast z3ast{};
  Z3Result result = z3ast.eval(*node);
  uint512 nbResult{result.getStringValue()};
  return nbResult;
}

#endif /* LIGHT_VERSION */

