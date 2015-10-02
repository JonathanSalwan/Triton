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
uint64 AnalysisProcessor::getRegisterValue(RegisterOperand &reg) {
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getRegisterValue(reg.getTritonRegId());
}


uint64 AnalysisProcessor::getFlagValue(RegisterOperand &flag) {
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
void AnalysisProcessor::setRegisterValue(RegisterOperand &reg, uint64 value) {
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


uint128 AnalysisProcessor::getMemValue(uint64 mem, uint32 readSize) {
  return this->currentCtxH->getMemValue(mem, readSize);
}


void AnalysisProcessor::setMemValue(MemoryOperand &mem, uint32 writeSize, uint128 value) {
  this->currentCtxH->setMemValue(mem.getAddress(), writeSize, value);
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


#ifndef LIGHT_VERSION

// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void) {
  return this->symEngine;
}


SymbolicExpression *AnalysisProcessor::createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment) {
  uint64 flagId = flag.getTritonRegId();
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, comment);
  this->symEngine.symbolicReg[flagId] = se->getID();
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, uint64 regSize, std::string comment) {
  uint64 regId = reg.getTritonRegId();
  smt2lib::smtAstAbstractNode *finalExpr = nullptr, *origReg = nullptr;

  origReg = this->buildSymbolicRegOperand(reg, REG_SIZE, 63, 0);

  switch (regSize) {
    case BYTE_SIZE:
      if (reg.getLow() == 0)
        finalExpr = smt2lib::concat(smt2lib::extract(63, 8, origReg), expr);
      else
        finalExpr = smt2lib::concat(smt2lib::extract(63, 16, origReg), smt2lib::concat(expr, smt2lib::extract(7, 0, origReg)));
      break;

    case WORD_SIZE:
      finalExpr = smt2lib::concat(smt2lib::extract(63, 16, origReg), expr);
      break;

    case DWORD_SIZE:
      /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
      finalExpr = smt2lib::zx(DWORD_SIZE_BIT, expr);
      break;

    case QWORD_SIZE:
    case DQWORD_SIZE:
      finalExpr = expr;
      break;
  }

  SymbolicExpression *se = this->symEngine.newSymbolicExpression(finalExpr, comment);
  this->symEngine.symbolicReg[regId] = se->getID();
  inst.addExpression(se);

  return se;
}


SymbolicExpression *AnalysisProcessor::createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, uint64 writeSize, std::string comment) {
  SymbolicExpression *se = nullptr;
  smt2lib::smtAstAbstractNode *tmp;
  std::list<smt2lib::smtAstAbstractNode *> ret;
  uint64 address = mem.getAddress();

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize) {
    /* Extract each byte of the memory */
    tmp = smt2lib::extract(((writeSize * REG_SIZE) - 1), ((writeSize * REG_SIZE) - REG_SIZE), expr);
    se  = symEngine.newSymbolicExpression(tmp, "byte reference");
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
  return symEngine.newSymbolicExpression(smt2lib::concat(ret), "concat reference");
}


SymbolicExpression *AnalysisProcessor::createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment) {
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, comment);
  inst.addExpression(se);
  return se;
}


uint64 AnalysisProcessor::getRegSymbolicID(RegisterOperand &reg) {
  return this->symEngine.getRegSymbolicID(reg.getTritonRegId());
}


uint64 AnalysisProcessor::getMemSymbolicID(MemoryOperand &mem) {
  return this->symEngine.getMemSymbolicID(mem.getAddress());
}


uint64 AnalysisProcessor::getMemSymbolicID(uint64 address) {
  return this->symEngine.getMemSymbolicID(address);
}


SymbolicVariable *AnalysisProcessor::getSymVar(uint64 symVarId) {
  return this->symEngine.getSymVar(symVarId);
}


SymbolicVariable *AnalysisProcessor::getSymVar(std::string symVarName) {
  return this->symEngine.getSymVar(symVarName);
}


std::vector<SymbolicVariable *> AnalysisProcessor::getSymVars(void) {
  return this->symEngine.getSymVars();
}


SymbolicExpression *AnalysisProcessor::getExpressionFromId(uint64 id) {
  return this->symEngine.getExpressionFromId(id);
}


std::vector<SymbolicExpression *> AnalysisProcessor::getExpressions(void) {
  return this->symEngine.getExpressions();
}


std::list<SymbolicExpression *> AnalysisProcessor::getTaintedExpressions(void) {
  return this->symEngine.getTaintedExpressions();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::getFullExpression(smt2lib::smtAstAbstractNode *node) {
  return this->symEngine.getFullExpression(smt2lib::newInstance(node));
}


SymbolicVariable *AnalysisProcessor::convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment) {
  SymbolicVariable *symVar = this->symEngine.convertExprToSymVar(exprId, symVarSize, symVarComment);
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertMemToSymVar(MemoryOperand &mem, uint64 symVarSize, std::string symVarComment) {
  uint64 address = mem.getAddress();
  SymbolicVariable *symVar = this->symEngine.convertMemToSymVar(address, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(this->getMemValue(address, symVarSize));
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertRegToSymVar(RegisterOperand &reg, uint64 symVarSize, std::string symVarComment) {
  uint64 regId     = reg.getTritonRegId();
  uint128 mask     = 1;
  mask             = (mask << symVarSize) - 1;
  uint128 regValue = this->getRegisterValue(reg) & mask;

  SymbolicVariable *symVar = this->symEngine.convertRegToSymVar(regId, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(regValue);
  return symVar;
}


void AnalysisProcessor::addPathConstraint(uint64 exprId) {
  this->symEngine.addPathConstraint(exprId);
}


std::list<uint64> AnalysisProcessor::getPathConstraints(void) {
  return this->symEngine.getPathConstraints();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, uint64 regSize) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 regId  = reg.getTritonRegId();
  uint64 symReg = this->getRegSymbolicID(reg);
  uint64 low    = reg.getLow();
  uint64 high   = !low ? (regSize * REG_SIZE) - 1 : reg.getHigh(); // TMP fix for #170
  /*
   * TODO
   * ----
   * We should use reg.getHigh() for every cases and remove regSize (#179).
   * Then, replace all:
   *
   *   - buildSymbolicRegOperand(ID_TMP_X, X_SIZE);
   *
   * To:
   *
   *   - buildSymbolicRegOperand(ID_TMP_X, HIGH, LOW);
   *
   */

  if (symReg != UNSET)
    op = smt2lib::extract(high, low, smt2lib::reference(symReg));
  else {
    if (regId >= ID_XMM0 && regId <= ID_XMM15)
      op = smt2lib::extract(high, low, smt2lib::bv(this->getSSERegisterValue(reg), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(high, low, smt2lib::bv(this->getRegisterValue(reg), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, uint64 regSize, uint64 highExtract, uint64 lowExtract) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 regId  = reg.getTritonRegId();
  uint64 symReg = this->getRegSymbolicID(reg);

  if (symReg != UNSET)
    op = smt2lib::extract(highExtract, lowExtract, smt2lib::reference(symReg));
  else {
    if (regId >= ID_XMM0 && regId <= ID_XMM15)
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getSSERegisterValue(reg), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getRegisterValue(reg), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicMemOperand(MemoryOperand &mem, uint64 memSize) {
  std::list<smt2lib::smtAstAbstractNode *> opVec;
  smt2lib::smtAstAbstractNode *tmp = nullptr;
  uint64 address = mem.getAddress();
  uint64 symMem;

  while (memSize) {
    symMem = this->getMemSymbolicID(address + memSize - 1);
    if (symMem != UNSET) {
      tmp = smt2lib::reference(symMem);
      opVec.push_back(smt2lib::extract(7, 0, tmp));
    }
    else {
      tmp = smt2lib::bv(this->getMemValue(address + memSize - 1, 1), REG_SIZE);
      opVec.push_back(smt2lib::extract(7, 0, tmp));
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


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag, uint64 size) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symFlag = this->getRegSymbolicID(flag);

  if (symFlag != UNSET)
    op = smt2lib::zx((size * REG_SIZE) - 1, smt2lib::reference(symFlag));
  else
    op = smt2lib::bv(this->getFlagValue(flag), size * REG_SIZE);

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symFlag = this->getRegSymbolicID(flag);

  if (symFlag != UNSET)
    op = smt2lib::reference(symFlag);
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


// Taint Engine Facade
// -------------------

TaintEngine &AnalysisProcessor::getTaintEngine(void) {
  return this->taintEngine;
}


void AnalysisProcessor::assignmentSpreadTaintExprMem(SymbolicExpression *se, MemoryOperand &mem, uint32 readSize) {
  uint64 memAddrSrc = mem.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprMem(memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprReg(SymbolicExpression *se, RegisterOperand &reg) {
  uint64 regIdSrc = reg.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprReg(regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegMem(SymbolicExpression *se, RegisterOperand &regSrc, MemoryOperand &memSrc, uint32 readSize) {
  uint64 regIdSrc = regSrc.getTritonRegId();
  uint64 memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegMem(regIdSrc, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegReg(SymbolicExpression *se, RegisterOperand &regSrc1, RegisterOperand &regSrc2) {
  uint64 regIdSrc1 = regSrc1.getTritonRegId();
  uint64 regIdSrc2 = regSrc2.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegReg(regIdSrc1, regIdSrc2);
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  uint64 regIdDst = regDst.getTritonRegId();
  uint64 regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst) {
  uint64 regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  uint64 regIdDst = regDst.getTritonRegId();
  uint64 memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize) {
  uint64 memAddrDst = memDst.getAddress();
  uint64 memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memAddrDst, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint64 writeSize) {
  uint64 memAddrDst = memDst.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memAddrDst, writeSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint64 writeSize) {
  uint64 memAddrDst = memDst.getAddress();
  uint64 regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemReg(memAddrDst, regIdSrc, writeSize);
}


bool AnalysisProcessor::isRegTainted(RegisterOperand &reg) {
  return this->taintEngine.isRegTainted(reg.getTritonRegId());
}


bool AnalysisProcessor::isMemTainted(MemoryOperand &addr) {
  return this->taintEngine.isMemTainted(addr.getAddress());
}


void AnalysisProcessor::taintReg(RegisterOperand &reg) {
  this->taintEngine.taintReg(reg.getTritonRegId());
}


void AnalysisProcessor::setTaintMem(SymbolicExpression *se, MemoryOperand &mem, uint64 flag) {
  this->taintEngine.setTaintMem(mem.getAddress(), flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicExpression *se, RegisterOperand &reg, uint64 flag) {
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
  uint64 regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  uint64 regIdDst = regDst.getTritonRegId();
  uint64 regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 writeSize) {
  uint64 memAddrDst = memDst.getAddress();
  uint64 memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memAddrDst, memAddrSrc, writeSize);
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  uint64 regIdDst = regDst.getTritonRegId();
  uint64 memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint32 writeSize) {
  uint64 memAddrDst = memDst.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memAddrDst, writeSize);
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint32 writeSize) {
  uint64 memAddrDst = memDst.getAddress();
  uint64 regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintMemReg(memAddrDst, regIdSrc, writeSize);
}


// SolverEngine Facade
// -------------------

SolverEngine &AnalysisProcessor::getSolverEngine(void) {
  return this->solverEngine;
}


std::list<Smodel> AnalysisProcessor::getModel(smt2lib::smtAstAbstractNode *node) {
  return this->solverEngine.getModel(node);
}


std::vector<std::list<Smodel>> AnalysisProcessor::getModels(smt2lib::smtAstAbstractNode *node, uint64 limit) {
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


void AnalysisProcessor::incNumberOfExpressions(uint64 val) {
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


uint64 AnalysisProcessor::getNumberOfBranchesTaken(void) {
  return this->stats.getNumberOfBranchesTaken();
}


uint64 AnalysisProcessor::getNumberOfExpressions(void) {
  return this->stats.getNumberOfExpressions();
}


uint64 AnalysisProcessor::getNumberOfUnknownInstruction(void) {
  return this->stats.getNumberOfUnknownInstruction();
}


uint64 AnalysisProcessor::getTimeOfExecution(void) {
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


void AnalysisProcessor::addSnapshotModification(uint64 addr, char byte) {
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


// Evaluator Facade
// ----------------

uint512 AnalysisProcessor::evaluateAST(smt2lib::smtAstAbstractNode *node) {
  Z3ast z3ast{};
  Z3Result result = z3ast.eval(*node);
  uint512 nbResult{result.getStringValue()};
  return nbResult;
}

#endif /* LIGHT_VERSION */


