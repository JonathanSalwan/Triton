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
reg_size AnalysisProcessor::getRegisterValue(RegisterOperand &reg) {
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getRegisterValue(reg.getTritonRegId());
}


reg_size AnalysisProcessor::getFlagValue(RegisterOperand &flag) {
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
void AnalysisProcessor::setRegisterValue(RegisterOperand &reg, reg_size value) {
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


uint128 AnalysisProcessor::getMemValue(reg_size mem, uint32 readSize) {
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


void AnalysisProcessor::clearTrace(void) {
  this->getTrace().getInstructions().clear();
}


#ifndef LIGHT_VERSION

// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void) {
  return this->symEngine;
}


SymbolicExpression *AnalysisProcessor::createFlagSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &flag, std::string comment) {
  reg_size flagId = flag.getTritonRegId();
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, SymExpr::REG, comment);
  this->symEngine.symbolicReg[flagId] = se->getID();
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, RegisterOperand &reg, reg_size regSize, std::string comment) {
  reg_size regId = reg.getTritonRegId();
  smt2lib::smtAstAbstractNode *finalExpr = nullptr, *origReg = nullptr;

  origReg = this->buildSymbolicRegOperand(reg, REG_SIZE, (REG_SIZE_BIT - 1), 0);

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
      /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
      finalExpr = smt2lib::zx(DWORD_SIZE_BIT, expr);
      break;

    case QWORD_SIZE:
    case DQWORD_SIZE:
      finalExpr = expr;
      break;
  }

  SymbolicExpression *se = this->symEngine.newSymbolicExpression(finalExpr, SymExpr::REG, comment);
  this->symEngine.symbolicReg[regId] = se->getID();
  inst.addExpression(se);

  return se;
}


SymbolicExpression *AnalysisProcessor::createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, MemoryOperand &mem, reg_size writeSize, std::string comment) {
  SymbolicExpression *se = nullptr;
  smt2lib::smtAstAbstractNode *tmp;
  std::list<smt2lib::smtAstAbstractNode *> ret;
  reg_size address = mem.getAddress();

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize) {
    /* Extract each byte of the memory */
    tmp = smt2lib::extract(((writeSize * REG_SIZE) - 1), ((writeSize * REG_SIZE) - REG_SIZE), expr);
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


SymbolicExpression *AnalysisProcessor::createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment) {
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, SymExpr::UNDEF, comment);
  inst.addExpression(se);
  return se;
}


reg_size AnalysisProcessor::getRegSymbolicID(RegisterOperand &reg) {
  return this->symEngine.getRegSymbolicID(reg.getTritonRegId());
}


reg_size AnalysisProcessor::getMemSymbolicID(MemoryOperand &mem) {
  return this->symEngine.getMemSymbolicID(mem.getAddress());
}


reg_size AnalysisProcessor::getMemSymbolicID(reg_size address) {
  return this->symEngine.getMemSymbolicID(address);
}


SymbolicVariable *AnalysisProcessor::getSymVar(reg_size symVarId) {
  return this->symEngine.getSymVar(symVarId);
}


SymbolicVariable *AnalysisProcessor::getSymVar(std::string symVarName) {
  return this->symEngine.getSymVar(symVarName);
}


std::vector<SymbolicVariable *> AnalysisProcessor::getSymVars(void) {
  return this->symEngine.getSymVars();
}


SymbolicExpression *AnalysisProcessor::getExpressionFromId(reg_size id) {
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


SymbolicVariable *AnalysisProcessor::convertExprToSymVar(reg_size exprId, reg_size symVarSize, std::string symVarComment) {
  SymbolicVariable *symVar = this->symEngine.convertExprToSymVar(exprId, symVarSize, symVarComment);
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertMemToSymVar(MemoryOperand &mem, reg_size symVarSize, std::string symVarComment) {
  reg_size address = mem.getAddress();
  SymbolicVariable *symVar = this->symEngine.convertMemToSymVar(address, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(this->getMemValue(address, symVarSize));
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertRegToSymVar(RegisterOperand &reg, reg_size symVarSize, std::string symVarComment) {
  reg_size regId     = reg.getTritonRegId();
  uint128 mask     = 1;
  mask             = (mask << symVarSize) - 1;
  uint128 regValue = this->getRegisterValue(reg) & mask;

  SymbolicVariable *symVar = this->symEngine.convertRegToSymVar(regId, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(regValue);
  return symVar;
}


void AnalysisProcessor::addPathConstraint(reg_size exprId) {
  this->symEngine.addPathConstraint(exprId);
}


std::list<reg_size> AnalysisProcessor::getPathConstraints(void) {
  return this->symEngine.getPathConstraints();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, reg_size regSize) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  reg_size regId  = reg.getTritonRegId();
  reg_size symReg = this->getRegSymbolicID(reg);
  reg_size low    = reg.getLow();
  reg_size high   = !low ? (regSize * REG_SIZE) - 1 : reg.getHigh(); // TMP fix for #170
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
    if (isSSERegId(regId))
      op = smt2lib::extract(high, low, smt2lib::bv(this->getSSERegisterValue(reg), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(high, low, smt2lib::bv(this->getRegisterValue(reg), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(RegisterOperand &reg, reg_size regSize, reg_size highExtract, reg_size lowExtract) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  reg_size regId  = reg.getTritonRegId();
  reg_size symReg = this->getRegSymbolicID(reg);

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


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicMemOperand(MemoryOperand &mem, reg_size memSize) {
  std::list<smt2lib::smtAstAbstractNode *> opVec;
  smt2lib::smtAstAbstractNode *tmp = nullptr;
  reg_size address = mem.getAddress();
  reg_size symMem;

  while (memSize) {
    symMem = this->getMemSymbolicID(address + memSize - 1);
    if (symMem != UNSET) {
      tmp = smt2lib::reference(symMem);
      opVec.push_back(smt2lib::extract((BYTE_SIZE_BIT - 1), 0, tmp));
    }
    else {
      tmp = smt2lib::bv(this->getMemValue(address + memSize - 1, 1), REG_SIZE);
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


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag, reg_size size) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  reg_size symFlag = this->getRegSymbolicID(flag);

  if (symFlag != UNSET)
    op = smt2lib::zx((size * REG_SIZE) - 1, smt2lib::reference(symFlag));
  else
    op = smt2lib::bv(this->getFlagValue(flag), size * REG_SIZE);

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(RegisterOperand &flag) {
  smt2lib::smtAstAbstractNode *op = nullptr;
  reg_size symFlag = this->getRegSymbolicID(flag);

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
  reg_size memAddrSrc = mem.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprMem(memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprReg(SymbolicExpression *se, RegisterOperand &reg) {
  reg_size regIdSrc = reg.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprReg(regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegMem(SymbolicExpression *se, RegisterOperand &regSrc, MemoryOperand &memSrc, uint32 readSize) {
  reg_size regIdSrc = regSrc.getTritonRegId();
  reg_size memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegMem(regIdSrc, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegReg(SymbolicExpression *se, RegisterOperand &regSrc1, RegisterOperand &regSrc2) {
  reg_size regIdSrc1 = regSrc1.getTritonRegId();
  reg_size regIdSrc2 = regSrc2.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegReg(regIdSrc1, regIdSrc2);
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  reg_size regIdDst = regDst.getTritonRegId();
  reg_size regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicExpression *se, RegisterOperand &regDst) {
  reg_size regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  reg_size regIdDst = regDst.getTritonRegId();
  reg_size memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 readSize) {
  reg_size memAddrDst = memDst.getAddress();
  reg_size memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memAddrDst, memAddrSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, reg_size writeSize) {
  reg_size memAddrDst = memDst.getAddress();
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memAddrDst, writeSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, reg_size writeSize) {
  reg_size memAddrDst = memDst.getAddress();
  reg_size regIdSrc = regSrc.getTritonRegId();
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


void AnalysisProcessor::setTaintMem(SymbolicExpression *se, MemoryOperand &mem, reg_size flag) {
  this->taintEngine.setTaintMem(mem.getAddress(), flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicExpression *se, RegisterOperand &reg, reg_size flag) {
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
  reg_size regIdDst = regDst.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regIdDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicExpression *se, RegisterOperand &regDst, RegisterOperand &regSrc) {
  reg_size regIdDst = regDst.getTritonRegId();
  reg_size regIdSrc = regSrc.getTritonRegId();
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regIdDst, regIdSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicExpression *se, MemoryOperand &memDst, MemoryOperand &memSrc, uint32 writeSize) {
  reg_size memAddrDst = memDst.getAddress();
  reg_size memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memAddrDst, memAddrSrc, writeSize);
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicExpression *se, RegisterOperand &regDst, MemoryOperand &memSrc, uint32 readSize) {
  reg_size regIdDst = regDst.getTritonRegId();
  reg_size memAddrSrc = memSrc.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regIdDst, memAddrSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicExpression *se, MemoryOperand &memDst, uint32 writeSize) {
  reg_size memAddrDst = memDst.getAddress();
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memAddrDst, writeSize);
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicExpression *se, MemoryOperand &memDst, RegisterOperand &regSrc, uint32 writeSize) {
  reg_size memAddrDst = memDst.getAddress();
  reg_size regIdSrc = regSrc.getTritonRegId();
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


std::vector<std::list<Smodel>> AnalysisProcessor::getModels(smt2lib::smtAstAbstractNode *node, reg_size limit) {
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


void AnalysisProcessor::incNumberOfExpressions(reg_size val) {
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


reg_size AnalysisProcessor::getNumberOfBranchesTaken(void) {
  return this->stats.getNumberOfBranchesTaken();
}


reg_size AnalysisProcessor::getNumberOfExpressions(void) {
  return this->stats.getNumberOfExpressions();
}


reg_size AnalysisProcessor::getNumberOfUnknownInstruction(void) {
  return this->stats.getNumberOfUnknownInstruction();
}


reg_size AnalysisProcessor::getTimeOfExecution(void) {
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


void AnalysisProcessor::addSnapshotModification(reg_size addr, char byte) {
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

