/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <AnalysisProcessor.h>
#include <PINContextHandler.h>


AnalysisProcessor::AnalysisProcessor():
  symEngine(),
  solverEngine(&this->symEngine),
  taintEngine(),
  snapshotEngine(),
  stats(),
  trace()
{
  this->currentCtxH = nullptr;
}


void AnalysisProcessor::updateCurrentCtxH(ContextHandler *ctxtHandler)
{
  delete this->currentCtxH;
  this->currentCtxH = ctxtHandler;
}


ContextHandler *AnalysisProcessor::getCurrentCtxH(void)
{
  return this->currentCtxH;
}


void AnalysisProcessor::lock(void)
{
  PIN_LockClient();
}


void AnalysisProcessor::unlock(void)
{
  PIN_UnlockClient();
}


// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void)
{
  return this->symEngine;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID)
{
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, std::string comment)
{
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, comment);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, uint64 regSize)
{
  smt2lib::smtAstAbstractNode *finalExpr = nullptr, *origReg = nullptr;

  origReg = this->buildSymbolicRegOperand(regID, REG_SIZE);

  switch (regSize) {
    case BYTE_SIZE:
      finalExpr = smt2lib::concat(smt2lib::extract(63, 8, origReg), expr);
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

  SymbolicExpression *se = this->symEngine.newSymbolicExpression(finalExpr);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addExpression(se);

  return se;
}


SymbolicExpression *AnalysisProcessor::createRegSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 regID, uint64 regSize, std::string comment)
{
  smt2lib::smtAstAbstractNode *finalExpr = nullptr, *origReg = nullptr;

  origReg = this->buildSymbolicRegOperand(regID, REG_SIZE);

  switch (regSize) {
    case BYTE_SIZE:
      finalExpr = smt2lib::concat(smt2lib::extract(63, 8, origReg), expr);
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
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addExpression(se);

  return se;
}


SymbolicExpression *AnalysisProcessor::createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 address, uint64 writeSize)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *tmp;
  std::list<smt2lib::smtAstAbstractNode *> ret;

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize) {
    /* Extract each byte of the memory */
    tmp = smt2lib::extract(((writeSize * REG_SIZE) - 1), ((writeSize * REG_SIZE) - REG_SIZE), expr);
    se = symEngine.newSymbolicExpression(tmp, "byte reference");
    ret.push_back(tmp);
    inst.addExpression(se);
    /* Assign memory with little endian */
    this->symEngine.addMemoryReference((address + writeSize) - 1, se->getID());
    writeSize--;
  }

  /* If there is only one reference, we return the symbolic expression */
  if (ret.size() == 1)
    return se;

  /* Otherwise, we return the concatenation of all expressions */
  return symEngine.newSymbolicExpression(smt2lib::concat(ret), "concat reference");
}


SymbolicExpression *AnalysisProcessor::createMemSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, uint64 address, uint64 writeSize, std::string comment)
{
  SymbolicExpression *se;
  smt2lib::smtAstAbstractNode *tmp;
  std::list<smt2lib::smtAstAbstractNode *> ret;

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


SymbolicExpression *AnalysisProcessor::createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr)
{
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr);
  inst.addExpression(se);
  return se;
}


SymbolicExpression *AnalysisProcessor::createSE(Inst &inst, smt2lib::smtAstAbstractNode *expr, std::string comment)
{
  SymbolicExpression *se = this->symEngine.newSymbolicExpression(expr, comment);
  inst.addExpression(se);
  return se;
}


uint64 AnalysisProcessor::getRegSymbolicID(uint64 regID)
{
  return this->symEngine.getRegSymbolicID(regID);
}


uint64 AnalysisProcessor::getMemSymbolicID(uint64 address)
{
  return this->symEngine.getMemSymbolicID(address);
}


SymbolicVariable *AnalysisProcessor::getSymVar(uint64 symVarId)
{
  return this->symEngine.getSymVar(symVarId);
}


SymbolicVariable *AnalysisProcessor::getSymVar(std::string symVarName)
{
  return this->symEngine.getSymVar(symVarName);
}


std::vector<SymbolicVariable *> AnalysisProcessor::getSymVars(void)
{
  return this->symEngine.getSymVars();
}


SymbolicExpression *AnalysisProcessor::getExpressionFromId(uint64 id)
{
  return this->symEngine.getExpressionFromId(id);
}


std::vector<SymbolicExpression *> AnalysisProcessor::getExpressions(void)
{
  return this->symEngine.getExpressions();
}


std::list<SymbolicExpression *> AnalysisProcessor::getTaintedExpressions(void)
{
  return this->symEngine.getTaintedExpressions();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::getFullExpression(smt2lib::smtAstAbstractNode *node)
{
  return this->symEngine.getFullExpression(smt2lib::newInstance(node));
}


SymbolicVariable *AnalysisProcessor::convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable *symVar = this->symEngine.convertExprToSymVar(exprId, symVarSize, symVarComment);
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment)
{
  SymbolicVariable *symVar = this->symEngine.convertMemToSymVar(memAddr, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(this->getMemValue(memAddr,symVarSize));
  return symVar;
}


SymbolicVariable *AnalysisProcessor::convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment)
{
  uint128 mask     = 1;
  mask             = (mask << symVarSize) - 1;
  uint128 regValue = this->getRegisterValue(regId) & mask;
  
  SymbolicVariable *symVar = this->symEngine.convertRegToSymVar(regId, symVarSize, symVarComment);
  symVar->setSymVarConcreteValue(regValue);
  return symVar;
}


void AnalysisProcessor::addPathConstraint(uint64 exprId)
{
  this->symEngine.addPathConstraint(exprId);
}


std::list<uint64> AnalysisProcessor::getPathConstraints(void)
{
  return this->symEngine.getPathConstraints();
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(uint64 regID, uint64 regSize)
{
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symReg = this->getRegSymbolicID(regID);
  uint64 low    = 0;
  uint64 high   = (regSize * REG_SIZE) - 1;

  if (symReg != UNSET)
    op = smt2lib::extract(high, low, smt2lib::reference(symReg));
  else {
    if (regID >= ID_XMM0 && regID <= ID_XMM15)
      op = smt2lib::extract(high, low, smt2lib::bv(this->getSSERegisterValue(regID), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(high, low, smt2lib::bv(this->getRegisterValue(regID), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicRegOperand(uint64 regID, uint64 regSize, uint64 highExtract, uint64 lowExtract)
{
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symReg = this->getRegSymbolicID(regID);

  if (symReg != UNSET)
    op = smt2lib::extract(highExtract, lowExtract, smt2lib::reference(symReg));
  else {
    if (regID >= ID_XMM0 && regID <= ID_XMM15)
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getSSERegisterValue(regID), SSE_REG_SIZE_BIT));
    else
      op = smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getRegisterValue(regID), REG_SIZE_BIT));
  }

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicMemOperand(uint64 mem, uint64 memSize)
{
  std::list<smt2lib::smtAstAbstractNode *> opVec;
  smt2lib::smtAstAbstractNode *tmp = nullptr;
  uint64 symMem;

  while (memSize) {
    symMem = this->getMemSymbolicID(mem + memSize - 1);
    if (symMem != UNSET) {
      tmp = smt2lib::reference(symMem);
      opVec.push_back(smt2lib::extract(7, 0, tmp));
    }
    else {
      tmp = smt2lib::bv(this->getMemValue(mem + memSize - 1, 1), REG_SIZE);
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


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(uint64 flagID, uint64 size)
{
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op = smt2lib::zx((size * REG_SIZE) - 1, smt2lib::reference(symFlag));
  else
    op = smt2lib::bv(this->getFlagValue(flagID), size * REG_SIZE);

  return op;
}


smt2lib::smtAstAbstractNode *AnalysisProcessor::buildSymbolicFlagOperand(uint64 flagID)
{
  smt2lib::smtAstAbstractNode *op = nullptr;
  uint64 symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op = smt2lib::reference(symFlag);
  else
    op = smt2lib::bv(this->getFlagValue(flagID), 1);

  return op;
}


void AnalysisProcessor::concretizeAllReg(void)
{
  this->symEngine.concretizeAllReg();
}


void AnalysisProcessor::concretizeAllMem(void)
{
  this->symEngine.concretizeAllMem();
}


void AnalysisProcessor::concretizeReg(uint64 regID)
{
  this->symEngine.concretizeReg(regID);
}


void AnalysisProcessor::concretizeMem(uint64 mem)
{
  this->symEngine.concretizeMem(mem);
}


// Taint Engine Facade
// -------------------

TaintEngine &AnalysisProcessor::getTaintEngine(void)
{
  return this->taintEngine;
}


void AnalysisProcessor::assignmentSpreadTaintExprMem(SymbolicExpression *se, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprMem(memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprReg(SymbolicExpression *se, uint64 regSrc)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprReg(regSrc);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegMem(SymbolicExpression *se, uint64 regSrc, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegMem(regSrc, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegReg(SymbolicExpression *se, uint64 regSrc1, uint64 regSrc2)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegReg(regSrc1, regSrc2);
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicExpression *se, uint64 regDst, uint64 regSrc)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicExpression *se, uint64 regDst)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicExpression *se, uint64 regDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regDst, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicExpression *se, uint64 memDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memDst, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicExpression *se, uint64 memDst, uint64 writeSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicExpression *se, uint64 memDst, uint64 regSrc, uint64 writeSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemReg(memDst, regSrc, writeSize);
}


bool AnalysisProcessor::isRegTainted(uint64 reg)
{
  return this->taintEngine.isRegTainted(reg);
}


bool AnalysisProcessor::isMemTainted(uint64 addr)
{
  return this->taintEngine.isMemTainted(addr);
}


void AnalysisProcessor::taintReg(uint64 reg)
{
  this->taintEngine.taintReg(reg);
}


void AnalysisProcessor::setTaintMem(SymbolicExpression *se, uint64 mem, uint64 flag)
{
  this->taintEngine.setTaintMem(mem, flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicExpression *se, uint64 reg, uint64 flag)
{
  this->taintEngine.setTaintReg(reg, flag);
  se->isTainted = flag;
}


void AnalysisProcessor::untaintReg(uint64 reg)
{
  this->taintEngine.untaintReg(reg);
}


void AnalysisProcessor::taintMem(uint64 addr)
{
  this->taintEngine.taintMem(addr);
}


void AnalysisProcessor::untaintMem(uint64 addr)
{
  this->taintEngine.untaintMem(addr);
}


void AnalysisProcessor::aluSpreadTaintRegImm(SymbolicExpression *se, uint64 regDst)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicExpression *se, uint64 regDst, uint64 regSrc)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicExpression *se, uint64 memDst, uint64 memSrc, uint32 writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memDst, memSrc, writeSize);
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicExpression *se, uint64 regDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regDst, memSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicExpression *se, uint64 memDst, uint32 writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicExpression *se, uint64 memDst, uint64 regSrc, uint32 writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemReg(memDst, regSrc, writeSize);
}


// SolverEngine Facade

SolverEngine &AnalysisProcessor::getSolverEngine(void)
{
  return this->solverEngine;
}


std::list<Smodel> AnalysisProcessor::getModel(smt2lib::smtAstAbstractNode *node)
{
  return this->solverEngine.getModel(node);
}


std::vector<std::list<Smodel>> AnalysisProcessor::getModels(smt2lib::smtAstAbstractNode *node, uint64 limit)
{
  return this->solverEngine.getModels(node, limit);
}


// Statistics Facade

Stats &AnalysisProcessor::getStats(void)
{
  return this->stats;
}


void AnalysisProcessor::incNumberOfExpressions(void)
{
  this->stats.incNumberOfExpressions();
}


void AnalysisProcessor::incNumberOfExpressions(uint64 val)
{
  this->stats.incNumberOfExpressions(val);
}


void AnalysisProcessor::incNumberOfUnknownInstruction(void)
{
  this->stats.incNumberOfUnknownInstruction();
}


void AnalysisProcessor::incNumberOfBranchesTaken(void)
{
  this->stats.incNumberOfBranchesTaken();
}


void AnalysisProcessor::incNumberOfBranchesTaken(bool isBranch)
{
  if (isBranch)
    this->stats.incNumberOfBranchesTaken();
}


uint64 AnalysisProcessor::getNumberOfBranchesTaken(void)
{
  return this->stats.getNumberOfBranchesTaken();
}


uint64 AnalysisProcessor::getNumberOfExpressions(void)
{
  return this->stats.getNumberOfExpressions();
}


uint64 AnalysisProcessor::getNumberOfUnknownInstruction(void)
{
  return this->stats.getNumberOfUnknownInstruction();
}


uint64 AnalysisProcessor::getTimeOfExecution(void)
{
  return this->stats.getTimeOfExecution();
}


// ContextHandler Facade

/* Returns the thread id  */
uint32 AnalysisProcessor::getThreadID(void)
{
  if (!this->currentCtxH)
    return -1;
  return this->currentCtxH->getThreadID();
}


// There is no verification on the validity of the ID.
uint64 AnalysisProcessor::getRegisterValue(uint64 regID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getRegisterValue(regID);
}


uint64 AnalysisProcessor::getFlagValue(uint64 flagID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getFlagValue(flagID);
}


uint128 AnalysisProcessor::getSSERegisterValue(uint64 regID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getSSERegisterValue(regID);
}


// There is no verification on the validity of the ID.
void AnalysisProcessor::setRegisterValue(uint64 regID, uint64 value)
{
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setRegisterValue(regID, value);
}


void AnalysisProcessor::setSSERegisterValue(uint64 regID, uint128 value)
{
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setSSERegisterValue(regID, value);
}


uint128 AnalysisProcessor::getMemValue(uint64 mem, uint32 readSize)
{
  return this->currentCtxH->getMemValue(mem, readSize);
}


void AnalysisProcessor::setMemValue(uint64 mem, uint32 writeSize, uint128 value)
{
  this->currentCtxH->setMemValue(mem, writeSize, value);
}


// Trace Facade

Trace &AnalysisProcessor::getTrace(void)
{
  return this->trace;
}


void AnalysisProcessor::addInstructionToTrace(Inst *instruction)
{
  this->trace.addInstruction(instruction);
}


Inst *AnalysisProcessor::getLastInstruction(void)
{
  return this->trace.getLastInstruction();
}


// Snapshot Engine Facade
// -------------------

SnapshotEngine &AnalysisProcessor::getSnapshotEngine(void)
{
  return this->snapshotEngine;
}


bool AnalysisProcessor::isSnapshotLocked(void)
{
  return this->snapshotEngine.isLocked();
}


void AnalysisProcessor::addSnapshotModification(uint64 addr, char byte)
{
  this->snapshotEngine.addModification(addr, byte);
}


void AnalysisProcessor::takeSnapshot(void)
{
  CONTEXT *ctx = static_cast<CONTEXT*>(this->getCurrentCtxH()->getCtx());
  this->snapshotEngine.takeSnapshot(this->symEngine, this->taintEngine, ctx);
}


void AnalysisProcessor::restoreSnapshot(void)
{
  CONTEXT *ctx = static_cast<CONTEXT*>(this->getCurrentCtxH()->getCtx());
  this->updateCurrentCtxH(new PINContextHandler(this->snapshotEngine.getCtx(), this->getThreadID()));
  this->snapshotEngine.restoreSnapshot(&this->symEngine, &this->taintEngine, ctx);
}


void AnalysisProcessor::disableSnapshot(void)
{
  this->snapshotEngine.disableSnapshot();
}


bool AnalysisProcessor::isSnapshotEnabled(void)
{
  if (this->snapshotEngine.isLocked())
    return false;
  return true;
}


// Evaluator
// ---------

uint512 AnalysisProcessor::evaluateAST(smt2lib::smtAstAbstractNode *node)
{
  Z3ast z3ast{};
  Z3Result result = z3ast.eval(*node);
  uint512 nbResult{result.getStringValue()};
  return nbResult;
}


