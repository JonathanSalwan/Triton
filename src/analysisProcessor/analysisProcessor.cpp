#include "AnalysisProcessor.h"
#include "PINContextHandler.h"


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
  if (this->currentCtxH != nullptr)
    delete this->currentCtxH;
  this->currentCtxH = ctxtHandler;
}


ContextHandler *AnalysisProcessor::getCurrentCtxH(void)
{
  return this->currentCtxH;
}


// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void)
{
  return this->symEngine;
}


SymbolicElement *AnalysisProcessor::createRegSE(std::stringstream &expr, uint64_t regID)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  this->symEngine.symbolicReg[regID] = se->getID();

  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(std::stringstream &expr, uint64_t regID, std::string comment)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr, comment);
  this->symEngine.symbolicReg[regID] = se->getID();

  return se;
}


SymbolicElement *AnalysisProcessor::createMemSE(std::stringstream &expr, uint64_t address)
{
  SymbolicElement *se = symEngine.newSymbolicElement(expr);
  symEngine.addMemoryReference(address, se->getID());

  return se;
}


SymbolicElement *AnalysisProcessor::createMemSE(std::stringstream &expr, uint64_t address, std::string comment)
{
  SymbolicElement *se = symEngine.newSymbolicElement(expr, comment);
  symEngine.addMemoryReference(address, se->getID());

  return se;
}


SymbolicElement *AnalysisProcessor::createSE(std::stringstream &expr)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  return se;
}


SymbolicElement *AnalysisProcessor::createSE(std::stringstream &expr, std::string comment)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr, comment);
  return se;
}


uint64_t AnalysisProcessor::getRegSymbolicID(uint64_t regID)
{
  return this->symEngine.getRegSymbolicID(regID);
}


uint64_t AnalysisProcessor::getMemSymbolicID(uint64_t address)
{
  return this->symEngine.getMemSymbolicID(address);
}


uint64_t AnalysisProcessor::getSymVarFromMemory(uint64_t address)
{
  return this->symEngine.getSymVarFromMemory(address);
}


uint64_t AnalysisProcessor::getMemoryFromSymVar(uint64_t symVar)
{
  return this->symEngine.getMemoryFromSymVar(symVar);
}


SymbolicElement *AnalysisProcessor::getElementFromId(uint64_t id)
{
  return this->symEngine.getElementFromId(id);
}


std::string AnalysisProcessor::getBacktrackedExpressionFromId(uint64_t id)
{
  return this->symEngine.getBacktrackedExpressionFromId(id);
}


bool AnalysisProcessor::convertExprToSymVar(uint64_t exprId, uint64_t symVarSize)
{
  return this->symEngine.convertExprToSymVar(exprId, symVarSize);
}


bool AnalysisProcessor::assignExprToSymVar(uint64_t exprId, uint64_t symVarId)
{
  return this->symEngine.assignExprToSymVar(exprId, symVarId);
}


void AnalysisProcessor::addPathConstraint(uint64_t exprId)
{
  this->symEngine.addPathConstraint(exprId);
}


std::list<uint64_t> AnalysisProcessor::getPathConstraints(void)
{
  return this->symEngine.getPathConstraints();
}


// Taint Engine Facade
// -------------------

TaintEngine &AnalysisProcessor::getTaintEngine(void)
{
  return this->taintEngine;
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regDst, memSrc, readSize);

  /* Use symbolic variable if the memory is tainted */
  if (se->isTainted) {

    std::stringstream newExpr;
    uint64_t          symVarID;

    /* Check if this memory area is already known as a symbolic variable */
    symVarID = this->symEngine.getSymVarFromMemory(memSrc); // TODO: Must use the readSize
    if (symVarID == UNSET){
      symVarID = this->symEngine.getUniqueSymVarID();
      this->symEngine.addSmt2LibVarDecl(symVarID, readSize);
      this->symEngine.addSymVarMemoryReference(memSrc, symVarID);
    }

    newExpr << "SymVar_" << std::dec << symVarID;
    se->setSrcExpr(newExpr);
  }
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memDst, memSrc, readSize);

  /* Use symbolic variable if the memory is tainted */
  if (se->isTainted) {

    std::stringstream newExpr;
    uint64_t          symVarID;

    /* Check if this memory area is already known as a symbolic variable */
    symVarID = this->symEngine.getSymVarFromMemory(memSrc); // TODO: Must use the readSize
    if (symVarID == UNSET){
      symVarID = this->symEngine.getUniqueSymVarID();
      this->symEngine.addSmt2LibVarDecl(symVarID, readSize);
      this->symEngine.addSymVarMemoryReference(memSrc, symVarID);
    }

    newExpr << "SymVar_" << std::dec << symVarID;
    se->setSrcExpr(newExpr);
  }
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint64_t writeSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint64_t writeSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemReg(memDst, regSrc, writeSize);
}


bool AnalysisProcessor::isRegTainted(uint64_t reg)
{
  return this->taintEngine.isRegTainted(reg);
}


bool AnalysisProcessor::isMemTainted(uint64_t addr)
{
  return this->taintEngine.isMemTainted(addr);
}


void AnalysisProcessor::taintReg(uint64_t reg)
{
  this->taintEngine.taintReg(reg);
}


void AnalysisProcessor::setTaintMem(uint64_t mem, uint64_t flag)
{
  this->taintEngine.setTaintMem(mem, flag);
}


void AnalysisProcessor::setTaintReg(uint64_t reg, uint64_t flag)
{
  this->taintEngine.setTaintReg(reg, flag);
}


void AnalysisProcessor::untaintReg(uint64_t reg)
{
  this->taintEngine.untaintReg(reg);
}


void AnalysisProcessor::taintMem(uint64_t addr)
{
  this->taintEngine.taintMem(addr);
}


void AnalysisProcessor::untaintMem(uint64_t addr)
{
  this->taintEngine.untaintMem(addr);
}


void AnalysisProcessor::aluSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memDst, memSrc);
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regDst, memSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint32_t writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint32_t writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemReg(memDst, regSrc, writeSize);
}


// SolverEngine Facade

SolverEngine &AnalysisProcessor::getSolverEngine(void)
{
  return this->solverEngine;
}


std::list< std::pair<std::string, unsigned long long> > AnalysisProcessor::getModel(std::string expr)
{
  return this->solverEngine.getModel(expr);
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


void AnalysisProcessor::incNumberOfExpressions(uint64_t val)
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


uint64_t AnalysisProcessor::getNumberOfBranchesTaken(void)
{
  return this->stats.getNumberOfBranchesTaken();
}


uint64_t AnalysisProcessor::getNumberOfExpressions(void)
{
  return this->stats.getNumberOfExpressions();
}


uint64_t AnalysisProcessor::getNumberOfUnknownInstruction(void)
{
  return this->stats.getNumberOfUnknownInstruction();
}


uint64_t AnalysisProcessor::getTimeOfExecution(void)
{
  return this->stats.getTimeOfExecution();
}


// ContextHandler Facade

/* Returns the thread id  */
uint32_t AnalysisProcessor::getThreadID(void)
{
  if (!this->currentCtxH)
    return -1;
  return this->currentCtxH->getThreadID();
}


// There is no verification on the validity of the ID.
uint64_t AnalysisProcessor::getRegisterValue(uint64_t regID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getRegisterValue(regID);
}


uint64_t AnalysisProcessor::getFlagValue(uint64_t flagID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getFlagValue(flagID);
}


__uint128_t AnalysisProcessor::getSSERegisterValue(uint64_t regID)
{
  if (!this->currentCtxH)
    return 0;
  return this->currentCtxH->getSSERegisterValue(regID);
}


// Returns the concret Carry Flag value
uint64_t AnalysisProcessor::getCFValue(void)
{
  uint64_t rflags;
  if (!this->currentCtxH)
    return 0;
  rflags = this->currentCtxH->getRegisterValue(ID_RFLAGS);
  return rflags & 1;
}


// There is no verification on the validity of the ID.
void AnalysisProcessor::setRegisterValue(uint64_t regID, uint64_t value)
{
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setRegisterValue(regID, value);
}


void AnalysisProcessor::setSSERegisterValue(uint64_t regID, __uint128_t value)
{
  if (!this->currentCtxH)
    return ;
  this->currentCtxH->setSSERegisterValue(regID, value);
}


uint64_t AnalysisProcessor::getMemValue(uint64_t mem, uint32_t readSize)
{
  return this->currentCtxH->getMemValue(mem, readSize);
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


void AnalysisProcessor::saveTrace(std::stringstream &file)
{
  if (file.str().empty() == false)
    this->trace.save(file);
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


void AnalysisProcessor::addSnapshotModification(uint64_t addr, char byte)
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


bool AnalysisProcessor::isSnapshotEnable(void)
{
  if (this->snapshotEngine.isLocked())
    return false;
  return true;
}


