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


// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine(void)
{
  return this->symEngine;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);
  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, std::string comment)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr, comment);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);
  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, uint64_t regSize)
{
  std::stringstream finalExpr, origReg;

  origReg << this->buildSymbolicRegOperand(regID, REG_SIZE);

  switch (regSize) {
    case BYTE_SIZE:
      finalExpr << smt2lib::concat(smt2lib::extract(63, 8, origReg.str()), expr.str());
      break;
    case WORD_SIZE:
      finalExpr << smt2lib::concat(smt2lib::extract(63, 16, origReg.str()), expr.str());
      break;
    case DWORD_SIZE:
      /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
      finalExpr << smt2lib::zx(expr.str(), DWORD_SIZE_BIT);
      break;
    case QWORD_SIZE:
      finalExpr << expr.str();
      break;
    case DQWORD_SIZE:
      finalExpr << expr.str();
      break;
  }

  SymbolicElement *se = this->symEngine.newSymbolicElement(finalExpr);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);

  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64_t regID, uint64_t regSize, std::string comment)
{
  std::stringstream finalExpr, origReg;

  origReg << this->buildSymbolicRegOperand(regID, REG_SIZE);

  switch (regSize) {
    case BYTE_SIZE:
      finalExpr << smt2lib::concat(smt2lib::extract(63, 8, origReg.str()), expr.str());
      break;
    case WORD_SIZE:
      finalExpr << smt2lib::concat(smt2lib::extract(63, 16, origReg.str()), expr.str());
      break;
    case DWORD_SIZE:
      /* In AMD64, if a reg32 is written, it clears the 32-bit MSB of the corresponding register (Thx Wisk!) */
      finalExpr << smt2lib::zx(expr.str(), DWORD_SIZE_BIT);
      break;
    case QWORD_SIZE:
      finalExpr << expr.str();
      break;
    case DQWORD_SIZE:
      finalExpr << expr.str();
      break;
  }

  SymbolicElement *se = this->symEngine.newSymbolicElement(finalExpr, comment);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);

  return se;
}


SymbolicElement *AnalysisProcessor::createMemSE(Inst &inst, std::stringstream &expr, uint64_t address, uint64_t writeSize)
{
  SymbolicElement   *ret = nullptr;
  std::stringstream tmp;

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize){
    /* Extract each byte if the size > 1 byte (8 bits) */
    if (writeSize > BYTE_SIZE){
      tmp.str(smt2lib::extract(((writeSize * REG_SIZE) - 1), ((writeSize * REG_SIZE) - REG_SIZE), expr.str()));
      SymbolicElement *se = symEngine.newSymbolicElement(tmp, "byte reference");
      inst.addElement(se);
      /* Assign memory with little endian */
      this->symEngine.addMemoryReference((address + writeSize) - 1, se->getID());
    }
    /* Otherwise keep the full formula */
    else {
      SymbolicElement *se = symEngine.newSymbolicElement(expr);
      inst.addElement(se);
      this->symEngine.addMemoryReference(address, se->getID());
      ret = se;
    }
    writeSize--;
  }

  return ret;
}


SymbolicElement *AnalysisProcessor::createMemSE(Inst &inst, std::stringstream &expr, uint64_t address, uint64_t writeSize, std::string comment)
{
  SymbolicElement   *ret = nullptr;
  std::stringstream tmp;

  /*
   * As the x86's memory can be accessed without alignment, each byte of the
   * memory must be assigned to an unique reference.
   */
  while (writeSize){
    /* Extract each byte if the size > 1 byte (8 bits) */
    if (writeSize > BYTE_SIZE){
      tmp.str(smt2lib::extract(((writeSize * REG_SIZE) - 1), ((writeSize * REG_SIZE) - REG_SIZE), expr.str()));
      SymbolicElement *se = symEngine.newSymbolicElement(tmp, "byte reference");
      inst.addElement(se);
      /* Assign memory with little endian */
      this->symEngine.addMemoryReference((address + writeSize) - 1, se->getID());
    }
    /* Otherwise keep the full formula */
    else {
      SymbolicElement *se = symEngine.newSymbolicElement(expr, comment);
      inst.addElement(se);
      this->symEngine.addMemoryReference(address, se->getID());
      ret = se;
    }
    writeSize--;
  }

  return ret;
}


SymbolicElement *AnalysisProcessor::createSE(Inst &inst, std::stringstream &expr)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  inst.addElement(se);
  return se;
}


SymbolicElement *AnalysisProcessor::createSE(Inst &inst, std::stringstream &expr, std::string comment)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr, comment);
  inst.addElement(se);
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


SymbolicVariable *AnalysisProcessor::getSymVar(uint64_t symVarId)
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


SymbolicElement *AnalysisProcessor::getElementFromId(uint64_t id)
{
  return this->symEngine.getElementFromId(id);
}


std::string AnalysisProcessor::getBacktrackedExpressionFromId(uint64_t id)
{
  return this->symEngine.getBacktrackedExpressionFromId(id);
}


uint64_t AnalysisProcessor::convertExprToSymVar(uint64_t exprId, uint64_t symVarSize)
{
  return this->symEngine.convertExprToSymVar(exprId, symVarSize);
}


uint64_t AnalysisProcessor::convertMemToSymVar(uint64_t memAddr, uint64_t symVarSize)
{
  return this->symEngine.convertMemToSymVar(memAddr, symVarSize);
}


uint64_t AnalysisProcessor::convertRegToSymVar(uint64_t regId, uint64_t symVarSize)
{
  return this->symEngine.convertRegToSymVar(regId, symVarSize);
}


void AnalysisProcessor::addPathConstraint(uint64_t exprId)
{
  this->symEngine.addPathConstraint(exprId);
}


std::list<uint64_t> AnalysisProcessor::getPathConstraints(void)
{
  return this->symEngine.getPathConstraints();
}


std::string AnalysisProcessor::buildSymbolicRegOperand(uint64_t regID, uint64_t regSize)
{
  std::stringstream   op;
  uint64_t            symReg = this->getRegSymbolicID(regID);

  if (symReg != UNSET)
    op << smt2lib::extract(regSize, "#" + std::to_string(symReg));
  else {
    if (regID >= ID_XMM0 && regID <= ID_XMM15)
      op << smt2lib::extract(regSize, smt2lib::bv(this->getSSERegisterValue(regID), SSE_REG_SIZE_BIT));
    else
      op << smt2lib::extract(regSize, smt2lib::bv(this->getRegisterValue(regID), REG_SIZE_BIT));
  }

  return op.str();
}


std::string AnalysisProcessor::buildSymbolicRegOperand(uint64_t regID, uint64_t regSize, uint64_t highExtract, uint64_t lowExtract)
{
  std::stringstream   op;
  uint64_t            symReg = this->getRegSymbolicID(regID);

  if (symReg != UNSET)
    op << smt2lib::extract(highExtract, lowExtract, "#" + std::to_string(symReg));
  else {
    if (regID >= ID_XMM0 && regID <= ID_XMM15)
      op << smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getSSERegisterValue(regID), SSE_REG_SIZE_BIT));
    else
      op << smt2lib::extract(highExtract, lowExtract, smt2lib::bv(this->getRegisterValue(regID), REG_SIZE_BIT));
  }

  return op.str();
}


std::string AnalysisProcessor::buildSymbolicMemOperand(uint64_t mem, uint64_t memSize)
{
  std::vector<std::string>  opVec;
  std::stringstream         tmp;
  uint64_t                  symMem, offset;

  offset = 0;
  while (memSize) {
    symMem = this->getMemSymbolicID(mem + memSize - 1);
    tmp.str("");
    if (symMem != UNSET)
      tmp << "#" << std::dec << symMem;
    else
      tmp << smt2lib::bv(this->getMemValue(mem + offset, 1), REG_SIZE);
    opVec.push_back(smt2lib::extract(7, 0, tmp.str()));
    offset++;
    memSize--;
  }

  tmp.str("");
  switch (opVec.size()) {
    case DQWORD_SIZE:
    case QWORD_SIZE:
    case DWORD_SIZE:
    case WORD_SIZE:
      tmp.str(smt2lib::concat(opVec));
      break;
    case BYTE_SIZE:
      tmp.str(opVec[0]);
      break;
  }

  return tmp.str();
}


std::string AnalysisProcessor::buildSymbolicFlagOperand(uint64_t flagID, uint64_t size)
{
  std::stringstream   op;
  uint64_t            symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op << smt2lib::zx("#" + std::to_string(symFlag), (size * REG_SIZE) - 1);
  else
    op << smt2lib::bv(this->getFlagValue(flagID), size * REG_SIZE);

  return op.str();
}


std::string AnalysisProcessor::buildSymbolicFlagOperand(uint64_t flagID)
{
  std::stringstream   op;
  uint64_t            symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op << "#" + std::to_string(symFlag);
  else
    op << smt2lib::bv(this->getFlagValue(flagID), 1);

  return op.str();
}



void AnalysisProcessor::concretizeReg(uint64_t regID)
{
  this->symEngine.concretizeReg(regID);
}


void AnalysisProcessor::concretizeMem(uint64_t mem)
{
  this->symEngine.concretizeMem(mem);
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
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicElement *se, uint64_t memDst, uint64_t memSrc, uint32_t readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memDst, memSrc, readSize);
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


void AnalysisProcessor::setTaintMem(SymbolicElement *se, uint64_t mem, uint64_t flag)
{
  this->taintEngine.setTaintMem(mem, flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicElement *se, uint64_t reg, uint64_t flag)
{
  this->taintEngine.setTaintReg(reg, flag);
  se->isTainted = flag;
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


__uint128_t AnalysisProcessor::getMemValue(uint64_t mem, uint32_t readSize)
{
  return this->currentCtxH->getMemValue(mem, readSize);
}


void AnalysisProcessor::setMemValue(uint64_t mem, uint32_t writeSize, __uint128_t value)
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


