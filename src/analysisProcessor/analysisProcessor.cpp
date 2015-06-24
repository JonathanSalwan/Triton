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


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64 regID)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);
  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, std::string comment)
{
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr, comment);
  this->symEngine.symbolicReg[regID] = se->getID();
  inst.addElement(se);
  return se;
}


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, uint64 regSize)
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


SymbolicElement *AnalysisProcessor::createRegSE(Inst &inst, std::stringstream &expr, uint64 regID, uint64 regSize, std::string comment)
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


SymbolicElement *AnalysisProcessor::createMemSE(Inst &inst, std::stringstream &expr, uint64 address, uint64 writeSize)
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


SymbolicElement *AnalysisProcessor::createMemSE(Inst &inst, std::stringstream &expr, uint64 address, uint64 writeSize, std::string comment)
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


SymbolicElement *AnalysisProcessor::getElementFromId(uint64 id)
{
  return this->symEngine.getElementFromId(id);
}


std::string AnalysisProcessor::getBacktrackedExpressionFromId(uint64 id)
{
  return this->symEngine.getBacktrackedExpressionFromId(id);
}


uint64 AnalysisProcessor::convertExprToSymVar(uint64 exprId, uint64 symVarSize, std::string symVarComment)
{
  return this->symEngine.convertExprToSymVar(exprId, symVarSize, symVarComment);
}


uint64 AnalysisProcessor::convertMemToSymVar(uint64 memAddr, uint64 symVarSize, std::string symVarComment)
{
  return this->symEngine.convertMemToSymVar(memAddr, symVarSize, symVarComment);
}


uint64 AnalysisProcessor::convertRegToSymVar(uint64 regId, uint64 symVarSize, std::string symVarComment)
{
  return this->symEngine.convertRegToSymVar(regId, symVarSize, symVarComment);
}


void AnalysisProcessor::addPathConstraint(uint64 exprId)
{
  this->symEngine.addPathConstraint(exprId);
}


std::list<uint64> AnalysisProcessor::getPathConstraints(void)
{
  return this->symEngine.getPathConstraints();
}


std::string AnalysisProcessor::buildSymbolicRegOperand(uint64 regID, uint64 regSize)
{
  std::stringstream   op;
  uint64              symReg = this->getRegSymbolicID(regID);

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


std::string AnalysisProcessor::buildSymbolicRegOperand(uint64 regID, uint64 regSize, uint64 highExtract, uint64 lowExtract)
{
  std::stringstream   op;
  uint64              symReg = this->getRegSymbolicID(regID);

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


std::string AnalysisProcessor::buildSymbolicMemOperand(uint64 mem, uint64 memSize)
{
  std::vector<std::string>  opVec;
  std::stringstream         tmp;
  uint64                    symMem, offset;

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


std::string AnalysisProcessor::buildSymbolicFlagOperand(uint64 flagID, uint64 size)
{
  std::stringstream   op;
  uint64              symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op << smt2lib::zx("#" + std::to_string(symFlag), (size * REG_SIZE) - 1);
  else
    op << smt2lib::bv(this->getFlagValue(flagID), size * REG_SIZE);

  return op.str();
}


std::string AnalysisProcessor::buildSymbolicFlagOperand(uint64 flagID)
{
  std::stringstream   op;
  uint64              symFlag = this->getRegSymbolicID(flagID);

  if (symFlag != UNSET)
    op << "#" + std::to_string(symFlag);
  else
    op << smt2lib::bv(this->getFlagValue(flagID), 1);

  return op.str();
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


void AnalysisProcessor::assignmentSpreadTaintExprMem(SymbolicElement *se, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprMem(memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprReg(SymbolicElement *se, uint64 regSrc)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprReg(regSrc);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegMem(SymbolicElement *se, uint64 regSrc, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegMem(regSrc, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintExprRegReg(SymbolicElement *se, uint64 regSrc1, uint64 regSrc2)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintExprRegReg(regSrc1, regSrc2);
}


void AnalysisProcessor::assignmentSpreadTaintRegReg(SymbolicElement *se, uint64 regDst, uint64 regSrc)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::assignmentSpreadTaintRegImm(SymbolicElement *se, uint64 regDst)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::assignmentSpreadTaintRegMem(SymbolicElement *se, uint64 regDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintRegMem(regDst, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemMem(SymbolicElement *se, uint64 memDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemMem(memDst, memSrc, readSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemImm(SymbolicElement *se, uint64 memDst, uint64 writeSize)
{
  se->isTainted = this->taintEngine.assignmentSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::assignmentSpreadTaintMemReg(SymbolicElement *se, uint64 memDst, uint64 regSrc, uint64 writeSize)
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


void AnalysisProcessor::setTaintMem(SymbolicElement *se, uint64 mem, uint64 flag)
{
  this->taintEngine.setTaintMem(mem, flag);
  se->isTainted = flag;
}


void AnalysisProcessor::setTaintReg(SymbolicElement *se, uint64 reg, uint64 flag)
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


void AnalysisProcessor::aluSpreadTaintRegImm(SymbolicElement *se, uint64 regDst)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicElement *se, uint64 regDst, uint64 regSrc)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::aluSpreadTaintMemMem(SymbolicElement *se, uint64 memDst, uint64 memSrc, uint32 writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemMem(memDst, memSrc, writeSize);
}


void AnalysisProcessor::aluSpreadTaintRegMem(SymbolicElement *se, uint64 regDst, uint64 memSrc, uint32 readSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegMem(regDst, memSrc, readSize);
}


void AnalysisProcessor::aluSpreadTaintMemImm(SymbolicElement *se, uint64 memDst, uint32 writeSize)
{
  se->isTainted = this->taintEngine.aluSpreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::aluSpreadTaintMemReg(SymbolicElement *se, uint64 memDst, uint64 regSrc, uint32 writeSize)
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


bool AnalysisProcessor::isSnapshotEnable(void)
{
  if (this->snapshotEngine.isLocked())
    return false;
  return true;
}


