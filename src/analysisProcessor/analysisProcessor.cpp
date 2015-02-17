#include "AnalysisProcessor.h"


AnalysisProcessor::AnalysisProcessor(): symEngine(), taintEngine() {
}

// Symbolic Engine Facade
// ----------------------

SymbolicEngine &AnalysisProcessor::getSymbolicEngine() {
  return this->symEngine;
}


SymbolicElement *AnalysisProcessor::createRegSE(std::stringstream &expr, uint64_t regID) {
  SymbolicElement *se = this->symEngine.newSymbolicElement(expr);
  this->symEngine.symbolicReg[regID] = se->getID();

  return se;
}


SymbolicElement *AnalysisProcessor::createMemSE(std::stringstream &expr, uint64_t address) {
  SymbolicElement *se = symEngine.newSymbolicElement(expr);
  symEngine.addMemoryReference(address, se->getID());

  return se;
}


uint64_t AnalysisProcessor::getRegSymbolicID(uint64_t regID) {
  return this->symEngine.symbolicReg[regID];
}


uint64_t AnalysisProcessor::getMemorySymbolicID(uint64_t address) {
  return this->symEngine.isMemoryReference(address);
}


// Taint Engine Facade
// -------------------

TaintEngine &AnalysisProcessor::getTaintEngine() {
  return this->taintEngine;
}


void AnalysisProcessor::spreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc)
{
  se->isTainted = this->taintEngine.spreadTaintRegReg(regDst, regSrc);
}


void AnalysisProcessor::spreadTaintRegImm(SymbolicElement *se, uint64_t regDst)
{
  se->isTainted = this->taintEngine.spreadTaintRegImm(regDst);
}


void AnalysisProcessor::spreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc, uint32_t readSize)
{
  se->isTainted = this->taintEngine.spreadTaintRegMem(regDst, memSrc, readSize);

  /* Use symbolic variable if the memory is tainted */
  if (se->isTainted) {

    std::stringstream newExpr;
    uint64_t          symVarID;

    /* Check if this memory area is already known as a symbolic variable */
    symVarID = this->symEngine.isSymVarMemory(memSrc); // TODO: Must use the readSize
    if (symVarID == UNSET){
      symVarID = this->symEngine.getUniqueSymVarID();
      this->symEngine.addSmt2LibVarDecl(symVarID, readSize);
      this->symEngine.addSymVarMemoryReference(memSrc, symVarID);
    }

    newExpr << "SymVar_" << std::dec << symVarID;
    se->setSrcExpr(newExpr);
  }
}


void AnalysisProcessor::spreadTaintMemImm(SymbolicElement *se, uint64_t memDst, uint64_t writeSize)
{
  se->isTainted = this->taintEngine.spreadTaintMemImm(memDst, writeSize);
}


void AnalysisProcessor::spreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc, uint64_t writeSize)
{
  se->isTainted = this->taintEngine.spreadTaintMemReg(memDst, regSrc, writeSize);
}


bool AnalysisProcessor::isRegTainted(uint64_t reg)
{
  return this->taintEngine.isRegTainted(reg);
}


bool AnalysisProcessor::isMemoryTainted(uint64_t addr)
{
  return this->taintEngine.isMemoryTainted(addr);
}


void AnalysisProcessor::aluSpreadTaintRegImm(SymbolicElement *se, uint64_t regDst)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegImm(regDst);
}


void AnalysisProcessor::aluSpreadTaintRegReg(SymbolicElement *se, uint64_t regDst, uint64_t regSrc)
{
  se->isTainted = this->taintEngine.aluSpreadTaintRegReg(regDst, regSrc);
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

