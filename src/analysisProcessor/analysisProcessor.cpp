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
  if (this->taintEngine.spreadTaintRegReg(regDst, regSrc))
    se->isTainted = true;
}


void AnalysisProcessor::spreadTaintRegImm(SymbolicElement *se, uint64_t regDst)
{
  if (this->taintEngine.spreadTaintRegImm(regDst))
    se->isTainted = true;
}


void AnalysisProcessor::spreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc)
{
  if (this->taintEngine.spreadTaintRegMem(regDst, memSrc))
    se->isTainted = true;
}


void AnalysisProcessor::spreadTaintMemImm(SymbolicElement *se, uint64_t memDst)
{
  if (this->taintEngine.spreadTaintMemImm(memDst))
    se->isTainted = true;
}


void AnalysisProcessor::spreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc)
{
  if (this->taintEngine.spreadTaintMemReg(memDst, regSrc))
    se->isTainted = true;
}


