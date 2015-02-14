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


void AnalysisProcessor::spreadTaintRegMem(SymbolicElement *se, uint64_t regDst, uint64_t memSrc)
{
  se->isTainted = this->taintEngine.spreadTaintRegMem(regDst, memSrc);
}


void AnalysisProcessor::spreadTaintMemImm(SymbolicElement *se, uint64_t memDst)
{
  se->isTainted = this->taintEngine.spreadTaintMemImm(memDst);
}


void AnalysisProcessor::spreadTaintMemReg(SymbolicElement *se, uint64_t memDst, uint64_t regSrc)
{
  se->isTainted = this->taintEngine.spreadTaintMemReg(memDst, regSrc);
}


