#include "AnalysisProcessor.h"

AnalysisProcessor::AnalysisProcessor(): symEngine() {
}


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
