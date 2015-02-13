#include "AnalysisProcessor.h"

AnalysisProcessor::AnalysisProcessor(): symEngine() {
}


SymbolicEngine &AnalysisProcessor::getSymbolicEngine() {
  return this->symEngine;
}
