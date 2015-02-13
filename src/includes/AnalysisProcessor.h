#ifndef _ANALYSISPROCESSOR_H_
#define _ANALYSISPROCESSOR_H_

#include "SymbolicEngine.h"


class AnalysisProcessor {
  public:
    AnalysisProcessor();

    // Symbolic Engine Facade

    // Return a symbolic element for the register (regID).
    SymbolicElement *createRegSE(std::stringstream &expr, uint64_t regID);

    // Return a symbolic element for the memory address.
    SymbolicElement *createMemSE(std::stringstream &expr, uint64_t address);

    // Return the ID of the symbolic element currently present in the
    // symbolic register. If there is no symbolic element, it returns UNSET.
    uint64_t getRegSymbolicID(uint64_t regID);

    // Return the ID of the symbolic element currently present in the
    // symbolic memory. If there is no symbolic element, it returns UNSET.
    uint64_t getMemorySymbolicID(uint64_t address);

    SymbolicEngine &getSymbolicEngine();

  private:
    SymbolicEngine symEngine;
};

#endif //_ANALYSISPROCESSOR_H_
