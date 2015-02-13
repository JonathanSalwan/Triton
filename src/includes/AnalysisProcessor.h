#ifndef _ANALYSISPROCESSOR_H_
#define _ANALYSISPROCESSOR_H_

#include "SymbolicEngine.h"


class AnalysisProcessor {
  public:
    AnalysisProcessor();

    SymbolicEngine &getSymbolicEngine();

  private:
    SymbolicEngine symEngine;
};

#endif //_ANALYSISPROCESSOR_H_
