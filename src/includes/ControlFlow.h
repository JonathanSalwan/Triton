
#ifndef   __CONTROLFLOW_H__
#define   __CONTROLFLOW_H__

#include "AnalysisProcessor.h"
#include "SymbolicElement.h"

namespace ControlFlow {
  SymbolicElement *rip(AnalysisProcessor &ap, uint64_t nextAddr);
};

#endif     /* !__CONTROLFLOW_H__ */
