
#ifndef   CONTROLFLOW_H
#define   CONTROLFLOW_H

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "SymbolicElement.h"

namespace ControlFlow {
  SymbolicElement *rip(Inst &inst, AnalysisProcessor &ap, uint64 nextAddr);
};

#endif     /* !__CONTROLFLOW_H__ */
