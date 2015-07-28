/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/


#ifndef   CONTROLFLOW_H
#define   CONTROLFLOW_H

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "SymbolicExpression.h"

namespace ControlFlow {
  SymbolicExpression *rip(Inst &inst, AnalysisProcessor &ap, uint64 nextAddr);
};

#endif     /* !__CONTROLFLOW_H__ */
