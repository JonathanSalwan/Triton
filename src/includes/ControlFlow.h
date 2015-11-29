/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef LIGHT_VERSION

#ifndef   CONTROLFLOW_H
#define   CONTROLFLOW_H

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "SymbolicExpression.h"

extern AnalysisProcessor ap;


namespace ControlFlow {
 void rip(Inst &inst, __uint nextAddr);
};

#endif /* !__CONTROLFLOW_H__ */
#endif /* LIGHT_VERSION */

