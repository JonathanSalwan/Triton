/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <tuple>
#include <stdexcept>

#include <AnalysisProcessor.h>
#include <Inst.h>
#include <NoneOperandTemplate.h>


void NoneOperandTemplate::templateMethod(
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  #ifndef LIGHT_VERSION
  /* Don't perform the symbolic execution if the engine is disabled. */
  if (!ap.isSymEngineEnabled())
    return;
  #endif

  /* none but we must apply the semantic */
  this->none(inst);
}

