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
  // none but we must apply the semantic
  this->none(inst);
}

