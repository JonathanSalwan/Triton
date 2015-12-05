/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <tuple>
#include <stdexcept>

#include <AnalysisProcessor.h>
#include <Inst.h>
#include <OneOperandTemplate.h>


void OneOperandTemplate::templateMethod(
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  #ifndef LIGHT_VERSION
  /* Don't perform the symbolic execution if the engine is disabled. */
  if (!ap.isSymEngineEnabled())
    return;
  #endif

  /*
   *  If there is no operand. Sometime instructions can have 0 or 1
   *  operand. Like RET and RET imm16.
   */
  if (operands.size() == 0)
    this->none(inst);

  /* Register operand */
  if (operands[0].getType() == IRBuilderOperand::REG)
    this->reg(inst);

  /* Immediate operand */
  if (operands[0].getType() == IRBuilderOperand::IMM)
    this->imm(inst);

  /* Memory operand */
  if (IRBuilder::isMemOperand(operands[0].getType()))
    this->mem(inst);
}

