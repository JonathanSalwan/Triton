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
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  // If there is no operand
  // Sometime instructions can have 0 or 1 operand. Like RET and RET imm16
  if (operands.size() == 0)
    this->none(ap, inst);

  // reg
  if (operands[0].getType() == IRBuilderOperand::REG)
    this->reg(ap, inst);

  // imm
  if (operands[0].getType() == IRBuilderOperand::IMM)
    this->imm(ap, inst);

  // mem
  if (IRBuilder::isMemOperand(operands[0].getType()))
    this->mem(ap, inst);
}

