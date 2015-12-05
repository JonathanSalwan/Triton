/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#include <tuple>
#include <stdexcept>

#include <AnalysisProcessor.h>
#include <Inst.h>
#include <TwoOperandsTemplate.h>


void TwoOperandsTemplate::templateMethod(
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  if (operands.size() < 2)
    throw std::runtime_error("Wrong numbers of operands: "
                           + insName
                           + " instruction must have two operands.");

  #ifndef LIGHT_VERSION
  /* Don't perform the symbolic execution if the engine is disabled. */
  if (!ap.isSymEngineEnabled())
    return;
  #endif

  /* Register, Immediate operand */
  if (operands[0].getType() == IRBuilderOperand::REG &&
      operands[1].getType() == IRBuilderOperand::IMM)
    this->regImm(inst);

  /* Register, Register operand */
  if (operands[0].getType() == IRBuilderOperand::REG &&
      operands[1].getType() == IRBuilderOperand::REG)
    this->regReg(inst);

  /* Register, Memory operand */
  if (operands[0].getType() == IRBuilderOperand::REG &&
      (IRBuilder::isMemOperand(operands[1].getType()) || operands[1].getType() == IRBuilderOperand::LEA))
    this->regMem(inst);

  /* Memory, Immediate operand */
  if (IRBuilder::isMemOperand(operands[0].getType()) &&
      operands[1].getType() == IRBuilderOperand::IMM)
    this->memImm(inst);

  /* Memory, Register operand */
  if (IRBuilder::isMemOperand(operands[0].getType()) &&
      operands[1].getType() == IRBuilderOperand::REG)
    this->memReg(inst);
}

