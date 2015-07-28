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
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  if (operands.size() < 2)
    throw std::runtime_error("Wrong numbers of operands: "
                           + insName
                           + " instruction must have two operands.");

  // reg, imm
  if (operands[0].getType() == IRBuilderOperand::REG &&
      operands[1].getType() == IRBuilderOperand::IMM)
    this->regImm(ap, inst);

  // reg, reg
  if (operands[0].getType() == IRBuilderOperand::REG &&
      operands[1].getType() == IRBuilderOperand::REG)
    this->regReg(ap, inst);

  // reg, mem
  if (operands[0].getType() == IRBuilderOperand::REG &&
      (IRBuilder::isMemOperand(operands[1].getType()) || operands[1].getType() == IRBuilderOperand::LEA))
    this->regMem(ap, inst);

  // mem, imm
  if (IRBuilder::isMemOperand(operands[0].getType()) &&
      operands[1].getType() == IRBuilderOperand::IMM)
    this->memImm(ap, inst);

  // mem, reg
  if (IRBuilder::isMemOperand(operands[0].getType()) &&
      operands[1].getType() == IRBuilderOperand::REG)
    this->memReg(ap, inst);
}

