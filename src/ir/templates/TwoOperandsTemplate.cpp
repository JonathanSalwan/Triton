#include <tuple>
#include <stdexcept>

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "TwoOperandsTemplate.h"

#include <iostream>
void TwoOperandsTemplate::templateMethod(
    const ContextHandler &ctxH,
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
    std::string insName) const
{
  if (operands.size() < 2) // TODO, MOV = 2, ADD = 3, virer le < et mettre un template 3op
    throw std::runtime_error("Wrong numbers of operands: "
                           + insName
                           + " instruction must have two operands.");

  // reg, imm
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      std::get<0>(operands[1]) == IRBuilder::IMM)
    this->regImm(ctxH, ap, inst);

  // reg, reg
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      std::get<0>(operands[1]) == IRBuilder::REG)
    this->regReg(ctxH, ap, inst);

  // reg, mem
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      IRBuilder::isMemOperand(std::get<0>(operands[1])))
    this->regMem(ctxH, ap, inst);

  // mem, imm
  if (IRBuilder::isMemOperand(std::get<0>(operands[0])) &&
      std::get<0>(operands[1]) == IRBuilder::IMM)
    this->memImm(ctxH, ap, inst);

  // mem, reg
  if (IRBuilder::isMemOperand(std::get<0>(operands[0])) &&
      std::get<0>(operands[1]) == IRBuilder::REG)
    this->memReg(ctxH, ap, inst);
}

