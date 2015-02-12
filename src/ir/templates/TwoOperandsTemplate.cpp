#include <tuple>
#include <stdexcept>

#include "TwoOperandsTemplate.h"


std::stringstream *TwoOperandsTemplate::templateMethod(
    const ContextHandler &ctxH,
    const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
    std::string insName) const
{
  if (operands.size() != 2)
    throw std::runtime_error("Wrong numbers of operands: "
                            + insName
                            + "instruction must have two operands.");

  std::stringstream *expr = nullptr;

  // reg, imm
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      std::get<0>(operands[1]) == IRBuilder::IMM)
    expr = this->regImm(ctxH);

  // reg, reg
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      std::get<0>(operands[1]) == IRBuilder::REG)
    expr = this->regReg(ctxH);

  // reg, mem
  if (std::get<0>(operands[0]) == IRBuilder::REG &&
      IRBuilder::isMemOperand(std::get<0>(operands[1])))
    expr = this->regMem(ctxH);

  // mem, imm
  if (IRBuilder::isMemOperand(std::get<0>(operands[0])) &&
      std::get<0>(operands[1]) == IRBuilder::IMM)
    expr = this->memImm(ctxH);

  // mem, reg
  if (IRBuilder::isMemOperand(std::get<0>(operands[0])) &&
      std::get<0>(operands[1]) == IRBuilder::REG)
    expr = this->memReg(ctxH);

  return expr;
}

