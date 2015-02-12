#include <stdexcept>

#include "TwoOperandsTemplate.h"


std::stringstream *TwoOperandsTemplate::templateMethod(
    const ContextHandler &ctxH,
    const std::vector< std::pair<IRBuilder::operand_t, uint64_t> > &operands,
    std::string insName) const
{
  if (operands.size() != 2)
    throw std::runtime_error("Wrong numbers of operands: "
                            + insName
                            + "instruction must have two operands.");

  std::stringstream *expr = nullptr;

  // reg, imm
  if (operands[0].first == IRBuilder::REG
      && operands[1].first == IRBuilder::IMM)
    expr = this->regImm(ctxH);

  // reg, reg
  if (operands[0].first == IRBuilder::REG
      && operands[1].first == IRBuilder::REG)
    expr = this->regReg(ctxH);

  // reg, mem
  if (operands[0].first == IRBuilder::REG
      && IRBuilder::isMemOperand(operands[1].first))
    expr = this->regMem(ctxH);

  // mem, imm
  if (IRBuilder::isMemOperand(operands[0].first)
      && operands[1].first == IRBuilder::IMM)
    expr = this->memImm(ctxH);

  // mem, reg
  if (IRBuilder::isMemOperand(operands[0].first)
      && operands[1].first == IRBuilder::REG)
    expr = this->memReg(ctxH);

  return expr;
}
