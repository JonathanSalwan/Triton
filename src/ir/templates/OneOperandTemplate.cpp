#include <tuple>
#include <stdexcept>

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "OneOperandTemplate.h"


void OneOperandTemplate::templateMethod(
    const ContextHandler &ctxH,
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
    std::string insName) const
{
  // If there is no operand
  // Sometime instructions can have 0 or 1 operand. Like REP and REP imm16
  if (operands.size() == 0)
    this->none(ctxH, ap, inst);

  // reg
  if (std::get<0>(operands[0]) == IRBuilder::REG)
    this->reg(ctxH, ap, inst);

  // imm
  if (std::get<0>(operands[0]) == IRBuilder::IMM)
    this->imm(ctxH, ap, inst);

  // mem
  if (IRBuilder::isMemOperand(std::get<0>(operands[0])))
    this->mem(ctxH, ap, inst);
}

