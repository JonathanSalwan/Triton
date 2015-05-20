#include <tuple>
#include <stdexcept>

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


void NoneOperandTemplate::templateMethod(
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> > &operands,
    std::string insName) const
{
  // none but we must apply the semantic
  this->none(ap, inst);
}

