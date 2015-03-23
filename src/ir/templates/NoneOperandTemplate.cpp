#include <tuple>
#include <stdexcept>

#include "AnalysisProcessor.h"
#include "Inst.h"
#include "NoneOperandTemplate.h"


void NoneOperandTemplate::templateMethod(
    const ContextHandler &ctxH,
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
    std::string insName) const
{
  // none but we must apply the semantic
  this->none(ctxH, ap, inst);
}

