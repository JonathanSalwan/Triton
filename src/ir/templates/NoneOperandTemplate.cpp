#include <tuple>
#include <stdexcept>

#include <AnalysisProcessor.h>
#include <Inst.h>
#include <NoneOperandTemplate.h>


void NoneOperandTemplate::templateMethod(
    AnalysisProcessor &ap,
    Inst &inst,
    const std::vector<TritonOperand> &operands,
    std::string insName) const
{
  // none but we must apply the semantic
  this->none(ap, inst);
}

