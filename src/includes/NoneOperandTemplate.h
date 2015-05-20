#ifndef _NONEOPERANDTEMPLATE_H_
#define _NONEOPERANDTEMPLATE_H_

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"


class NoneOperandTemplate: public OperandTemplate {
  public:
    virtual ~NoneOperandTemplate() { }

    virtual void templateMethod(
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector< std::tuple<IRBuilderOperand::operand_t, uint64_t, uint32_t, uint64_t, uint64_t, uint64_t, uint64_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void none(AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // _NONEOPERANDTEMPLATE_H_
