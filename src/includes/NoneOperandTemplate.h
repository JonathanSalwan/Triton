#ifndef _NONEOPERANDTEMPLATE_H_
#define _NONEOPERANDTEMPLATE_H_

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"


class NoneOperandTemplate {
  public:
    virtual ~NoneOperandTemplate() { }

    virtual void templateMethod(
        const ContextHandler &ctxH,
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector< std::tuple<IRBuilder::operand_t, uint64_t, uint32_t> > &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void none(const ContextHandler &ctxH, AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // _NONEOPERANDTEMPLATE_H_
