#ifndef NONEOPERANDTEMPLATE_H
#define NONEOPERANDTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"


class NoneOperandTemplate: public OperandTemplate {
  public:
    virtual ~NoneOperandTemplate() { }

    virtual void templateMethod(
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void none(AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // NONEOPERANDTEMPLATE_H
