#ifndef ONEOPERANDTEMPLATE_H
#define ONEOPERANDTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"
#include "TritonOperand.h"


class OneOperandTemplate: public OperandTemplate {
  public:
    virtual ~OneOperandTemplate() { }

    virtual void templateMethod(
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void none(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void reg(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void imm(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void mem(AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // ONEOPERANDTEMPLATE_H
