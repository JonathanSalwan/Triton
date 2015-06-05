#ifndef TWOOPERANDSTEMPLATE_H
#define TWOOPERANDSTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"


class TwoOperandsTemplate: public OperandTemplate {
  public:
    virtual ~TwoOperandsTemplate() { }

    virtual void templateMethod(
        AnalysisProcessor &ap,
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.

    virtual void regImm(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void regReg(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void regMem(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void memImm(AnalysisProcessor &ap, Inst &inst) const = 0;

    virtual void memReg(AnalysisProcessor &ap, Inst &inst) const = 0;
};

#endif // TWOOPERANDSTEMPLATE_H
