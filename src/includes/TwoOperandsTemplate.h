/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef TWOOPERANDSTEMPLATE_H
#define TWOOPERANDSTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"

extern AnalysisProcessor ap;


class TwoOperandsTemplate: public OperandTemplate {
  public:
    virtual ~TwoOperandsTemplate() { }

    virtual void templateMethod(
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.
    virtual void regImm(Inst &inst) const = 0;
    virtual void regReg(Inst &inst) const = 0;
    virtual void regMem(Inst &inst) const = 0;
    virtual void memImm(Inst &inst) const = 0;
    virtual void memReg(Inst &inst) const = 0;
};

#endif // TWOOPERANDSTEMPLATE_H
