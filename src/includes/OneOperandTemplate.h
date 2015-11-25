/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef ONEOPERANDTEMPLATE_H
#define ONEOPERANDTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"

extern AnalysisProcessor ap;


class OneOperandTemplate: public OperandTemplate {
  public:
    virtual ~OneOperandTemplate() { }

    virtual void templateMethod(
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.
    virtual void none(Inst &inst) const = 0;
    virtual void reg(Inst &inst) const = 0;
    virtual void imm(Inst &inst) const = 0;
    virtual void mem(Inst &inst) const = 0;
};

#endif // ONEOPERANDTEMPLATE_H
