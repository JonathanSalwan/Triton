/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef NONEOPERANDTEMPLATE_H
#define NONEOPERANDTEMPLATE_H

#include <vector>

#include "AnalysisProcessor.h"
#include "ContextHandler.h"
#include "Inst.h"
#include "IRBuilder.h"
#include "OperandTemplate.h"
#include "TritonOperand.h"

extern AnalysisProcessor ap;


class NoneOperandTemplate: public OperandTemplate {
  public:
    virtual ~NoneOperandTemplate() { }

    virtual void templateMethod(
        Inst &inst,
        const std::vector<TritonOperand> &operands,
        std::string instructionName) const;

  protected:
    // Primitives uses in the templateMethod, must be implemented by subclasses.
    virtual void none(Inst &inst) const = 0;
};

#endif // NONEOPERANDTEMPLATE_H
