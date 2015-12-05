/*
**  Copyright (C) - Triton
**
**  This program is under the terms of the LGPLv3 License.
*/

#ifndef NULLIRBUILDER_H
#define NULLIRBUILDER_H

#include "TritonTypes.h"

#include <string>

#include "AnalysisProcessor.h"
#include "BaseIRBuilder.h"
#include "TritonOperand.h"

extern AnalysisProcessor ap;


// Null object, it's purpose is to handle "nicely" not implemented instructions.
class NullIRBuilder: public BaseIRBuilder {
  public:
    NullIRBuilder(__uint address, const std::string &disas) :
      BaseIRBuilder(address, disas) {
    }

    void addOperand(const TritonOperand &operand) {
    }

    using BaseIRBuilder::getOperands;
    const std::vector<TritonOperand> &getOperands(void) {
      return this->operands;
    }

    Inst *process(void) const {
      #ifndef LIGHT_VERSION
      ap.incNumberOfUnknownInstruction(); /* Used for statistics */
      #endif
      return new Inst(ap.getCurrentCtxH()->getThreadID(), this->address, this->disas);
    }
};

#endif // NULLIRBUILDER_H

