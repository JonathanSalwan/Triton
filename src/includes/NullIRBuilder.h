#ifndef _NULLIRBUILDER_H_
#define _NULLIRBUILDER_H_

#include <cstdint>

#include <string>

#include "BaseIRBuilder.h"


// Null object, it's purpose is to handle "nicely" not implemented instructions.
class NullIRBuilder: public BaseIRBuilder {
  public:
    NullIRBuilder(uint64_t address, const std::string &disas):
      BaseIRBuilder(address, disas) { }

    void addOperand(IRBuilder::operand_t type, uint64_t value = 0) { }

    Inst *process(const ContextHandler &ctxH, AnalysisProcessor &ap) const {
      return new Inst(ctxH.getThreadId(), this->address, this->disas);
    }
};

#endif // _NULLIRBUILDER_H_
