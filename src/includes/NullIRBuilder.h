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

    std::stringstream *process(const ContextHandler &ctxH) const {
      return nullptr;
    }
};

#endif // _NULLIRBUILDER_H_
